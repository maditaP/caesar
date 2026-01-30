use std::collections::HashMap;

use num::{BigInt, BigRational};

use z3rro::{
    eureal::ConcreteEUReal,
    model::{InstrumentedModel, SmtEval},
    prover::{IncrementalMode, Prover},
};

use crate::{
    ast::{
        self, BinOpKind, DeclKind, Direction, DomainSpec, Expr, ExprBuilder, ExprData, ExprKind, Ident, Shared, Span, Spanned, Stmt, StmtKind, TyKind, UnOpKind, visit::{VisitorMut, walk_expr, walk_stmt}
    }, driver::{commands::verify::VerifyCommand, error::CaesarError, quant_proof::BoolVcProveTask, smt_proof::SmtVcProveTask}, resource_limits::LimitsRef, smt::{
        symbolic::Symbolic, translate_exprs::TranslateExprs, uninterpreted::FuncEntry
    }, tyctx::TyCtx,
    driver::{
        front::SourceUnit,
    },
};
// Takes a function and substitutes calls to that function with the functions body,
// substituting function parameters with the caller argumentspub struct FunctionInliner<'ctx, T: FuncLookup> {
pub struct FunctionInliner<'smt, 'ctx> {
    pub target: Ident,
    pub entry: &'ctx FuncEntry<'ctx>,
    pub body: &'ctx Expr,
    pub tcx: &'smt TyCtx,

    /// Track which functions are currently being inlined
    inlining_stack: Vec<Ident>, // to avoid infinitely inlining recursive functions
}

impl<'smt, 'ctx> FunctionInliner<'smt, 'ctx> {
    pub fn new(
        target: Ident,
        entry: &'ctx FuncEntry<'ctx>,
        body: &'ctx Expr,
        tcx: &'smt TyCtx,
    ) -> Self {
        Self {
            target,
            entry,
            body,
            tcx,
            inlining_stack: Vec::new(),
        }
    }
}

impl<'smt, 'ctx> VisitorMut for FunctionInliner<'smt, 'ctx> {
    type Err = ();

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        let span = expr.span;

        match &mut expr.kind {
            // Case 1: INLINE THE TARGET FUNCTION (existing)
            ExprKind::Call(func_ident, args) if *func_ident == self.target => {
                let parameters: Vec<Ident> =
                    self.entry.inputs.node.iter().map(|p| p.name).collect();

                let mut wrapped = self.body.clone();

                for (parameter, actual_expr) in parameters.iter().zip(args.iter()) {
                    wrapped = Shared::new(ExprData {
                        kind: ExprKind::Subst(*parameter, actual_expr.clone(), wrapped.clone()),
                        ty: wrapped.ty.clone(),
                        span,
                    });
                }

                *expr = wrapped.clone();
                return Ok(());
            }

            // Case 2: INLINE OTHER FUNCTIONS (with recursion guard)
            ExprKind::Call(func_ident, args) => {
                // RECURSION GUARD: do NOT inline if this function is already being processed
                if self.inlining_stack.contains(func_ident) {
                    // Still recurse through arguments, but do not inline the body
                    return walk_expr(self, expr);
                }

                // Lookup the function definition
                if let Some(DeclKind::FuncDecl(func_ref)) = self.tcx.get(*func_ident).as_deref() {
                    let func = func_ref.borrow();
                    let body_opt = func.body.borrow();
                    let parameters: Vec<Ident> = func.inputs.node.iter().map(|p| p.name).collect();

                    if let Some(body_expr) = body_opt.clone() {
                        // Mark this function as "inlining in progress"
                        self.inlining_stack.push(*func_ident);

                        let mut wrapped = body_expr;

                        // Substitute parameters
                        for (parameter, actual_expr) in parameters.iter().zip(args.iter()) {
                            wrapped = Shared::new(ExprData {
                                kind: ExprKind::Subst(
                                    *parameter,
                                    actual_expr.clone(),
                                    wrapped.clone(),
                                ),
                                ty: wrapped.ty.clone(),
                                span,
                            });
                        }

                        // Recursively inline inside the substituted body
                        let mut wrapped_mut = wrapped.clone();
                        self.visit_expr(&mut wrapped_mut)?;

                        // Done processing this function
                        self.inlining_stack.pop();

                        *expr = wrapped_mut;
                        return Ok(());
                    }

                    return walk_expr(self, expr);
                }

                walk_expr(self, expr)
            }

            _ => walk_expr(self, expr),
        }
    }
}

// Translates a model into a map Ident -> Expression
pub fn create_subst_mapping<'ctx>(
    model: &InstrumentedModel<'ctx>,
    translate: &mut crate::smt::translate_exprs::TranslateExprs<'_, 'ctx>,
) -> HashMap<ast::symbol::Ident, Expr> {
    let builder = ExprBuilder::new(Span::dummy_span());
    let mut mapping = HashMap::new();

    let idents: Vec<_> = translate.local_idents().collect();

    for ident in idents {
        // Build a variable expression to feed into t_symbolic
        let var_expr = builder.var(ident.clone(), translate.ctx.tcx());
        let symbolic = translate.t_symbolic(&var_expr);

        let lit_opt = match &symbolic {
            Symbolic::Bool(v) => v.eval(model).ok().map(|b| builder.bool_lit(b)),

            Symbolic::Int(v) => v
                .eval(model)
                .ok()
                .map(|i: BigInt| builder.frac_lit(BigRational::from_integer(i))),

            Symbolic::UInt(v) => v.eval(model).ok().map(|i: BigInt| {
                if i >= BigInt::from(0) {
                    match u128::try_from(i.clone()) {
                        Ok(u) => builder.uint(u),
                        Err(_) => builder.frac_lit(BigRational::from_integer(i)),
                    }
                } else {
                    builder.frac_lit(BigRational::from_integer(i))
                }
            }),

            Symbolic::Real(v) => {
                let eval = v.eval(model);
                eval.ok().map(|r: BigRational| builder.signed_frac_lit(r))
            }

            Symbolic::UReal(v) => {
                let eval = v.eval(model);
                eval.ok()
                    .map(|r: BigRational| builder.frac_lit_not_extended(r))
            }

            Symbolic::EUReal(v) => v.eval(model).ok().map(|r| match r {
                ConcreteEUReal::Real(rat) => builder.frac_lit(rat),
                ConcreteEUReal::Infinity => builder.infinity_lit(),
            }),

            _ => None,
        };

        if let Some(ref lit) = lit_opt {
            mapping.insert(ident.clone(), lit.clone());
        }
    }

    mapping
}

/// "Instantiate" an expression with concrete values from a mapping.
/// To do this, wrap the expression in nested `Subst` expressions.
/// Then later tunfolding can take care of the actual substitutions.
pub fn subst_from_mapping<'ctx>(mapping: HashMap<ast::symbol::Ident, Expr>, vc: &Expr) -> Expr {
    let mut wrapped = vc.clone();
    for (ident, expr) in mapping {
        wrapped = Shared::new(ExprData {
            kind: ExprKind::Subst(ident, expr, wrapped.clone()),
            ty: wrapped.ty.clone(),
            span: vc.span,
        });
    }
    wrapped
}

/// Get a model for a BoolVcProveTask representing a constraint and return it as a hashmap
pub fn get_model_for_constraints<'smt, 'ctx, 'tcx: 'ctx>(
    ctx: &'ctx z3::Context,
    options: &VerifyCommand,
    limits_ref: &LimitsRef,
    constraints: BoolVcProveTask,
    translate: &mut TranslateExprs<'smt, 'ctx>,
) -> Result<Option<HashMap<ast::symbol::Ident, Expr>>, CaesarError> {
    let mut constraints_prove_task = SmtVcProveTask::translate(constraints, translate);
    if !options.opt_options.no_simplify {
        constraints_prove_task.simplify();
    }
    let mut prover = Prover::new(&ctx, IncrementalMode::Native);
    if let Some(remaining) = limits_ref.time_left() {
        prover.set_timeout(remaining);
    }
    // Add axioms and assumptions
    translate.ctx.add_lit_axioms_to_prover(&mut prover);
    translate
        .ctx
        .uninterpreteds()
        .add_axioms_to_prover(&mut prover);
    translate
        .local_scope()
        .add_assumptions_to_prover(&mut prover);

    // Add the verification condition. This should be checked for satisfiability.
    // Therefore, add_assumption is used (which just adds it as an smtlib assert)
    // vs. add_provable, which would negate it first.
    prover.add_assumption(&constraints_prove_task.vc);

    // Run solver & retrieve model if available
    prover.check_sat();
    let model = prover.get_model();

    // If we find a model for the template constraints, filter it to the template variables and create a mapping from it.
    if let Some(template_model) = model {
        let mapping = create_subst_mapping(&template_model, translate);
        Ok(Some(mapping))
    } else {
        // No template model found;.
        Ok(None)
    }
}

pub fn get_functions_from_source_unit(source_unit: &SourceUnit) -> Vec<Ident> {
    let mut funcs = Vec::new();
    if let SourceUnit::Decl(decl) = source_unit {
        if let DeclKind::DomainDecl(domain_ref) = decl {
            let domain = domain_ref.borrow();
            for spec in &domain.body {
                if let DomainSpec::Function(func_ref) = spec {
                    let func = func_ref.borrow();
                    funcs.push(func.name.clone());
                }
            }
        }
    }
    funcs
}

struct CallArgCollector<'a> {
    funcs: &'a [Ident],
    args: Vec<Expr>,
}

impl<'a> CallArgCollector<'a> {
    fn new(funcs: &'a [Ident]) -> Self {
        Self {
            funcs,
            args: Vec::new(),
        }
    }
}

impl<'a> VisitorMut for CallArgCollector<'a> {
    type Err = ();

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Call(ref func, ref args) = e.kind {
            if self.funcs.contains(func) {
                // collect arguments
                for arg in args {
                    self.args.push(arg.clone());
                }
            }
        }

        // always recurse
        walk_expr(self, e)
    }
}

pub struct InsertAssumeBeforeCalls<'a> {
    pub(crate) func_idents: &'a [Ident],
    pub(crate) direction: Direction,
}

impl<'a> InsertAssumeBeforeCalls<'a> {

      fn guarded_args(&self, e: &Expr) -> Vec<Expr> {
        let mut collector = CallArgCollector::new(self.func_idents);

        // clone so we can walk mutably without touching the original
        let mut e_clone = e.clone();
        collector.visit_expr(&mut e_clone).unwrap();

        collector.args
    }
    fn make_assume_seq_for_args(
        &self,
        span: Span,
        args: Vec<Expr>,
        original: StmtKind,
    ) -> StmtKind {
        let builder = ExprBuilder::new(Span::dummy_span());

        let mut stmts = Vec::new();

        for arg in args {
            let mut le_expr = builder.binary(
                BinOpKind::Le,
                Some(TyKind::Bool),
                arg.clone(),
                builder.binary(BinOpKind::Add, Some(arg.ty.clone().unwrap_or(TyKind::Int)), builder.one_lit(&arg.ty.clone().unwrap_or(TyKind::Int)), builder.one_lit(&arg.ty.clone().unwrap_or(TyKind::Int)))
                // builder.one_lit(&arg.ty.clone().unwrap_or(TyKind::Int)),
            );
            if self.direction == Direction::Up {
                le_expr = builder.unary(UnOpKind::Not, Some(TyKind::Bool), le_expr);
            }
            let assume_expr = builder.unary(UnOpKind::Embed, Some(TyKind::EUReal), le_expr);

            stmts.push(Spanned {
                span,
                node: StmtKind::Assume(self.direction, assume_expr),
            });
        }

        stmts.push(Spanned { span, node: original });

        StmtKind::Seq(stmts)
    }
}

impl<'a> VisitorMut for InsertAssumeBeforeCalls<'a> {
    type Err = ();

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        // println!("visiting stmt {s}");
        let span = s.span;

        // -------- Phase 1: collect guarded arguments
        let args: Vec<Expr> = match &s.node {
            StmtKind::Var(decl) =>
                decl.borrow().init
                    .as_ref()
                    .map(|e| self.guarded_args(e))
                    .unwrap_or_default(),

            StmtKind::Assign(_, e)
            | StmtKind::Assert(_, e)
            | StmtKind::Assume(_, e)
            | StmtKind::Compare(_, e)
            | StmtKind::Tick(e) =>
                self.guarded_args(e),

            StmtKind::If(cond, _, _)
            | StmtKind::While(cond, _) =>
                self.guarded_args(cond),

            _ => Vec::new(),
        };

        // -------- Phase 2: rewrite
        if !args.is_empty() {
            let original = std::mem::replace(&mut s.node, StmtKind::Seq(vec![]));
            println!("original statement {original}");
            s.node = self.make_assume_seq_for_args(span, args, original);
            println!("replaced with {s}");
            return Ok(());
        }

        // -------- Phase 3: recurse
        walk_stmt(self, s)
    }
}
