use std::{rc::Rc, time::Instant};

use indexmap::{IndexMap, IndexSet};
use num::{BigInt, BigRational};

use z3::{Context, Goal};
use z3rro::{
    eureal::ConcreteEUReal,
    model::{InstrumentedModel, SmtEval, SmtEvalError},
    probes::ProbeSummary,
    prover::{IncrementalMode, Prover},
};

use crate::{
    ast::{
        self,
        visit::{walk_expr, walk_stmt, VisitorMut},
        BinOpKind, DeclKind, Direction, DomainSpec, Expr, ExprBuilder, ExprData, ExprKind, Ident,
        Range, Shared, Span, Spanned, Stmt, StmtKind, TyKind, UnOpKind,
    },
    driver::{
        commands::verify::VerifyCommand,
        error::CaesarError,
        front::SourceUnit,
        quant_proof::{BoolVcProveTask, QuantVcProveTask},
        smt_proof::SmtVcProveTask,
    },
    opt::unfolder::Unfolder,
    resource_limits::LimitsRef,
    smt::{symbolic::Symbolic, translate_exprs::TranslateExprs, uninterpreted::FuncEntry, SmtCtx},
    tyctx::TyCtx,
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
pub fn create_subst_mapping<'ctx>(
    idents: IndexSet<Ident>,
    model: &InstrumentedModel<'ctx>,
    translate: &mut crate::smt::translate_exprs::TranslateExprs<'_, 'ctx>,
) -> IndexMap<ast::symbol::Ident, Expr> {
    let builder = ExprBuilder::new(Span::dummy_span());
    let mut mapping = IndexMap::new();

    for ident in idents {
        let var_expr = builder.var(ident.clone(), translate.ctx.tcx());
        let symbolic = translate.t_symbolic(&var_expr);

        let lit_opt = match &symbolic {
            Symbolic::Bool(v) => {
                let b = v.eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for {ident:?}: {e}"));
                Some(builder.bool_lit(b))
            }

            Symbolic::Int(v) => {
                let i: BigInt = v.eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for {ident:?}: {e}"));
                Some(builder.frac_lit(BigRational::from_integer(i)))
            }

            Symbolic::UInt(v) => {
                let i: BigInt = v.eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for {ident:?}: {e}"));

                let lit = if i >= BigInt::from(0) {
                    match u128::try_from(i.clone()) {
                        Ok(u) => builder.uint(u),
                        Err(_) => builder.frac_lit(BigRational::from_integer(i)),
                    }
                } else {
                    builder.frac_lit(BigRational::from_integer(i))
                };

                Some(lit)
            }

            Symbolic::Real(v) => {
                let r: BigRational = v.eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for {ident:?}: {e}"));
                Some(builder.signed_frac_lit(r))
            }

            Symbolic::UReal(v) => {
                let r: BigRational = v.eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for {ident:?}: {e}"));
                Some(builder.frac_lit_not_extended(r))
            }

            Symbolic::EUReal(v) => {
                let r = v.eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for {ident:?}: {e}"));

                let lit = match r {
                    ConcreteEUReal::Real(rat) => builder.frac_lit(rat),
                    ConcreteEUReal::Infinity => builder.infinity_lit(),
                };

                Some(lit)
            }

            _ => None,
        };

        if let Some(lit) = lit_opt {
            mapping.insert(ident.clone(), lit);
        }
    }

    mapping
}
/// "Instantiate" an expression with concrete values from a mapping.
/// To do this, wrap the expression in nested `Subst` expressions.
/// Then later tunfolding can take care of the actual substitutions.
pub fn subst_from_mapping<'ctx>(
    mapping: IndexMap<ast::symbol::Ident, Expr>,
    vc: &Expr,
    limits_ref: &LimitsRef,
    smt_ctx: &SmtCtx<'ctx>,
) -> Result<Expr, CaesarError> {
    let mut wrapped = vc.clone();
    for (ident, expr) in mapping {
        wrapped = Shared::new(ExprData {
            kind: ExprKind::Subst(ident, expr, wrapped.clone()),
            ty: wrapped.ty.clone(),
            span: vc.span,
        });
    }

    let mut unfolder = Unfolder::new(limits_ref.clone(), &smt_ctx);
    unfolder.visit_expr(&mut wrapped)?;
    Ok(wrapped)
}

pub fn get_model_for_constraints<'smt, 'ctx, 'tcx: 'ctx>(
    prover: &mut Prover<'ctx>,
    options: &VerifyCommand,
    constraints: BoolVcProveTask,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    idents: IndexSet<Ident>,
    ctx: &'ctx Context,
) -> Result<Option<IndexMap<ast::symbol::Ident, Expr>>, CaesarError> {
    // Translate only the NEW constraint
    let mut constraints_prove_task = SmtVcProveTask::translate(constraints, translate);

    if !options.opt_options.no_simplify {
        constraints_prove_task.simplify();
    }

    prover.push();

    prover.add_assumption(&constraints_prove_task.vc);

    if options.debug_options.print_smt {
        println!("Current solver state for constraints:");
        println!("{}", prover.get_smtlib().into_string());
    }

    let total_start = Instant::now();

    if options.debug_options.z3_probe {
        let goal = Goal::new(ctx, false, false, false);
        for assertion in prover.get_assertions() {
            goal.assert(&assertion);
        }
        eprintln!("Constraint Probe results: {}", ProbeSummary::probe(ctx, &goal));
    }
    let res = prover.check_sat();

    // println!("check_sat result: {:?}", res);

    // match res {
    //     z3::SatResult::Unsat => {
    //         println!("unsat");
    //         println!("TIME: (constraint) total solving time: {:.3?}", total_start.elapsed());
    //         return Ok(None);
    //     }
    //     z3::SatResult::Unknown => {
    //         println!("unknown: {:?}", prover.get_reason_unknown().unwrap());
    //         println!("TIME: (constraint) total solving time: {:.3?}", total_start.elapsed());
    //         return Ok(None);
    //     }
    //     z3::SatResult::Sat => {
    //         println!("sat");
    //         println!("TIME: (constraint) check_sat took: {:.3?}", total_start.elapsed());

    //     }
    // }

    // --------------------
    // Measure get_model()
    // --------------------
    let model_start = Instant::now();
    let model_opt = prover.get_model();
    let model_duration = model_start.elapsed();

    // println!("TIME (constraint): get_model took: {:.3?}", model_duration);
    // println!("TIME (constraint): total solving time: {:.3?}", total_start.elapsed());

    if let Some(model) = model_opt {
        prover.pop();
        prover.add_assumption(&constraints_prove_task.vc);

        let mapping = create_subst_mapping(idents, &model, translate);
        Ok(Some(mapping))
    } else {
        Ok(None)
    }
}

// /// Get a model for a BoolVcProveTask representing a constraint and return it as a hashmap
// pub fn get_model_for_constraints<'smt, 'ctx, 'tcx: 'ctx>(
//     ctx: &'ctx z3::Context,
//     options: &VerifyCommand,
//     limits_ref: &LimitsRef,
//     constraints: BoolVcProveTask,
//     translate: &mut TranslateExprs<'smt, 'ctx>,
//     idents: IndexSet<Ident>,
//     ranges_constraints: Vec<BoolVcProveTask>,

// ) -> Result<Option<IndexMap<ast::symbol::Ident, Expr>>, CaesarError> {
//     let mut constraints_prove_task = SmtVcProveTask::translate(constraints, translate);
//     if  !options.opt_options.no_simplify {
//         constraints_prove_task.simplify();
//     }
//     let mut prover = Prover::new(&ctx, IncrementalMode::Emulated);
//     // if let Some(remaining) = limits_ref.time_left() {
//     //     prover.set_timeout(remaining);
//     // }

//     // Add axioms and assumptions
//     // Maybe the bug is here?
//     translate.ctx.add_lit_axioms_to_prover(&mut prover);
//     translate
//         .ctx
//         .uninterpreteds()
//         .add_axioms_to_prover(&mut prover);
//     translate
//         .local_scope()
//         .add_assumptions_to_prover(&mut prover);

//         for constraint in ranges_constraints {
//             let smt_task = SmtVcProveTask::translate(constraint, translate);
//             prover.add_assumption(&smt_task.vc);
//         }
//     // Add the verification condition. This should be checked for satisfiability.
//     // Therefore, add_assumption is used (which just adds it as an smtlib assert)
//     // vs. add_provable, which would negate it first.
//     prover.add_assumption(&constraints_prove_task.vc);

//     println!("Constraints prove task");
//     println!("{}",prover.get_smtlib().into_string());

//     // Run solver & retrieve model if available
//     let res: z3::SatResult = prover.check_sat();
//     println!("after check sat");
//     println!("{:?}",res);

//     match res {
//             z3::SatResult::Unsat => println!("unsat"),
//             z3::SatResult::Unknown => println!("unknown: {:?}",prover.get_reason_unknown().unwrap()),
//             z3::SatResult::Sat => println!("sat")
//         }
//     let model = prover.get_model();

//     // If we find a model for the tema checplate constraints, filter it to the template variables and create a mapping from it.
//     if let Some(template_model) = model {
//         let mapping = create_subst_mapping(idents, &template_model, translate);
//         Ok(Some(mapping))
//     } else {
//         // No template model found;.
//         Ok(None)
//     }
// }

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
                // builder.binary(BinOpKind::Add, Some(arg.ty.clone().unwrap_or(TyKind::Int)), builder.one_lit(&arg.ty.clone().unwrap_or(TyKind::Int)), builder.one_lit(&arg.ty.clone().unwrap_or(TyKind::Int)))
                builder.one_lit(&arg.ty.clone().unwrap_or(TyKind::Int)),
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

        stmts.push(Spanned {
            span,
            node: original,
        });

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
            StmtKind::Var(decl) => decl
                .borrow()
                .init
                .as_ref()
                .map(|e| self.guarded_args(e))
                .unwrap_or_default(),

            StmtKind::Assign(_, e)
            | StmtKind::Assert(_, e)
            | StmtKind::Assume(_, e)
            | StmtKind::Compare(_, e)
            | StmtKind::Tick(e) => self.guarded_args(e),

            StmtKind::If(cond, _, _) | StmtKind::While(cond, _) => self.guarded_args(cond),

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

pub fn canonical_form(map: &IndexMap<Ident, Expr>) -> String {
    let mut items: Vec<_> = map.iter().collect();

    items.sort_by_key(|(ident, _)| ident.to_string());

    items
        .into_iter()
        .map(|(ident, expr)| format!("{}={}", ident, expr))
        .collect::<Vec<_>>()
        .join(";")
}

pub struct PiecewiseLinearCounter {
    pub count: usize,
}

impl PiecewiseLinearCounter {
    pub fn new() -> Self {
        Self { count: 0 }
    }
}

impl VisitorMut for PiecewiseLinearCounter {
    type Err = ();

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Binary(bin_op, lhs, _) = &expr.kind {
            if bin_op.node == BinOpKind::Mul {
                if let ExprKind::Unary(un_op, _) = &lhs.kind {
                    if un_op.node == UnOpKind::Iverson {
                        self.count += 1;
                    }
                }
            }
        }

        walk_expr(self, expr)
    }
}

pub fn create_range_constraint(ident: Ident, range: &Range) -> Expr {
    let builder = ExprBuilder::new(Span::dummy_span());

    let var = builder.var_ty(ident.clone(), TyKind::UInt);

    let lower = builder.binary(
        BinOpKind::Le,
        Some(TyKind::Bool),
        builder.uint(range.lower.into()),
        var.clone(),
    );

    let upper = builder.binary(
        BinOpKind::Le,
        Some(TyKind::Bool),
        var,
        builder.uint(range.upper.into()),
    );

    builder.binary(BinOpKind::And, Some(TyKind::Bool), lower, upper)
}

pub fn range_constraints_to_bool_tasks(
    constraints: Vec<Expr>,
    dummy_quant: QuantVcProveTask,
) -> Vec<BoolVcProveTask> {
    constraints
        .into_iter()
        .map(|constraint| BoolVcProveTask {
            quant_vc: dummy_quant.clone(), // unused, but well-formed
            vc: constraint,
        })
        .collect()
}

pub fn collect_ranges_from_decls(
    declarations: &IndexMap<Ident, Rc<DeclKind>>,
) -> IndexMap<Ident, Range> {
    let mut ranges = IndexMap::new();

    for (ident, decl) in declarations.iter() {
        if let DeclKind::VarDecl(var_ref) = decl.as_ref() {
            let var = var_ref.borrow();
            if let Some(range) = &var.range {
                ranges.insert(ident.clone(), range.clone());
            }
        }
    }

    ranges
}
