use num::{BigInt, BigRational};
use z3::{Config, Context, SatResult};
use z3rro::prover::{IncrementalMode, Prover};

use crate::{
    ast::{
        decl, util::FreeVariableCollector, visit::VisitorMut, BinOpKind, DeclKind, DeclRef, Expr,
        ExprBuilder, ExprData, ExprKind, Ident, Range, Shared, Span, Symbol, TyKind, UnOpKind,
        VarDecl, VarKind,
    },
    driver::commands::verify::VerifyCommand,
    invariant_synthesis::inv_synth_helpers::subst_from_mapping,
    opt::unfolder::Unfolder,
    resource_limits::LimitsRef,
    smt::{
        funcs::axiomatic::AxiomaticFunctionEncoder,
        translate_exprs::TranslateExprs,
        uninterpreted::{self, Uninterpreteds},
        DepConfig, SmtCtx,
    },
    tyctx::TyCtx,
};
use std::collections::HashMap;
pub type ArgParamMap = HashMap<*const Expr, Expr>;
pub type VarToParamMap = HashMap<Ident, Expr>;

pub fn collect_call_var_param_maps(
    expr: &Expr,
    target_ident: &Ident,
    params: &[Expr],
) -> Vec<VarToParamMap> {
    let mut out = Vec::new();
    collect_call_var_param_maps_rec(expr, target_ident, params, &mut out);
    out
}
fn collect_call_var_param_maps_rec(
    expr: &Expr,
    target_ident: &Ident,
    params: &[Expr],
    out: &mut Vec<VarToParamMap>,
) {
    match &expr.kind {
        ExprKind::Call(func_ident, args) if func_ident.name == target_ident.name => {
            if args.len() == params.len() {
                let mut map = HashMap::new();

                for (arg, param) in args.iter().zip(params.iter()) {
                    if let ExprKind::Var(id) = &arg.kind {
                        // program var → formal param expr
                        map.insert(id.clone(), param.clone());
                    }
                }

                if !map.is_empty() {
                    out.push(map);
                }
            }

            // Still recurse into arguments
            for arg in args {
                collect_call_var_param_maps_rec(arg, target_ident, params, out);
            }
        }

        _ => {
            for child in expr.children() {
                collect_call_var_param_maps_rec(child, target_ident, params, out);
            }
        }
    }
}

// Helper: generate all monomials of given degree (combinations with repetition)
fn gen_monomials(
    vars: &[Expr],
    degree: usize,
    start: usize,
    current: &mut Vec<Expr>,
    out: &mut Vec<Vec<Expr>>,
) {
    if current.len() == degree {
        out.push(current.clone());
        return;
    }

    for i in start..vars.len() {
        current.push(vars[i].clone());
        gen_monomials(vars, degree, i, current, out);
        current.pop();
    }
}

// Helper: multiply all expressions in a slice
fn multiply_all(builder: &ExprBuilder, output_type: &TyKind, factors: &[Expr]) -> Expr {
    let mut acc = factors[0].clone();
    for f in &factors[1..] {
        acc = builder.binary(BinOpKind::Mul, Some(output_type.clone()), acc, f.clone());
    }
    // println!("created multiplication {acc:?}");
    acc
}

fn build_polynomial(
    name_addon: &str,
    synth_name: &Ident,
    builder: &ExprBuilder,
    tcx: &TyCtx,
    declare_template_var: &mut dyn FnMut(String) -> decl::VarDecl,
    program_var_decls: &[VarDecl],
    signed_output_type: TyKind,
    max_degree: usize,
) -> Expr {
    let vars: Vec<Expr> = program_var_decls
        .iter()
        .map(|vardecl| {
            let mut v = builder.var(vardecl.name, tcx);
            if v.ty != Some(signed_output_type.clone()) {
                v = builder.cast(signed_output_type.clone(), v);
            }
            v
        })
        .collect();

    let mut poly: Option<Expr> = None;

    for degree in 1..=max_degree {
        let mut monomials = Vec::new();
        gen_monomials(&vars, degree, 0, &mut Vec::new(), &mut monomials);

        for (idx, mono) in monomials.into_iter().enumerate() {
            let prod = multiply_all(builder, &signed_output_type, &mono);

            let coeff_name = format!("tvar_{synth_name}_{name_addon}_deg{degree}_m{idx}");
            let coeff_decl = declare_template_var(coeff_name);
            let coeff = builder.var(coeff_decl.name, tcx);

            let term = builder.binary(
                BinOpKind::Mul,
                Some(signed_output_type.clone()),
                coeff,
                prod,
            );

            poly = Some(poly.map_or(term.clone(), |acc| {
                builder.binary(BinOpKind::Add, Some(signed_output_type.clone()), acc, term)
            }));
        }
    }

    let const_decl = declare_template_var(format!("tvar_{synth_name}_{name_addon}_const"));
    let constant = builder.var(const_decl.name, tcx);

    poly.map_or(constant.clone(), |acc| {
        builder.binary(
            BinOpKind::Add,
            Some(signed_output_type.clone()),
            acc,
            constant,
        )
    })
}

fn build_rational_combination(
    name_addon: String,
    synth_name: &Ident,
    builder: &ExprBuilder,
    tcx: &TyCtx,
    declare_template_var: &mut dyn FnMut(String) -> decl::VarDecl,
    program_var_decls: &[VarDecl],
    signed_output_type: TyKind,
    output_type: &TyKind,
    max_degree: usize,
) -> Expr {
    // Numerator
    let numerator = build_polynomial(
        &format!("{name_addon}_num"),
        synth_name,
        builder,
        tcx,
        declare_template_var,
        program_var_decls,
        signed_output_type.clone(),
        max_degree,
    );
    println!("numerator: {numerator}");

    // Denominator polynomial
    let denom_poly = build_polynomial(
        &format!("{name_addon}_den"),
        synth_name,
        builder,
        tcx,
        declare_template_var,
        program_var_decls,
        signed_output_type.clone(),
        max_degree,
    );
    println!("denominator: {denom_poly}");

    let denom_pos = builder.ite(
        Some(signed_output_type.clone()),
        builder.binary(
            BinOpKind::Gt,
            Some(TyKind::Bool),
            denom_poly.clone(),
            builder.zero_lit(&signed_output_type),
        ),
        denom_poly,
        builder.one_lit(&signed_output_type),
    );
    // Enforce denominator > 0 by doing: 1 + abs(denom_poly)
    // let one = builder.one_lit(&signed_output_type.clone());

    // let abs_name = Ident::with_dummy_span(Symbol::intern("abs"));
    // let abs_denom = Shared::new(ExprData {
    //     kind: ExprKind::Call(abs_name, vec![denom_poly]),
    //     ty: Some(signed_output_type.clone()),
    //     span: Span::dummy_span(),
    // });

    // let safe_denom = builder.binary(
    //     BinOpKind::Add,
    //     Some(signed_output_type.clone()),
    //     one,
    //     abs_denom,
    // );

    // Division
    let mut rational = builder.binary(
        BinOpKind::Div,
        Some(signed_output_type.clone()),
        numerator,
        denom_pos,
    );

    // Clamp (same logic as polynomial case)
    let clamp_with_zero_name = Ident::with_dummy_span(Symbol::intern("clamp_with_zero"));

    let clamp_ty = if signed_output_type == TyKind::Int || signed_output_type == TyKind::UInt {
        TyKind::UInt
    } else {
        TyKind::UReal
    };

    rational = Shared::new(ExprData {
        kind: ExprKind::Call(clamp_with_zero_name, vec![rational]),
        ty: Some(clamp_ty),
        span: Span::dummy_span(),
    });

    if rational.ty != Some(output_type.clone()) {
        rational = builder.cast(output_type.clone(), rational);
    }

    rational
}

// Main function: build polynomial template up to max_degree
fn build_polynomial_combination(
    name_addon: String,
    synth_name: &Ident,
    builder: &ExprBuilder,
    tcx: &TyCtx,
    declare_template_var: &mut dyn FnMut(String) -> decl::VarDecl,
    program_var_decls: &[VarDecl],
    signed_output_type: TyKind,
    output_type: &TyKind,
    max_degree: usize,
) -> Expr {
    // Collect program variables as expressions (casted)
    let vars: Vec<Expr> = program_var_decls
        .iter()
        .map(|vardecl| {
            let mut v = builder.var(vardecl.name, tcx);
            if v.ty != Some(signed_output_type.clone()) {
                v = builder.cast(signed_output_type.clone(), v);
            }
            v
        })
        .collect();

    let mut poly: Option<Expr> = None;

    // Degrees 1 ..= max_degree
    for degree in 1..=max_degree {
        let mut monomials = Vec::new();
        gen_monomials(&vars, degree, 0, &mut Vec::new(), &mut monomials);

        for (idx, mono) in monomials.into_iter().enumerate() {
            let prod = multiply_all(builder, &signed_output_type, &mono);

            let coeff_name = format!("tvar_{synth_name}_{name_addon}_deg{degree}_m{idx}");
            let coeff_decl = declare_template_var(coeff_name);
            let coeff = builder.var(coeff_decl.name, tcx);

            let term = builder.binary(
                BinOpKind::Mul,
                Some(signed_output_type.clone()),
                coeff,
                prod,
            );

            poly = Some(poly.map_or(term.clone(), |acc| {
                builder.binary(BinOpKind::Add, Some(signed_output_type.clone()), acc, term)
            }));
        }
    }

    // Add constant term (degree 0)
    let const_decl = declare_template_var(format!("tvar_{synth_name}_{name_addon}_const"));
    let constant = builder.var(const_decl.name, tcx);

    let poly_with_const = poly.map_or(constant.clone(), |acc| {
        builder.binary(
            BinOpKind::Add,
            Some(signed_output_type.clone()),
            acc,
            constant,
        )
    });

    // Clamp with zero (same logic as your original code)
    let clamp_with_zero_name = Ident::with_dummy_span(Symbol::intern("clamp_with_zero"));

    let clamp_with_zero_type =
        if signed_output_type == TyKind::Int || signed_output_type == TyKind::UInt {
            TyKind::UInt
        } else {
            TyKind::UReal
        };

    let mut final_expr = builder.ite(
        Some(clamp_with_zero_type.clone()),
        builder.binary(
            BinOpKind::Ge,
            Some(TyKind::Bool),
            poly_with_const.clone(),
            builder.zero_lit(&signed_output_type),
        ),
        Shared::new(ExprData {
            kind: ExprKind::Call(clamp_with_zero_name, vec![poly_with_const.clone()]),
            ty: Some(clamp_with_zero_type.clone()),
            span: Span::dummy_span(),
        }),
        builder.zero_lit(&clamp_with_zero_type),
    );

    println!("final expr {final_expr}");
    println!("clamp_with_zero_type {clamp_with_zero_type}");
    println!("signed_outp {signed_output_type}");
    println!("poly_with_const_type {:?}", poly_with_const.ty);
    // let mut final_expr = Shared::new(ExprData {
    //     kind: ExprKind::Call(clamp_with_zero_name, vec![poly_with_const.clone()]),
    //     ty: Some(clamp_with_zero_type),
    //     span: Span::dummy_span(),
    // });

    if final_expr.ty != Some(output_type.clone()) {
        final_expr = builder.cast(output_type.clone(), final_expr);
    }

    final_expr
}
pub fn collect_relevant_bool_conditions(
    _synth_val: &uninterpreted::FuncEntry,
    vc_expr: &Expr,
    mappings: Vec<VarToParamMap>,
    tcx: &TyCtx,
    limits_ref: LimitsRef,
) -> (Vec<Expr>, HashMap<Ident, Ident>) {
    let mut out = Vec::new();

    let ctx = Context::new(&Config::default());
    let dep_config = DepConfig::SpecsOnly;
    let smt_ctx_local = SmtCtx::new(
        &ctx,
        &tcx,
        Box::new(AxiomaticFunctionEncoder::default()),
        dep_config,
    );
    let mut unfolder = Unfolder::new(limits_ref.clone(), &smt_ctx_local);
    // param → program var
    let mut param_var_mapping: HashMap<Ident, Ident> = HashMap::new();

    'bools: for b in collect_bool_conditions(vc_expr) {
        let vars = collect_program_vars(&b);

        // Try to explain this boolean via one call-site mapping
        for mapping in &mappings {
            // All vars must be mapped
            if vars.iter().all(|v| mapping.contains_key(v)) {
                // Wrap boolean in substitutions
                let mut wrapped = subst_from_mapping(mapping.clone(), &b);
                let _ = unfolder.visit_expr(&mut wrapped);

                out.push(wrapped);

                // Record param → program var info
                for (prog_var, param_expr) in mapping {
                    if let ExprKind::Var(param_id) = &param_expr.kind {
                        param_var_mapping
                            .entry(param_id.clone())
                            .or_insert_with(|| prog_var.clone());
                    }
                }

                continue 'bools;
            }
        }
    }

    (out, param_var_mapping)
}

fn collect_program_vars(expr: &Expr) -> indexmap::IndexSet<Ident> {
    let mut collector = FreeVariableCollector::new();
    let mut cloned = expr.clone();

    let vars = collector.collect_and_clear(&mut cloned);

    vars
}

/// Construct Boolean predicates that partition each ranged variable into
/// a fixed number of contiguous regions, then take the Cartesian product
/// across variables.
///
/// Each variable is split into `split_count` intervals over its numeric range.
/// ([lower_bound,upper_bound])
/// For each interval we generate a predicate of the form:
///
///     (var > lower_cut) && (var <= upper_cut)
///
/// To not exclude var = lower_bound we also include the "interval" var = lower_bound
/// The final result is the conjunction of one region predicate per variable,
/// enumerated via a Cartesian product.
pub fn get_fix_region_splits<'ctx>(
    ranged_vars: &[(Expr, Range)], // program variables with precomputed numeric ranges
    split_count: usize,            // number of uniform splits per variable
    builder: &mut ExprBuilder,
) -> Vec<Expr> {
    // Trivial case:
    //  - no variables, or
    //  - zero requested splits
    //
    // In both cases, return a single unconstrained region (true).
    if ranged_vars.is_empty() || split_count == 0 {
        return vec![builder.bool_lit(true)];
    }

    // For each variable, build a list of mutually exclusive region predicates.
    let mut per_var_conditions: Vec<Vec<Expr>> = Vec::new();

    for (var, range) in ranged_vars {
        // Convert integer bounds into rationals so we can compute fractional cuts.
        let lower = BigRational::from_integer(BigInt::from(range.lower));
        let upper = BigRational::from_integer(BigInt::from(range.upper));
        let width = &upper - &lower;

        // All interval arithmetic is done in the Real domain.
        let real_var = if var.ty.clone().unwrap() == TyKind::Real {
            var.clone()
        } else {
            builder.cast(TyKind::Real, var.clone())
        };

        // Region predicates corresponding to this single variable.
        let mut conditions_for_var = Vec::new();

        // Generate `split_count` contiguous intervals over [lower, upper].
        //
        // Interval i corresponds to:
        //   (lower + i/split_count * width,
        //    lower + (i+1)/split_count * width]
        //
        for i in 0..split_count {
            let lower_ratio = BigRational::new(i.into(), split_count.into());
            let upper_ratio = BigRational::new((i + 1).into(), split_count.into());

            let lower_cut = &lower + &width * lower_ratio;
            let upper_cut = &lower + &width * upper_ratio;

            let lower_expr = builder.signed_frac_lit(lower_cut);
            let upper_expr = builder.signed_frac_lit(upper_cut);

            let gt_lower = builder.binary(
                BinOpKind::Gt,
                Some(TyKind::Bool),
                real_var.clone(),
                lower_expr,
            );

            let le_upper = builder.binary(
                BinOpKind::Le,
                Some(TyKind::Bool),
                real_var.clone(),
                upper_expr,
            );

            let interval_pred =
                builder.binary(BinOpKind::And, Some(TyKind::Bool), gt_lower, le_upper);

            conditions_for_var.push(interval_pred);
        }

        //   var == lower
        let lower_eq = builder.binary(
            BinOpKind::Eq,
            Some(TyKind::Bool),
            real_var.clone(),
            builder.signed_frac_lit(lower),
        );

        conditions_for_var.push(lower_eq);

        // Store all regions for this variable.
        per_var_conditions.push(conditions_for_var);
    }

    // Combine per-variable region predicates into full region conditions
    // by taking the Cartesian product and conjoining each combination.
    cartesian_and(&per_var_conditions, builder)
}

fn cartesian_and(lists: &[Vec<Expr>], builder: &ExprBuilder) -> Vec<Expr> {
    // Start with a single empty conjunction
    let mut acc: Vec<Expr> = vec![builder.bool_lit(true)];

    for list in lists {
        let mut next = Vec::new();

        for prefix in &acc {
            for item in list {
                // prefix AND item
                let conj = builder.binary(
                    BinOpKind::And,
                    Some(TyKind::Bool),
                    prefix.clone(),
                    item.clone(),
                );
                next.push(conj);
            }
        }

        acc = next;
    }

    acc
}

// Creates the expression (collected_guards x split_conditions) * lc
pub fn assemble_piecewise_expression<'smt, 'ctx>(
    synth_name: &Ident,
    collected_guards: &[Expr],
    split_conditions: &Vec<Expr>,
    builder: &mut ExprBuilder,
    tcx: &TyCtx,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    ctx: &'ctx z3::Context,
    declare_template_var: &mut dyn FnMut(String) -> decl::VarDecl,
    program_var_decls: &[VarDecl],
    signed_output_type: TyKind,
    output_type: &TyKind,
    max_degree: usize,
) -> (Expr, usize, usize) {
    let mut final_expr: Option<Expr> = None;
    let mut num_guard_expressions = 0;

    let clamp_with_zero_type =
        if signed_output_type == TyKind::Int || signed_output_type == TyKind::UInt {
            TyKind::UInt
        } else {
            TyKind::UReal
        };
    let mut num_sat_checks = 0;
    for (i_idx, iv_prod) in collected_guards.iter().enumerate() {
        for (s_idx, split) in split_conditions.iter().enumerate() {
            let both = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                iv_prod.clone(),
                split.clone(),
            );

            // Check satisfiability of guard && split_condition, since this is a short formula
            // and if it is not sat we don't have to add the lc
            // The problem here is that those are not the same variables right?
            // The split variables are the actual function paramters,
            // whereas the other ones are the caller parameter
            // I think this is where the real problem lies
            let expr_z3 = translate.t_bool(&both);
            let mut prover = Prover::new(&ctx, IncrementalMode::Native);
            prover.add_assumption(&expr_z3);

            num_sat_checks = num_sat_checks + 1;
            if prover.check_sat() == SatResult::Sat {
                num_guard_expressions = num_guard_expressions + 1;
                let iverson_both =
                    builder.unary(UnOpKind::Iverson, Some(clamp_with_zero_type.clone()), both);

                // Pass precomputed program_var_decls
                let lc_name = format!("{}_{}", i_idx, s_idx);
                // let lc = build_rational_combination(
                //     lc_name,
                //     synth_name,
                //     builder,
                //     tcx,
                //     declare_template_var,
                //     program_var_decls,
                //     signed_output_type.clone(),
                //     output_type,
                //     max_degree,
                // );
                let lc = build_polynomial_combination(
                    lc_name,
                    synth_name,
                    builder,
                    tcx,
                    declare_template_var,
                    program_var_decls,
                    signed_output_type.clone(),
                    output_type,
                    max_degree,
                );

                let full = builder.binary(
                    BinOpKind::Mul,
                    Some(clamp_with_zero_type.clone()),
                    iverson_both,
                    lc,
                );

                final_expr = Some(match final_expr {
                    None => full,
                    Some(acc) => builder.binary(
                        BinOpKind::Add,
                        Some(clamp_with_zero_type.clone()),
                        acc,
                        full,
                    ),
                });
            }
        }
    }

    (final_expr.unwrap(), num_sat_checks, num_guard_expressions)
}

pub fn build_template_expression<'smt, 'ctx>(
    options: &VerifyCommand,
    synth_name: &Ident,
    synth_val: &uninterpreted::FuncEntry,
    vc_expr: &Expr,
    builder: &mut ExprBuilder,
    tcx: &TyCtx,
    split_count: usize,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    ctx: &'ctx z3::Context,
    limits_ref: LimitsRef,
) -> (Expr, Vec<(Ident, TyKind)>, usize, usize) {
    let mut output_type = TyKind::EUReal;
    if let Some(DeclKind::FuncDecl(func_ref)) = tcx.get(*synth_name).as_deref() {
        output_type = func_ref.borrow().output.clone();
    }

    let mut signed_output_type = output_type.clone();

    if !options.synth_options.unsigned_coefficients {
        signed_output_type = if output_type == TyKind::UInt {
            TyKind::Int
        } else {
            TyKind::Real
        };
    }

    // Storage for all newly created template parameter identifiers
    let mut template_idents: Vec<(Ident, TyKind)> = Vec::new();
    let mut num_sat_checks = 0;

    let mut program_var_decls = Vec::new();
    let mut program_vars = Vec::new();
    let mut program_vars_no_cast = Vec::new();
    let mut program_vars_for_conditions = Vec::new();

    for param in &synth_val.inputs.node {
        let vardecl = VarDecl::from_param(param, VarKind::Input)
            .try_unwrap()
            .unwrap();
        if vardecl.ty != TyKind::Bool {
            let raw = builder.var(vardecl.name, tcx);

            let mut casted = raw.clone();
            if vardecl.ty != signed_output_type {
                casted = builder.cast(signed_output_type.clone(), raw.clone());
            }
            // println!("Created pvar {} of type {:?}", casted, casted.ty);
            program_var_decls.push(vardecl.clone());
            program_vars.push(casted);
            program_vars_no_cast.push(raw);
        }
        program_vars_for_conditions.push(builder.var(vardecl.name, tcx));
    }

    let mappings = collect_call_var_param_maps(vc_expr, synth_name, &program_vars_for_conditions);

    // Template-variable declaration closure
    let mut declare_template_var = |name: String| -> decl::VarDecl {
        let full_name = format!("{}{}", name, split_count + 1);
        let ident = Ident::with_dummy_span(Symbol::intern(&full_name));
        let decl = VarDecl {
            name: ident,
            ty: signed_output_type.clone(),
            kind: VarKind::Input,
            init: None,
            span: Span::dummy_span(),
            created_from: None,
            range: None,
        };
        tcx.declare(crate::ast::DeclKind::VarDecl(DeclRef::new(decl.clone())));
        template_idents.push((decl.name, signed_output_type.clone()));
        decl
    };

    let mut bool_exprs: Vec<Shared<ExprData>> = [].into();
    let mut var_map = [].into();
    // Step 1: Collect Boolean conditions relevant to the inputs
    if split_count >= 1 {
        (bool_exprs, var_map) =
            collect_relevant_bool_conditions(synth_val, vc_expr, mappings, tcx, limits_ref);
    }

    if bool_exprs.is_empty() {
        bool_exprs.push(builder.bool_lit(true));
    }

    // Step 2: Build all split predicates
    let ranged_vars: Vec<(Expr, Range)> = program_var_decls
        .iter()
        .filter_map(|v| {
            let r = v.range.as_ref()?;
            Some((builder.var(v.name, tcx), r.clone()))
        })
        .collect();

    let split_conditions = get_fix_region_splits(&ranged_vars, split_count, builder);

    // Step 3: Compute satisfiable guards from Boolean conditions
    let mut valid_iversons = Vec::new();
    num_sat_checks = num_sat_checks
        + explore_boolean_assignments(
            0,
            bool_exprs.as_slice(),
            builder,
            translate,
            ctx,
            &mut Vec::new(),        // partial assignment
            builder.bool_lit(true), // initial Iverson factor
            &mut valid_iversons,    // output
        );

    // for iv in valid_iversons.clone() {
    //     println!("bool guard: {iv}");
    // }

    // Step 4: Combine original guards × split conditions and multiply each with own lin.exp
    let (mut final_expr, temp_sat_checks, num_guard_expr) = assemble_piecewise_expression(
        synth_name,
        &valid_iversons,
        &split_conditions,
        builder,
        tcx,
        translate,
        ctx,
        &mut declare_template_var,
        &program_var_decls,
        signed_output_type.clone(),
        &output_type,
        options.synth_options.max_degree.unwrap_or(1),
    );
    num_sat_checks = num_sat_checks + temp_sat_checks;

    // Step 5: Substitute only program variables in final_expr
    let free_vars = collect_program_vars(&final_expr);

    // Build substitution iterator only for variables that match program_var_decls
    let subst_iter = free_vars.into_iter().filter_map(|id| {
        // Find index of program_var_decl with same name
        program_var_decls
            .iter()
            .position(|decl| decl.name.name == id.name)
            .map(|idx| (id, program_vars_no_cast[idx].clone()))
    });

    // Apply substitution
    final_expr = builder.subst(final_expr, subst_iter);

    (
        final_expr,
        template_idents,
        valid_iversons.len() * split_conditions.len(),
        num_sat_checks,
    )
}

pub fn get_synth_functions<'ctx>(
    un: &'ctx Uninterpreteds<'ctx>,
) -> HashMap<Ident, &'ctx uninterpreted::FuncEntry<'ctx>> {
    un.functions()
        .iter()
        .filter_map(|(id, f)| if f.syn { Some((id.clone(), f)) } else { None })
        .collect()
}

/// Explores all possible Boolean assignments for a given set of Boolean expressions
/// and accumulates the guards for all satisfiable assignments found.
///
/// This function recursively explores each possible Boolean assignment by branching on
/// whether each Boolean variable is assigned `true` or `false`. For each partial
/// assignment, it builds the corresponding conjunction (these are the guards) and checks
/// whether the assignment satisfies the given Boolean expressions using a SAT solver.
///
/// The recursion stops at a complete assignment (when all Boolean variables have been
/// assigned) or when an unsatisfiable prefix is encountered. If a satisfiable assignment
/// is found, the guards for that assignment are added to the result list.
fn explore_boolean_assignments<'smt, 'ctx>(
    idx: usize,
    bool_exprs: &[Expr],
    builder: &mut ExprBuilder,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    ctx: &'ctx z3::Context,
    partial_assign: &mut Vec<bool>,
    iverson_prod: Expr,
    valid_iversons: &mut Vec<Expr>,
) -> usize {
    // Base case: a complete assignment
    if idx == bool_exprs.len() {
        valid_iversons.push(iverson_prod);
        return 0;
    }

    let mut num_sat_checks = 0;

    // Recursive case: branch on bit = false / true
    for &bit in &[false, true] {
        partial_assign.push(bit);

        let mut new_iverson = iverson_prod.clone();
        {
            let b = bool_exprs[idx].clone();
            let cond = if bit {
                b
            } else {
                builder.unary(UnOpKind::Not, Some(TyKind::Bool), b)
            };

            new_iverson = builder.binary(BinOpKind::And, Some(TyKind::Bool), new_iverson, cond);
        }

        // SAT check for the prefix
        let expr_z3 = translate.t_bool(&new_iverson);
        let mut prover = Prover::new(&ctx, IncrementalMode::Native);
        prover.add_assumption(&expr_z3);

        if prover.check_sat() == SatResult::Sat {
            num_sat_checks += 1 + explore_boolean_assignments(
                idx + 1,
                bool_exprs,
                builder,
                translate,
                ctx,
                partial_assign,
                new_iverson,
                valid_iversons,
            );
        } else {
            tracing::trace!("Pruned UNSAT prefix");
        }

        partial_assign.pop();
    }

    num_sat_checks
}

//TODO!
// Hm this is not really good. In reality we want to take a better look at the pre
// and basically if there is an || or a + , we want to take both + and neg, if not we don't?
// This also holds for asserts
fn _split_vc(expr: &Expr) -> (&Expr, &Expr) {
    match &expr.kind {
        ExprKind::Binary(bin_op, lhs, rhs) => match bin_op.node {
            BinOpKind::Impl => (lhs, rhs),
            BinOpKind::CoImpl => (lhs, rhs),
            _ => panic!("Expected top-level Impl or CoImpl"),
        },
        _ => panic!("Expected top-level implication VC"),
    }
}

/// Collect all boolean expressions that appear either:
///   a) as the condition of an ITE
///   b) as the operand of an Iverson `[expr]`
pub fn collect_bool_conditions(expr: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    let mut seen: Vec<*const Expr> = Vec::new(); // identity via raw pointers
    collect_bool_conditions_rec(expr, &mut out, &mut seen);
    out
}
fn collect_bool_conditions_rec(expr: &Expr, out: &mut Vec<Expr>, seen: &mut Vec<*const Expr>) {
    match &expr.kind {
        // a) ITE condition
        ExprKind::Ite(cond, then_branch, else_branch) => {
            record_if_new(cond, out, seen);

            collect_bool_conditions_rec(cond, out, seen);
            collect_bool_conditions_rec(then_branch, out, seen);
            collect_bool_conditions_rec(else_branch, out, seen);
        }

        // b) Unary Iverson operator
        ExprKind::Unary(un_op, operand) if matches!(un_op.node, UnOpKind::Iverson) => {
            record_if_new(operand, out, seen);
            collect_bool_conditions_rec(operand, out, seen);
        }

        // all other expressions
        _ => {
            for child in expr.children() {
                collect_bool_conditions_rec(child, out, seen);
            }
        }
    }
}
fn record_if_new(expr: &Expr, out: &mut Vec<Expr>, seen: &mut Vec<*const Expr>) {
    let ptr = expr as *const Expr;
    if !seen.contains(&ptr) {
        out.push(expr.clone());
        seen.push(ptr);
    }
}
