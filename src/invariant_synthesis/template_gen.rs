use num::{BigInt, BigRational};
use z3::SatResult;
use z3rro::prover::{IncrementalMode, Prover};

use crate::{
    ast::{
        decl, util::FreeVariableCollector, BinOpKind, DeclKind, DeclRef, Expr, ExprBuilder,
        ExprData, ExprKind, Ident, Range, Shared, Span, Symbol, TyKind, UnOpKind, VarDecl, VarKind,
    },
    smt::{
        translate_exprs::TranslateExprs,
        uninterpreted::{self, Uninterpreteds},
    },
    tyctx::TyCtx,
};
use std::collections::{HashMap, HashSet};

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
fn multiply_all(
    builder: &ExprBuilder,
    output_type: &TyKind,
    factors: &[Expr],
) -> Expr {
    let mut acc = factors[0].clone();
    for f in &factors[1..] {
        acc = builder.binary(
            BinOpKind::Mul,
            Some(output_type.clone()),
            acc,
            f.clone(),
        );
    }
    println!("created multiplication {acc:?}");
    acc
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
    max_degree: usize, // <-- NEW
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

            let coeff_name = format!(
                "tvar_{synth_name}_{name_addon}_deg{degree}_m{idx}"
            );
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
    let const_decl = declare_template_var(format!(
        "tvar_{synth_name}_{name_addon}_const"
    ));
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

    let clamp_with_zero_type = if signed_output_type == TyKind::Int || signed_output_type == TyKind::UInt {
        TyKind::UInt
    } else {
        TyKind::UReal
    };

    let mut final_expr = Shared::new(ExprData {
        kind: ExprKind::Call(clamp_with_zero_name, vec![poly_with_const.clone()]),
        ty: Some(clamp_with_zero_type),
        span: Span::dummy_span(),
    });

    if final_expr.ty != Some(output_type.clone()) {
        final_expr = builder.cast(output_type.clone(), final_expr);
    }

    final_expr
}

pub fn collect_relevant_bool_conditions(
    synth_val: &uninterpreted::FuncEntry,
    vc_expr: &Expr,
) -> Vec<Expr> {
    let mut allowed_vars = HashSet::new();

    for param in &synth_val.inputs.node {
        let vardecl = VarDecl::from_param(param, VarKind::Input)
            .try_unwrap()
            .unwrap();
        allowed_vars.insert(vardecl.name.name);
    }

    collect_bool_conditions(vc_expr)
        .into_iter()
        .filter(|b| {
            let vars = collect_program_vars(b);
            vars.iter().all(|id| allowed_vars.contains(&id.name))
        })
        .collect()
}

fn collect_program_vars(expr: &Expr) -> indexmap::IndexSet<Ident> {
    let mut collector = FreeVariableCollector::new();
    let mut cloned = expr.clone();

    let vars = collector.collect_and_clear(&mut cloned);

    vars
}
pub fn get_fix_region_splits<'ctx>(
    ranged_vars: &[(Expr, Range)], // precomputed program variables + ranges
    split_count: usize,
    builder: &mut ExprBuilder,
) -> Vec<Expr> {
    let mut region_conditions = Vec::new();

    if ranged_vars.is_empty() || split_count == 0 {
        region_conditions.push(builder.bool_lit(true));
        return region_conditions;
    }

    let mut per_var_regions: Vec<Vec<Expr>> = Vec::new();

    for (pv, range) in ranged_vars {
        let l = BigRational::from_integer(BigInt::from(range.lower));
        let u = BigRational::from_integer(BigInt::from(range.upper));
        let width = &u - &l;

        let mut regions_for_this_var = Vec::new();

        for i in 1..=(split_count + 1) {
            let pred = if i == 1 {
                let ratio = BigRational::new(i.into(), split_count.into());
                let cut_val = &l + &width * ratio;
                let cut_expr = builder.signed_frac_lit(cut_val);
                let mut potentially_casted = pv.clone();
                if pv.ty.clone().unwrap() != TyKind::Real {
                    potentially_casted = builder.cast(TyKind::Real, pv.clone())
                }
                builder.binary(
                    BinOpKind::Le,
                    Some(TyKind::Bool),
                    potentially_casted,
                    cut_expr,
                )
            } else {
                let ratio = BigRational::new((i - 1).into(), split_count.into());
                let cut_val = &l + &width * ratio;
                let cut_expr = builder.signed_frac_lit(cut_val);
                let mut potentially_casted = pv.clone();
                if pv.ty.clone().unwrap() != TyKind::Real {
                    potentially_casted = builder.cast(TyKind::Real, pv.clone())
                }
                builder.binary(
                    BinOpKind::Gt,
                    Some(TyKind::Bool),
                    potentially_casted,
                    cut_expr,
                )
            };
            regions_for_this_var.push(pred);
        }

        per_var_regions.push(regions_for_this_var);
    }

    cartesian_and(&per_var_regions, builder)
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

pub fn _get_variable_region_splits<'ctx>(
    program_vars: &[Expr], // precomputed builder variables
    split_count: usize,
    builder: &mut ExprBuilder,
    tcx: &TyCtx,
    declare_template_var: &mut dyn FnMut(String) -> decl::VarDecl,
) -> Vec<Expr> {
    let mut threshold_vars = Vec::<Vec<Expr>>::new();
    for (i, _) in program_vars.iter().enumerate() {
        let mut cuts = Vec::new();
        for j in 0..split_count {
            let name = format!("split_threshold_{}_{}", i, j);
            let decl = declare_template_var(name);
            let t = builder.var(decl.name, tcx);
            cuts.push(t);
        }
        threshold_vars.push(cuts);
    }

    if program_vars.is_empty() || split_count == 0 {
        return vec![builder.bool_lit(true)];
    }

    let n = program_vars.len();
    let regions_per_var = split_count + 1;
    let total_regions = regions_per_var.pow(n as u32);

    let mut region_conditions = Vec::new();

    for region_index in 0..total_regions {
        let mut cond = builder.bool_lit(true);
        let mut idx = region_index;

        for var_i in 0..n {
            let reg = idx % regions_per_var;
            idx /= regions_per_var;

            let mut pv = program_vars[var_i].clone();
            let cuts = &threshold_vars[var_i];

            if pv.ty.clone().unwrap() != TyKind::Real {
                pv = builder.cast(TyKind::Real, pv.clone())
            }
            let pred = match reg {
                0 => builder.binary(BinOpKind::Lt, Some(TyKind::Bool), pv, cuts[0].clone()),
                r if r == regions_per_var - 1 => builder.binary(
                    BinOpKind::Ge,
                    Some(TyKind::Bool),
                    pv,
                    cuts.last().unwrap().clone(),
                ),
                r => {
                    let ge_prev = builder.binary(
                        BinOpKind::Ge,
                        Some(TyKind::Bool),
                        pv.clone(),
                        cuts[r - 1].clone(),
                    );
                    let lt_next =
                        builder.binary(BinOpKind::Lt, Some(TyKind::Bool), pv, cuts[r].clone());
                    builder.binary(BinOpKind::And, Some(TyKind::Bool), ge_prev, lt_next)
                }
            };

            cond = builder.binary(BinOpKind::And, Some(TyKind::Bool), cond, pred);
        }

        region_conditions.push(cond);
    }

    region_conditions
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
    output_type: &TyKind
) -> (Expr, usize) {
    let mut final_expr: Option<Expr> = None;

    let clamp_with_zero_type = if signed_output_type == TyKind::Int || signed_output_type == TyKind::UInt {
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
            let expr_z3 = translate.t_bool(&both);
            let mut prover = Prover::new(&ctx, IncrementalMode::Native);
            prover.add_assumption(&expr_z3);

            num_sat_checks = num_sat_checks + 1;
            if prover.check_sat() == SatResult::Sat {
                let iverson_both =
                    builder.unary(UnOpKind::Iverson, Some(clamp_with_zero_type.clone()), both);

                // Pass precomputed program_var_decls
                let lc_name = format!("{}_{}", i_idx, s_idx);
                let lc = build_polynomial_combination(
                    lc_name,
                    synth_name,
                    builder,
                    tcx,
                    declare_template_var,
                    program_var_decls,
                    signed_output_type.clone(),
                    output_type,
                    2
                );

                let full =
                    builder.binary(BinOpKind::Mul, Some(clamp_with_zero_type.clone()), iverson_both, lc);

                final_expr = Some(match final_expr {
                    None => full,
                    Some(acc) => {
                        builder.binary(BinOpKind::Add, Some(clamp_with_zero_type.clone()), acc, full)
                    }
                });
            }
        }
    }

    (final_expr.unwrap(), num_sat_checks)
}

pub fn build_template_expression<'smt, 'ctx>(
    synth_name: &Ident,
    synth_val: &uninterpreted::FuncEntry,
    vc_expr: &Expr,
    builder: &mut ExprBuilder,
    tcx: &TyCtx,
    split_count: usize,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    ctx: &'ctx z3::Context,
) -> (Expr, Vec<Ident>, usize, usize) {
    let mut output_type = TyKind::EUReal;
    if let Some(DeclKind::FuncDecl(func_ref)) = tcx.get(*synth_name).as_deref() {
        output_type = func_ref.borrow().output.clone();
    }

    // let signed_output_type = if output_type == TyKind::UInt {
    //     TyKind::Int
    // } else {
    //     TyKind::Real
    // };
    let signed_output_type = output_type.clone();

    // Storage for all newly created template parameter identifiers
    let mut template_idents: Vec<Ident> = Vec::new();
    let mut num_sat_checks = 0;

    let mut program_var_decls = Vec::new();
    let mut program_vars = Vec::new();
    let mut program_vars_no_cast = Vec::new();

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
            println!("Created pvar {} of type {:?}", casted, casted.ty);
            program_var_decls.push(vardecl);
            program_vars.push(casted);
            program_vars_no_cast.push(raw);
        }
    }

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
        template_idents.push(decl.name);
        decl
    };

    let mut bool_exprs: Vec<Shared<ExprData>> = [].into();
    // Step 1: Collect Boolean conditions relevant to the inputs
    if split_count >= 1 {
        bool_exprs = collect_relevant_bool_conditions(synth_val, vc_expr);
    }

    if bool_exprs.is_empty() {
        bool_exprs.push(builder.bool_lit(true));
    }

    // Step 2: Build all split predicates
    let ranged_vars: Vec<(Expr, Range)> = program_var_decls
        .iter()
        .filter_map(|v| {
            v.range
                .as_ref()
                .map(|r| (builder.var(v.name, tcx), r.clone()))
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
    let (mut final_expr, temp_sat_checks) = assemble_piecewise_expression(
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
        &output_type
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
