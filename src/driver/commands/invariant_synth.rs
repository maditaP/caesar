use std::{ops::DerefMut, process::ExitCode, sync::Arc};

use crate::ast::util::{FreeVariableCollector, remove_casts};
use crate::ast::visit::VisitorMut;
use crate::ast::{Direction, Ident};
use crate::invariant_synthesis::inv_synth_helpers::{
    canonical_form, create_subst_mapping, get_functions_from_source_unit,
    get_model_for_constraints, subst_from_mapping, FunctionInliner, InsertAssumeBeforeCalls,
};
use crate::invariant_synthesis::template_gen::{build_template_expression, get_synth_functions};
use crate::opt::unfolder::Unfolder;
use crate::smt::funcs::axiomatic::AxiomaticFunctionEncoder;
use crate::{
    ast::{BinOpKind, Expr, ExprBuilder, FileId, Span, TyKind},
    driver::{
        commands::{mk_cli_server, print_timings, verify::VerifyCommand},
        core_verify::{lower_core_verify_task, CoreVerifyTask},
        error::{finalize_caesar_result, CaesarError},
        front::parse_and_tycheck,
        quant_proof::{lower_quant_prove_task, BoolVcProveTask, QuantVcProveTask},
        smt_proof::{mk_function_encoder, set_global_z3_params, SmtVcProveTask},
    },
    resource_limits::{await_with_resource_limits, LimitsRef},
    servers::{Server, SharedServer},
    smt::{translate_exprs::TranslateExprs, DepConfig, SmtCtx},
};
use indexmap::{IndexMap, IndexSet};
use z3::{Config, Context};
use z3rro::prover::ProveResult;
/// The inner loop of the invariant synthesis procedure.
///
/// This loop refines candidate invariants iteratively through several phases:
///
/// Phase 0:Construct the fully uninstantiated verification condition (VC).
///
/// Phase 1: Check whether the current template variables already result in a valid invariant
/// (Check whether VC, evaluated with the template variables, is valid).
///
/// Phase 2:  
/// - If a counterexample is found in Phase 1, use it to (further) constrain the template variables  
///   and search for a new model that satisfies these constraints.  
/// - Otherwise, if no counterexample is found, the current template instantiation
///   is an admissible invariant!
///
/// Phase 3: Instantiate VC with the model found in Phase 2,
/// and return with this to Phase 1.

pub async fn run_synth_inv(options: VerifyCommand) -> ExitCode {
    let (user_files, server) = match mk_cli_server(&options.input_options) {
        Ok(value) => value,
        Err(value) => return value,
    };
    let options = Arc::new(options);
    let result = synth_inv_files(&options, &server, user_files).await;

    if options.debug_options.timing {
        print_timings();
    }

    finalize_caesar_result(server, &options.rlimit_options, result)
}

/// Synthesize invariants for a list of `user_files`. The `options.files` value is ignored here.
pub async fn synth_inv_files(
    options: &Arc<VerifyCommand>,
    server: &SharedServer,
    user_files: Vec<FileId>,
) -> Result<bool, CaesarError> {
    let handle = |limits_ref: LimitsRef| {
        let options = options.clone();
        let server = server.clone();
        tokio::task::spawn_blocking(move || {
            // execute the verifier with a larger stack size of 50MB. the
            // default stack size might be quite small and we need to do quite a
            // lot of recursion.
            let stack_size = 50 * 1024 * 1024;
            stacker::maybe_grow(stack_size, stack_size, move || {
                let mut server = server.lock().unwrap();
                synth_inv_main(&options, limits_ref, server.deref_mut(), &user_files)
            })
        })
    };
    // Unpacking lots of Results with `.await??` :-)
    await_with_resource_limits(
        Some(options.rlimit_options.timeout()),
        Some(options.rlimit_options.mem_limit()),
        handle,
    )
    .await??
}

use std::time::{Duration, Instant};

/// Synchronously synthesize invariants for the given files.
fn synth_inv_main(
    options: &VerifyCommand,
    limits_ref: LimitsRef,
    server: &mut dyn Server,
    user_files: &[FileId],
) -> Result<bool, CaesarError> {
    let start_total = Instant::now();
    let mut split_count = 1;
    let mut num_proven: usize = 0;
    let mut num_failures: usize = 0;
    let mut total_num_cegis_its = 0;
    const MAX_CEGIS_ITERS: usize = 3000;
    // let max_split_count: usize = options.synth_options.max_template_refinements.unwrap_or(30) + 1;
    let max_split_count = 30;
    let mut template_satchecks = 0;
    let mut duration_template_building = Duration::new(0, 0);

    while split_count <= max_split_count {
        println!("Iteration {split_count}");
        // I have to reset the tcx, how do I do that without parsing new?
        let start_parse = Instant::now();

        let (mut module, mut tcx) = parse_and_tycheck(
            &options.input_options,
            &options.debug_options,
            server,
            user_files,
        )?;
        let duration_parse = start_parse.elapsed(); // Parse time

        if options.synth_options.print_benchmark_info {
            println!("Parse time = {:.2}", duration_parse.as_secs_f64());
        }

        // Register all relevant source units with the server
        module.register_with_server(server)?;

        // Visit every source unit and check possible cases of unsoundness
        // based on the provided calculus annotations
        module.check_calculus_rules(&mut tcx)?;

        // Desugar encodings from source units.
        module.apply_encodings(&mut tcx, server)?;

        if options.debug_options.print_core_procs {
            println!("HeyVL invariant synthesis task with generated procs:");
            println!("{module}");
        }

        // generate dependency graph to determine which declarations are needed for
        // the SMT translation later
        let mut depgraph = module.generate_depgraph(&options.opt_options.function_encoding)?;

        let mut target_funcs: Vec<Ident> = Vec::new();

        // I am DYING over here
        for item in &module.items {
            // get functions from this item
            let mut fn_names = get_functions_from_source_unit(item);

            // append to our vector
            target_funcs.append(&mut fn_names);

            // println!("Functions in this item: {:?}", fn_names);
            // println!("Source unit: {:}", item);
        }

        // let mut synth_inv_units: Vec<Item<CoreVerifyTask>> = module
        //     .items
        //     .into_iter()
        //     .flat_map(|item| {
        //         item.flat_map(|unit| CoreVerifyTask::from_source_unit(unit, &mut depgraph))
        //     })
        //     .collect();

        // set requested global z3 options
        set_global_z3_params(options, &limits_ref);

        // for synth_inv_unit in &mut synth_inv_units {
        for item in module.items {
            let mut visitor = InsertAssumeBeforeCalls {
                func_idents: &target_funcs,
                direction: Direction::Up, // or whatever is appropriate
            };
            //   let mut visitor = InsertAssumeForRanges::new(
            //     Direction::Up, // or whatever is appropriate
            //   );
            let synth_inv_unit = if options.synth_options.only_well_defined {
                item.flat_map(|unit| {
                    CoreVerifyTask::from_source_unit2(unit, &mut depgraph, &mut visitor)
                })
            } else {
                item.flat_map(|unit| CoreVerifyTask::from_source_unit(unit, &mut depgraph))
            };

            let Some(mut synth_inv_unit) = synth_inv_unit else {
                continue;
            };

            // --- Phase 0: Create the completely uninstatiated verification condition ---
            limits_ref.check_limits()?;

            let (name, mut synth_inv_unit) = synth_inv_unit.enter_with_name();

            // Set the current unit as ongoing
            server.set_ongoing_unit(name)?;
            // return Err(CaesarError::Interrupted);

            // Lowering the core synth_inv_unit task to a quantitative prove task: applying
            // spec call desugaring, preparing slicing, and verification condition
            // generation.

            let (mut vc_expr, slice_vars) = lower_core_verify_task(
                &mut tcx,
                name,
                options,
                &limits_ref,
                server,
                &mut synth_inv_unit,
            )?;

            // The constraints are a conjunction of Expressions, so we start with true

            let direction = vc_expr.direction.clone();
            let vcdeps = vc_expr.deps.clone();

            // Lowering the quantitative task to a Boolean one. This contains (lazy)
            // unfolding, and various optimizations
            // (depending on options).
            // TODO: think about quantifier elimination

            let mut builder = ExprBuilder::new(Span::dummy_span());
            let mut constraints = builder.bool_lit(true);

            let mut vc_is_valid =
                lower_quant_prove_task(options, &limits_ref, &tcx, name, vc_expr.clone())?;

            let ctx = Context::new(&z3::Config::default());
            let function_encoder = mk_function_encoder(&tcx, &depgraph, options)?;
            let dep_config = DepConfig::Set(vc_is_valid.get_dependencies());
            let smt_ctx = SmtCtx::new(&ctx, &tcx, function_encoder, dep_config);
            let mut translate = TranslateExprs::new(&smt_ctx);

            let synth = get_synth_functions(smt_ctx.uninterpreteds());

            let mut templates = Vec::new(); // list of templates (one per synth fn)
            let mut all_template_vars = Vec::new();
            if !synth.is_empty() {
                for (synth_name, synth_val) in synth.iter() {
                    let start_template = Instant::now();

                    // Build template for this particular synthesized function
                    let (temp_template, vars, temp_num_guards, temp_num_sat_checks) =
                        build_template_expression(
                            options,
                            synth_name,
                            synth_val,
                            &vc_expr.expr,
                            &mut builder,
                            &tcx,
                            split_count,
                            &mut translate,
                            &ctx,
                            limits_ref.clone(),
                        );
                    template_satchecks = template_satchecks + temp_num_sat_checks;

                    let duration_template = start_template.elapsed();
                    duration_template_building += duration_template;
                    if options.synth_options.print_benchmark_info {
                        println!(
                            "Template building for `{}` took: {:.2}",
                            synth_name,
                            duration_template.as_secs_f64()
                        );
                    }

                    all_template_vars.extend(vars.clone());

                    // Process the template (unfold, neutral removal, etc.)
                    let ctx = Context::new(&Config::default());
                    let dep_config = DepConfig::SpecsOnly;
                    let smt_ctx_local = SmtCtx::new(
                        &ctx,
                        &tcx,
                        Box::new(AxiomaticFunctionEncoder::default()),
                        dep_config,
                    );

                    let mut tpl = temp_template.clone();

                    let mut unfolder = Unfolder::new(limits_ref.clone(), &smt_ctx_local);
                    unfolder.visit_expr(&mut tpl)?;
                    // println!("template for `{}`: {} before neutrals remover", synth_name, remove_casts(&tpl));

                    // let mut neutrals_remover =
                    //     NeutralsRemover::new(limits_ref.clone(), &smt_ctx_local);
                    // neutrals_remover.visit_expr(&mut tpl)?;

                    // println!("template for `{}`: {:?}", synth_name, tpl);
                    if options.synth_options.print_template {
                        println!("template for `{}`: {}", synth_name, remove_casts(&tpl));
                    }

                    // Store the processed template
                    templates.push((synth_name.clone(), tpl, temp_num_guards));
                }

                // Now inline ALL templates into vc_expr
                for (func_ident, template_expr, _num_guards) in templates.iter() {
                    let func_entry = synth
                        .get(func_ident)
                        .expect("synth function disappeared unexpectedly");

                    let mut inliner =
                        FunctionInliner::new(*func_ident, func_entry, template_expr, &tcx);
                    inliner.visit_expr(&mut vc_expr.expr).unwrap();
                }

                // Lower to boolean proof task and unfold
                vc_is_valid =
                    lower_quant_prove_task(options, &limits_ref, &tcx, name, vc_expr.clone())?;
            }

            let template_idents: IndexSet<Ident> =
                all_template_vars.iter().map(|(id, _)| id.clone()).collect();

            // This vc_tvars_pvars is the vc where both tvars and pvars are not instantiated.
            // This will be needed later because it will repeatedly get initiated with new tvars,
            // to check if they are IT
            // let mut vc_tvars_pvars = SmtVcProveTask::translate(vc_is_valid, &mut translate);
            let mut boolean_vc = vc_is_valid;

            if options.debug_options.z3_trace {
                tracing::info!("Z3 tracing output will be written to `z3.log`.");
            }

            let mut iteration = 0;

            // In the first iteration we will use the vc where both tvars and pvars are uninstantiated, but
            // starting from the second loop iteration, the tvars will be instantiated with some value
            let mut bvc_tvars_inst_smttask;
            let mut tvar_mapping: IndexMap<Ident, Expr> = IndexMap::new();

            let mut duration_check = Duration::new(0, 0);
            let mut duration_template_inst = Duration::new(0, 0);
            let time_spent_in_synthesizer = Duration::new(0, 0);
            let mut collector = FreeVariableCollector::new();

            let vc_vars = collector.collect_and_clear(&mut boolean_vc.vc);

            let mut cex_mapping: IndexMap<Ident, Expr>;

            let mut all_cexs: IndexSet<String> = [].into();
            let mut all_zems: IndexSet<String> = [].into();
            loop {
                total_num_cegis_its += 1;
                let start_check = Instant::now(); // Start the timer for template building

                iteration += 1;
                if options.synth_options.print_cegis_info {
                    println!("=== CEGIS loop {iteration} ===");
                }

                //  for (ident, expr) in &tvar_mapping {
                //     if template_idents.contains(ident) {
                //         println!("{} -> {expr}", ident.name);
                //         // print!(" {expr} ");
                //     }
                // }
                // println!("");
                let zero_extended_mapping: IndexMap<Ident, Expr>;
                // Map all template variables to the value to try out.
                // Template variables with no mapping will be mapped to zero
                if true {
                    zero_extended_mapping = all_template_vars
                        .iter()
                        .cloned()
                        .map(|(id, var_type)| {
                            let value = tvar_mapping
                                .get(&id)
                                .cloned()
                                .unwrap_or_else(|| builder.zero_lit(&var_type)); //TODO this needs to be output type... but like this requires a mapping which tempvar belongs to which template
                            (id.clone(), value)
                        })
                        .collect();
                } else {
                    zero_extended_mapping = all_template_vars
                        .iter()
                        .filter_map(|(id, _var_type)| {
                            tvar_mapping
                                .get(id)
                                .cloned()
                                .map(|value| (id.clone(), value))
                        })
                        .collect::<IndexMap<Ident, Expr>>();
                }
                let stringified_map = canonical_form(&zero_extended_mapping);
                if !all_zems.insert(stringified_map.clone()) {
                    return Err(CaesarError::UserError(
                        "Counterexample appeared twice".into(),
                    ));
                }
                // for (ident, expr) in &zero_extended_mapping {
                //     if template_idents.contains(ident) {
                //         println!("{} -> {expr}", ident.name);
                //         // print!(" {expr} ");
                //     }
                // }
                // println!("");
                let bvc_tvars_inst = subst_from_mapping(
                    zero_extended_mapping.clone(),
                    &boolean_vc.vc,
                    &limits_ref.clone(),
                    &smt_ctx,
                )?;

                if options.synth_options.print_cegis_info {
                    for (_synth_name, template_expr, _num_guards) in templates.iter() {
                        let instantiated = subst_from_mapping(
                            zero_extended_mapping.clone(),
                            template_expr,
                            &limits_ref.clone(),
                            &smt_ctx,
                        )?;

                        let mut task = QuantVcProveTask {
                            expr: instantiated,
                            direction,
                            deps: vcdeps.clone(),
                        };

                        task.remove_neutrals(&limits_ref, &tcx)?; // TODO these need to be counted
                                                                  // println!("");
                                                                  // println!("instantiated template");
                                                                  // println!("{} := {}", synth_name, remove_casts(&task.expr));
                                                                  // println!("");
                    }
                }

                // The true distance constraint should be here
                // "Does this verify or is there a counterexample (pvars) with a distance > 2 to the previous pvars "
                // If not try again  without the distance constraint

                // refined_vc.remove_neutrals(&limits_ref, &tcx)?;

                let bvc_tvars_inst_btask = BoolVcProveTask {
                    quant_vc: vc_expr.clone(), // This is a random quant_task and should not!! be used
                    vc: bvc_tvars_inst,
                };

                // println!("checking for validity: {}", bvc_tvars_inst_btask.vc);
                // Translate to SMT form
                bvc_tvars_inst_smttask =
                    SmtVcProveTask::translate(bvc_tvars_inst_btask, &mut translate);

                let result_verifier = bvc_tvars_inst_smttask.clone().no_slice_run_solver(
                    options,
                    &limits_ref,
                    name,
                    &ctx,
                    &mut translate,
                    &slice_vars,
                )?;
                let prove_result_verifier = result_verifier.prove_result;
                duration_check = start_check.elapsed() + duration_check; // Template instantiation time

                match prove_result_verifier {
                    ProveResult::Proof => {
                        num_proven += 1;

                        let mut instantiated_tasks = Vec::new();

                        for (synth_name, template_expr, num_guards) in templates.iter() {
                            let instantiated = subst_from_mapping(
                                zero_extended_mapping.clone(),
                                template_expr,
                                &limits_ref.clone(),
                                &smt_ctx,
                            )?;

                            let mut task = QuantVcProveTask {
                                expr: instantiated,
                                direction,
                                deps: vcdeps.clone(),
                            };

                            task.remove_neutrals(&limits_ref, &tcx)?;

                            instantiated_tasks.push((synth_name.clone(), task));
                            if options.synth_options.print_benchmark_info {
                                println!(
                                    "Number of guard expressions for invariant {synth_name}: {}",
                                    num_guards
                                );
                            }
                        }

                        let duration_inductivity = start_total.elapsed();

                        if options.synth_options.print_benchmark_info {
                            println!("");
                            println!("=== Benchmark info ===");

                            println!(
                                "Total synthesis took: {:.2}",
                                duration_inductivity.as_secs_f64()
                            );
                            println!(
                                "Template building took: {:.2}",
                                duration_template_building.as_secs_f64()
                            );
                            println!(
                                "Verification checks took: {:.2}",
                                duration_check.as_secs_f64()
                            );
                            // println!(
                            //     "Template instantiation took: {:.2}",
                            //     duration_template_inst.as_secs_f64()
                            // );
                            println!(
                                "Time spent in synthesizer: {:.2}",
                                time_spent_in_synthesizer.as_secs_f64()
                            );

                            println!("Number of templates generated: {}", split_count + 1);
                            println!(
                                "Number of counterexamples checked {}",
                                total_num_cegis_its - 1
                            );
                            println!(
                                "Number of sat checks in template building {template_satchecks}"
                            );
                            println!("=======================");
                            println!("");
                        }

                        split_count = max_split_count + 1;
                        println!(
                            "After {iteration} CEGIS loop iterations, the following admissible invariants were found:"
                        );
                        for (name, task) in instantiated_tasks.iter() {
                            println!("  {} := {}", name, remove_casts(&task.expr));
                        }
                        break;
                    }

                    ProveResult::Counterexample => {}
                    ProveResult::Unknown(msg) => {
                        num_failures += 1;
                        println!("Solver returned unknown for {name}: {msg}");
                        break;
                    }
                }

                if iteration >= MAX_CEGIS_ITERS {
                    println!("Reached max num of CEGIS loops ({iteration}) for {name}.");
                    num_failures += 1;
                    break;
                }

                // --- Phase 2: Template-model search ---

                let start_template_instatiate = Instant::now(); // Start the timer for template building

                // Here we add the original vc_tvars_pvars instantiated with the model for the program variables
                // to the constraint we use to find valuations for the template variables.
                if let Some(model) = result_verifier.model {
                    cex_mapping = create_subst_mapping(vc_vars.clone(), &model, &mut translate);

                    if options.synth_options.print_cegis_info {
                        println!("Found counterexample: ");
                        let mut entries: Vec<_> = cex_mapping.iter().collect();
                        entries.sort_by(|(a, _), (b, _)| a.name.cmp(&b.name));

                        for (ident, expr) in entries {
                            // if !template_idents.contains(ident) && vc_vars.contains(ident) {
                            println!("{} -> {expr}", ident.name);
                            // print!(" {expr} ");
                            // }
                        }

                        println!("");
                    }
                    let stringified_map = canonical_form(&cex_mapping);
                    if !all_cexs.insert(stringified_map.clone()) {
                        return Err(CaesarError::UserError(
                            "Counterexample appeared twice".into(),
                        ));
                    }


                    let cex_mapping_only_pvars: IndexMap<Ident, Expr> = cex_mapping
                        .iter()
                        // .filter(|(key, _)| !template_idents.contains(key))
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect();

                    let bvc_pvars_inst = subst_from_mapping(
                        cex_mapping_only_pvars,
                        &boolean_vc.vc,
                        &limits_ref.clone(),
                        &smt_ctx,
                    )?;

                    // Add the new constraint to the constraint-set via conjunction
                    constraints = builder.binary(
                        BinOpKind::And,
                        Some(TyKind::Bool),
                        bvc_pvars_inst,
                        constraints,
                    );

                    // constraints = new_constraint.vc;

                    // Create a Boolean verification task from the constraints
                    let constraints_on_tvars_bool_task = BoolVcProveTask {
                        quant_vc: vc_expr.clone(), // This is a random quant_task and should not!! be used
                        vc: constraints.clone(),
                    };

                    // --- Phase 3: Evaluate template variables in original vc ---

                    if let Some(mapping) = get_model_for_constraints(
                        &ctx,
                        options,
                        &limits_ref,
                        constraints_on_tvars_bool_task,
                        &mut translate,
                        template_idents.clone(),
                    )? {
                        // Update template variable mapping; zero-extension happens at top of loop
                        tvar_mapping = mapping;
                        duration_template_inst += start_template_instatiate.elapsed();

                        continue; // restart CEGIS loop
                    }

                    println!(
    "No template model found (with or without distance); stopping CEGIS loop after iteration {iteration}."
);

                    num_failures += 1;
                    break;
                }
            }

            split_count = split_count + 1;
        }
    }

    if !options.lsp_options.language_server {
        println!();
        println!("Invariants found for {num_proven}, search failed for {num_failures}.");
    }

    Ok(num_failures == 0)
}
