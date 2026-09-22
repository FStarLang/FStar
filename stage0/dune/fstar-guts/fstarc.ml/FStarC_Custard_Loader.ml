open Prims
let loaded_memo : unit FStarC_SMap.t= FStarC_SMap.create (Prims.of_int 100)
let loaded (env : FStarC_TypeChecker_Env.env) (m : Prims.string)
  (want_impl : Prims.bool) : Prims.bool=
  let m1 = FStarC_String.lowercase m in
  let key = Prims.strcat (if want_impl then "!" else "?") m1 in
  let uu___ = FStarC_SMap.try_find loaded_memo key in
  match uu___ with
  | FStar_Pervasives_Native.Some () -> true
  | FStar_Pervasives_Native.None ->
      let b =
        FStarC_List.existsb
          (fun md ->
             ((FStarC_String.lowercase
                 (FStarC_Ident.string_of_lid md.FStarC_Syntax_Syntax.name))
                = m1)
               &&
               (Prims.not (want_impl && md.FStarC_Syntax_Syntax.is_interface)))
          (FStarC_TypeChecker_Env.modules env) in
      (if b then FStarC_SMap.add loaded_memo key () else (); b)
let candidate_files (deps : FStarC_Parser_Dep.deps) (m : Prims.string) :
  Prims.string Prims.list=
  let m1 = FStarC_String.lowercase m in
  let uu___ =
    let uu___1 = FStarC_Parser_Dep.implementation_of deps m1 in
    let uu___2 = FStarC_Parser_Dep.interface_of deps m1 in (uu___1, uu___2) in
  match uu___ with
  | (FStar_Pervasives_Native.Some i, FStar_Pervasives_Native.Some j) ->
      [i; j]
  | (FStar_Pervasives_Native.Some i, FStar_Pervasives_Native.None) -> [i]
  | (FStar_Pervasives_Native.None, o) ->
      (match o with
       | FStar_Pervasives_Native.Some j -> [j]
       | FStar_Pervasives_Native.None -> [])
let cache_primed : unit FStarC_SMap.t= FStarC_SMap.create (Prims.of_int 100)
let rec prime_cache (deps : FStarC_Parser_Dep.deps)
  (env : FStarC_TypeChecker_Env.env) (fn : Prims.string) : unit=
  let uu___ = FStarC_SMap.try_find cache_primed fn in
  match uu___ with
  | FStar_Pervasives_Native.Some uu___1 -> ()
  | FStar_Pervasives_Native.None ->
      (FStarC_SMap.add cache_primed fn ();
       (let uu___3 = FStarC_Parser_Dep.deps_of deps fn in
        FStarC_List.iter (prime_cache deps env) uu___3);
       FStarC_Custard_Prof.timed "cachefile"
         (fun uu___3 ->
            let uu___4 = FStarC_CheckedFiles.load_module_from_cache env fn in
            ()))
let iface_only : unit FStarC_SMap.t= FStarC_SMap.create (Prims.of_int 10)
let loaded_files : unit FStarC_SMap.t= FStarC_SMap.create (Prims.of_int 100)
let module_is_loaded (deps : FStarC_Parser_Dep.deps)
  (env : FStarC_TypeChecker_Env.env) (m : Prims.string) : Prims.bool=
  let m' = FStarC_String.lowercase m in
  let want_impl =
    let uu___ =
      let uu___1 = FStarC_Parser_Dep.implementation_of deps m' in
      match uu___1 with
      | FStar_Pervasives_Native.Some v -> true
      | uu___2 -> false in
    if uu___
    then
      let uu___1 = FStarC_SMap.try_find iface_only m' in
      match uu___1 with
      | FStar_Pervasives_Native.None -> true
      | uu___2 -> false
    else false in
  loaded env m want_impl
let loading : unit FStarC_SMap.t= FStarC_SMap.create (Prims.of_int 100)
let rec ensure_loaded (deps : FStarC_Parser_Dep.deps)
  (env : FStarC_TypeChecker_Env.env) (m : Prims.string) :
  FStarC_TypeChecker_Env.env=
  let uu___ = module_is_loaded deps env m in
  if uu___
  then env
  else
    (let uu___1 =
       let uu___2 = FStarC_SMap.try_find loading (FStarC_String.lowercase m) in
       match uu___2 with
       | FStar_Pervasives_Native.Some v -> true
       | uu___3 -> false in
     if uu___1
     then env
     else
       (let rec first_usable fns =
          match fns with
          | [] ->
              FStarC_Errors.raise_error0
                FStarC_Errors_Codes.Error_CustardEntryNotFound ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                (Obj.magic
                   [FStarC_Errors_Msg.text
                      (Prims.strcat "Custard needs module "
                         (Prims.strcat m
                            ", but no usable checked file for it is in the dependency graph."));
                   FStarC_Errors_Msg.text
                     "Verify the module first, or pass --already_cached appropriately."])
          | fn::fns1 ->
              (prime_cache deps env fn;
               (let uu___3 =
                  FStarC_Custard_Prof.timed "cachefile"
                    (fun uu___4 ->
                       FStarC_CheckedFiles.load_module_from_cache env fn) in
                match uu___3 with
                | FStar_Pervasives_Native.None -> first_usable fns1
                | FStar_Pervasives_Native.Some tcr -> (fn, tcr))) in
        let uu___2 =
          let uu___3 = candidate_files deps m in first_usable uu___3 in
        match uu___2 with
        | (fn, tcr) ->
            (FStarC_SMap.add loaded_files fn ();
             FStarC_SMap.add loading (FStarC_String.lowercase m) ();
             (let env1 =
                let uu___5 = FStarC_Parser_Dep.deps_of deps fn in
                FStarC_List.fold_left
                  (fun env2 dfn ->
                     let dm = FStarC_Parser_Dep.module_name_of_file dfn in
                     if
                       (FStarC_String.lowercase dm) =
                         (FStarC_String.lowercase m)
                     then env2
                     else ensure_loaded deps env2 dm) env uu___5 in
              FStarC_SMap.remove loading (FStarC_String.lowercase m);
              (let uu___7 =
                 let uu___8 = FStarC_Parser_Dep.is_implementation fn in
                 Prims.not uu___8 in
               if uu___7
               then FStarC_SMap.add iface_only (FStarC_String.lowercase m) ()
               else ());
              (let uu___7 =
                 let uu___8 =
                   let uu___9 = FStarC_Parser_Dep.is_implementation fn in
                   Prims.not uu___9 in
                 if uu___8 then loaded env1 m false else false in
               if uu___7
               then env1
               else
                 (let dsenv =
                    let uu___8 =
                      FStarC_List.existsb
                        (fun uu___9 ->
                           match uu___9 with
                           | (l, uu___10) ->
                               (FStarC_String.lowercase
                                  (FStarC_Ident.string_of_lid l))
                                 = (FStarC_String.lowercase m))
                        (FStarC_Syntax_DsEnv.open_modules
                           env1.FStarC_TypeChecker_Env.dsenv) in
                    if uu___8
                    then env1.FStarC_TypeChecker_Env.dsenv
                    else
                      (let uu___9 =
                         let uu___10 =
                           FStarC_ToSyntax_ToSyntax.add_modul_to_env
                             tcr.FStarC_CheckedFiles.checked_module
                             tcr.FStarC_CheckedFiles.mii in
                         uu___10 env1.FStarC_TypeChecker_Env.dsenv in
                       match uu___9 with | (uu___10, dsenv1) -> dsenv1) in
                  let env2 =
                    FStarC_TypeChecker_Tc.load_checked_module
                      {
                        FStarC_TypeChecker_Env.solver =
                          (env1.FStarC_TypeChecker_Env.solver);
                        FStarC_TypeChecker_Env.range =
                          (env1.FStarC_TypeChecker_Env.range);
                        FStarC_TypeChecker_Env.curmodule =
                          (env1.FStarC_TypeChecker_Env.curmodule);
                        FStarC_TypeChecker_Env.gamma =
                          (env1.FStarC_TypeChecker_Env.gamma);
                        FStarC_TypeChecker_Env.gamma_sig =
                          (env1.FStarC_TypeChecker_Env.gamma_sig);
                        FStarC_TypeChecker_Env.gamma_cache =
                          (env1.FStarC_TypeChecker_Env.gamma_cache);
                        FStarC_TypeChecker_Env.modules =
                          (env1.FStarC_TypeChecker_Env.modules);
                        FStarC_TypeChecker_Env.expected_typ =
                          (env1.FStarC_TypeChecker_Env.expected_typ);
                        FStarC_TypeChecker_Env.sigtab =
                          (env1.FStarC_TypeChecker_Env.sigtab);
                        FStarC_TypeChecker_Env.attrtab =
                          (env1.FStarC_TypeChecker_Env.attrtab);
                        FStarC_TypeChecker_Env.instantiate_imp =
                          (env1.FStarC_TypeChecker_Env.instantiate_imp);
                        FStarC_TypeChecker_Env.effects =
                          (env1.FStarC_TypeChecker_Env.effects);
                        FStarC_TypeChecker_Env.generalize =
                          (env1.FStarC_TypeChecker_Env.generalize);
                        FStarC_TypeChecker_Env.letrecs =
                          (env1.FStarC_TypeChecker_Env.letrecs);
                        FStarC_TypeChecker_Env.rec_names =
                          (env1.FStarC_TypeChecker_Env.rec_names);
                        FStarC_TypeChecker_Env.top_level =
                          (env1.FStarC_TypeChecker_Env.top_level);
                        FStarC_TypeChecker_Env.check_uvars =
                          (env1.FStarC_TypeChecker_Env.check_uvars);
                        FStarC_TypeChecker_Env.use_eq_strict =
                          (env1.FStarC_TypeChecker_Env.use_eq_strict);
                        FStarC_TypeChecker_Env.is_iface =
                          (env1.FStarC_TypeChecker_Env.is_iface);
                        FStarC_TypeChecker_Env.admit =
                          (env1.FStarC_TypeChecker_Env.admit);
                        FStarC_TypeChecker_Env.phase1 =
                          (env1.FStarC_TypeChecker_Env.phase1);
                        FStarC_TypeChecker_Env.failhard =
                          (env1.FStarC_TypeChecker_Env.failhard);
                        FStarC_TypeChecker_Env.flychecking =
                          (env1.FStarC_TypeChecker_Env.flychecking);
                        FStarC_TypeChecker_Env.uvar_subtyping =
                          (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                        FStarC_TypeChecker_Env.intactics =
                          (env1.FStarC_TypeChecker_Env.intactics);
                        FStarC_TypeChecker_Env.nocoerce =
                          (env1.FStarC_TypeChecker_Env.nocoerce);
                        FStarC_TypeChecker_Env.tc_term =
                          (env1.FStarC_TypeChecker_Env.tc_term);
                        FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                          (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                        FStarC_TypeChecker_Env.universe_of =
                          (env1.FStarC_TypeChecker_Env.universe_of);
                        FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                          =
                          (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                        FStarC_TypeChecker_Env.teq_nosmt_force =
                          (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                        FStarC_TypeChecker_Env.subtype_nosmt_force =
                          (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                        FStarC_TypeChecker_Env.qtbl_name_and_index =
                          (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                        FStarC_TypeChecker_Env.fv_delta_depths =
                          (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                        FStarC_TypeChecker_Env.proof_ns =
                          (env1.FStarC_TypeChecker_Env.proof_ns);
                        FStarC_TypeChecker_Env.synth_hook =
                          (env1.FStarC_TypeChecker_Env.synth_hook);
                        FStarC_TypeChecker_Env.try_solve_implicits_hook =
                          (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                        FStarC_TypeChecker_Env.splice =
                          (env1.FStarC_TypeChecker_Env.splice);
                        FStarC_TypeChecker_Env.mpreprocess =
                          (env1.FStarC_TypeChecker_Env.mpreprocess);
                        FStarC_TypeChecker_Env.postprocess =
                          (env1.FStarC_TypeChecker_Env.postprocess);
                        FStarC_TypeChecker_Env.identifier_info =
                          (env1.FStarC_TypeChecker_Env.identifier_info);
                        FStarC_TypeChecker_Env.tc_hooks =
                          (env1.FStarC_TypeChecker_Env.tc_hooks);
                        FStarC_TypeChecker_Env.dsenv = dsenv;
                        FStarC_TypeChecker_Env.nbe =
                          (env1.FStarC_TypeChecker_Env.nbe);
                        FStarC_TypeChecker_Env.strict_args_tab =
                          (env1.FStarC_TypeChecker_Env.strict_args_tab);
                        FStarC_TypeChecker_Env.disc_proj_tab =
                          (env1.FStarC_TypeChecker_Env.disc_proj_tab);
                        FStarC_TypeChecker_Env.erasable_types_tab =
                          (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                        FStarC_TypeChecker_Env.enable_defer_to_tac =
                          (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                        FStarC_TypeChecker_Env.unif_allow_ref_guards =
                          (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                        FStarC_TypeChecker_Env.erase_erasable_args =
                          (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                        FStarC_TypeChecker_Env.core_check =
                          (env1.FStarC_TypeChecker_Env.core_check);
                        FStarC_TypeChecker_Env.missing_decl =
                          (env1.FStarC_TypeChecker_Env.missing_decl);
                        FStarC_TypeChecker_Env.iface_todo =
                          (env1.FStarC_TypeChecker_Env.iface_todo);
                        FStarC_TypeChecker_Env.iface_hidden =
                          (env1.FStarC_TypeChecker_Env.iface_hidden);
                        FStarC_TypeChecker_Env.iface_lids =
                          (env1.FStarC_TypeChecker_Env.iface_lids);
                        FStarC_TypeChecker_Env.iface_val_lids =
                          (env1.FStarC_TypeChecker_Env.iface_val_lids)
                      } tcr.FStarC_CheckedFiles.checked_module in
                  if
                    (tcr.FStarC_CheckedFiles.checked_module).FStarC_Syntax_Syntax.is_interface
                  then env2
                  else
                    FStarC_List.fold_left
                      (fun env3 se ->
                         let env4 =
                           FStarC_TypeChecker_Env.push_sigelt_force env3 se in
                         FStarC_List.iter
                           (fun l ->
                              let uu___9 =
                                FStarC_TypeChecker_Env.lookup_sigelt env4 l in
                              ()) (FStarC_Syntax_Util.lids_of_sigelt se);
                         env4) env2
                      (tcr.FStarC_CheckedFiles.checked_module).FStarC_Syntax_Syntax.declarations))))))
let loaded_digests (uu___ : unit) : (Prims.string * Prims.string) Prims.list=
  let uu___1 = FStarC_SMap.keys loaded_files in
  FStarC_List.map
    (fun fn -> let uu___2 = FStarC_Util.digest_of_file fn in (fn, uu___2))
    uu___1
