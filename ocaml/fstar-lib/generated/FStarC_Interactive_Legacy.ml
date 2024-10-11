open Prims
let (tc_one_file :
  Prims.string Prims.list ->
    FStarC_TypeChecker_Env.env ->
      ((Prims.string FStar_Pervasives_Native.option * Prims.string) *
        FStarC_TypeChecker_Env.env_t * Prims.string Prims.list))
  =
  fun remaining ->
    fun env ->
      let uu___ =
        match remaining with
        | intf::impl::remaining1 when
            FStarC_Universal.needs_interleaving intf impl ->
            let uu___1 =
              FStarC_Universal.tc_one_file_for_ide env
                (FStar_Pervasives_Native.Some intf) impl
                FStarC_Parser_Dep.empty_parsing_data in
            (match uu___1 with
             | (uu___2, env1) ->
                 (((FStar_Pervasives_Native.Some intf), impl), env1,
                   remaining1))
        | intf_or_impl::remaining1 ->
            let uu___1 =
              FStarC_Universal.tc_one_file_for_ide env
                FStar_Pervasives_Native.None intf_or_impl
                FStarC_Parser_Dep.empty_parsing_data in
            (match uu___1 with
             | (uu___2, env1) ->
                 ((FStar_Pervasives_Native.None, intf_or_impl), env1,
                   remaining1))
        | [] -> failwith "Impossible" in
      match uu___ with
      | ((intf, impl), env1, remaining1) -> ((intf, impl), env1, remaining1)
type env_t = FStarC_TypeChecker_Env.env
type modul_t = FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t * modul_t) Prims.list
let (pop : FStarC_TypeChecker_Env.env -> Prims.string -> unit) =
  fun env ->
    fun msg ->
      (let uu___1 = FStarC_TypeChecker_Tc.pop_context env msg in ());
      FStarC_Options.pop ()
let (push_with_kind :
  FStarC_TypeChecker_Env.env ->
    Prims.bool -> Prims.bool -> Prims.string -> FStarC_TypeChecker_Env.env)
  =
  fun env ->
    fun lax ->
      fun restore_cmd_line_options ->
        fun msg ->
          let env1 =
            {
              FStarC_TypeChecker_Env.solver =
                (env.FStarC_TypeChecker_Env.solver);
              FStarC_TypeChecker_Env.range =
                (env.FStarC_TypeChecker_Env.range);
              FStarC_TypeChecker_Env.curmodule =
                (env.FStarC_TypeChecker_Env.curmodule);
              FStarC_TypeChecker_Env.gamma =
                (env.FStarC_TypeChecker_Env.gamma);
              FStarC_TypeChecker_Env.gamma_sig =
                (env.FStarC_TypeChecker_Env.gamma_sig);
              FStarC_TypeChecker_Env.gamma_cache =
                (env.FStarC_TypeChecker_Env.gamma_cache);
              FStarC_TypeChecker_Env.modules =
                (env.FStarC_TypeChecker_Env.modules);
              FStarC_TypeChecker_Env.expected_typ =
                (env.FStarC_TypeChecker_Env.expected_typ);
              FStarC_TypeChecker_Env.sigtab =
                (env.FStarC_TypeChecker_Env.sigtab);
              FStarC_TypeChecker_Env.attrtab =
                (env.FStarC_TypeChecker_Env.attrtab);
              FStarC_TypeChecker_Env.instantiate_imp =
                (env.FStarC_TypeChecker_Env.instantiate_imp);
              FStarC_TypeChecker_Env.effects =
                (env.FStarC_TypeChecker_Env.effects);
              FStarC_TypeChecker_Env.generalize =
                (env.FStarC_TypeChecker_Env.generalize);
              FStarC_TypeChecker_Env.letrecs =
                (env.FStarC_TypeChecker_Env.letrecs);
              FStarC_TypeChecker_Env.top_level =
                (env.FStarC_TypeChecker_Env.top_level);
              FStarC_TypeChecker_Env.check_uvars =
                (env.FStarC_TypeChecker_Env.check_uvars);
              FStarC_TypeChecker_Env.use_eq_strict =
                (env.FStarC_TypeChecker_Env.use_eq_strict);
              FStarC_TypeChecker_Env.is_iface =
                (env.FStarC_TypeChecker_Env.is_iface);
              FStarC_TypeChecker_Env.admit = lax;
              FStarC_TypeChecker_Env.lax_universes =
                (env.FStarC_TypeChecker_Env.lax_universes);
              FStarC_TypeChecker_Env.phase1 =
                (env.FStarC_TypeChecker_Env.phase1);
              FStarC_TypeChecker_Env.failhard =
                (env.FStarC_TypeChecker_Env.failhard);
              FStarC_TypeChecker_Env.flychecking =
                (env.FStarC_TypeChecker_Env.flychecking);
              FStarC_TypeChecker_Env.uvar_subtyping =
                (env.FStarC_TypeChecker_Env.uvar_subtyping);
              FStarC_TypeChecker_Env.intactics =
                (env.FStarC_TypeChecker_Env.intactics);
              FStarC_TypeChecker_Env.nocoerce =
                (env.FStarC_TypeChecker_Env.nocoerce);
              FStarC_TypeChecker_Env.tc_term =
                (env.FStarC_TypeChecker_Env.tc_term);
              FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
              FStarC_TypeChecker_Env.universe_of =
                (env.FStarC_TypeChecker_Env.universe_of);
              FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
              FStarC_TypeChecker_Env.teq_nosmt_force =
                (env.FStarC_TypeChecker_Env.teq_nosmt_force);
              FStarC_TypeChecker_Env.subtype_nosmt_force =
                (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
              FStarC_TypeChecker_Env.qtbl_name_and_index =
                (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
              FStarC_TypeChecker_Env.normalized_eff_names =
                (env.FStarC_TypeChecker_Env.normalized_eff_names);
              FStarC_TypeChecker_Env.fv_delta_depths =
                (env.FStarC_TypeChecker_Env.fv_delta_depths);
              FStarC_TypeChecker_Env.proof_ns =
                (env.FStarC_TypeChecker_Env.proof_ns);
              FStarC_TypeChecker_Env.synth_hook =
                (env.FStarC_TypeChecker_Env.synth_hook);
              FStarC_TypeChecker_Env.try_solve_implicits_hook =
                (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
              FStarC_TypeChecker_Env.splice =
                (env.FStarC_TypeChecker_Env.splice);
              FStarC_TypeChecker_Env.mpreprocess =
                (env.FStarC_TypeChecker_Env.mpreprocess);
              FStarC_TypeChecker_Env.postprocess =
                (env.FStarC_TypeChecker_Env.postprocess);
              FStarC_TypeChecker_Env.identifier_info =
                (env.FStarC_TypeChecker_Env.identifier_info);
              FStarC_TypeChecker_Env.tc_hooks =
                (env.FStarC_TypeChecker_Env.tc_hooks);
              FStarC_TypeChecker_Env.dsenv =
                (env.FStarC_TypeChecker_Env.dsenv);
              FStarC_TypeChecker_Env.nbe = (env.FStarC_TypeChecker_Env.nbe);
              FStarC_TypeChecker_Env.strict_args_tab =
                (env.FStarC_TypeChecker_Env.strict_args_tab);
              FStarC_TypeChecker_Env.erasable_types_tab =
                (env.FStarC_TypeChecker_Env.erasable_types_tab);
              FStarC_TypeChecker_Env.enable_defer_to_tac =
                (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
              FStarC_TypeChecker_Env.unif_allow_ref_guards =
                (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
              FStarC_TypeChecker_Env.erase_erasable_args =
                (env.FStarC_TypeChecker_Env.erase_erasable_args);
              FStarC_TypeChecker_Env.core_check =
                (env.FStarC_TypeChecker_Env.core_check);
              FStarC_TypeChecker_Env.missing_decl =
                (env.FStarC_TypeChecker_Env.missing_decl)
            } in
          let res = FStarC_TypeChecker_Tc.push_context env1 msg in
          FStarC_Options.push ();
          if restore_cmd_line_options
          then
            (let uu___2 = FStarC_Options.restore_cmd_line_options false in ())
          else ();
          res
let (check_frag :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
      (FStarC_Parser_ParseIt.input_frag * FStarC_Universal.lang_decls_t) ->
        (FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option *
          FStarC_TypeChecker_Env.env * Prims.int)
          FStar_Pervasives_Native.option)
  =
  fun env ->
    fun curmod ->
      fun frag ->
        try
          (fun uu___ ->
             match () with
             | () ->
                 let uu___1 =
                   FStarC_Universal.tc_one_fragment curmod env
                     (FStar_Pervasives.Inl frag) in
                 (match uu___1 with
                  | (m, env1, uu___2) ->
                      let uu___3 =
                        let uu___4 = FStarC_Errors.get_err_count () in
                        (m, env1, uu___4) in
                      FStar_Pervasives_Native.Some uu___3)) ()
        with
        | FStarC_Errors.Error (e, msg, r, ctx) when
            let uu___1 = FStarC_Options.trace_error () in
            Prims.op_Negation uu___1 ->
            (FStarC_TypeChecker_Err.add_errors env [(e, msg, r, ctx)];
             FStar_Pervasives_Native.None)
let (report_fail : unit -> unit) =
  fun uu___ ->
    (let uu___2 = FStarC_Errors.report_all () in ()); FStarC_Errors.clear ()
type input_chunks =
  | Push of (Prims.bool * Prims.int * Prims.int) 
  | Pop of Prims.string 
  | Code of (Prims.string * (Prims.string * Prims.string)) 
  | Info of (Prims.string * Prims.bool * (Prims.string * Prims.int *
  Prims.int) FStar_Pervasives_Native.option) 
  | Completions of Prims.string 
let (uu___is_Push : input_chunks -> Prims.bool) =
  fun projectee -> match projectee with | Push _0 -> true | uu___ -> false
let (__proj__Push__item___0 :
  input_chunks -> (Prims.bool * Prims.int * Prims.int)) =
  fun projectee -> match projectee with | Push _0 -> _0
let (uu___is_Pop : input_chunks -> Prims.bool) =
  fun projectee -> match projectee with | Pop _0 -> true | uu___ -> false
let (__proj__Pop__item___0 : input_chunks -> Prims.string) =
  fun projectee -> match projectee with | Pop _0 -> _0
let (uu___is_Code : input_chunks -> Prims.bool) =
  fun projectee -> match projectee with | Code _0 -> true | uu___ -> false
let (__proj__Code__item___0 :
  input_chunks -> (Prims.string * (Prims.string * Prims.string))) =
  fun projectee -> match projectee with | Code _0 -> _0
let (uu___is_Info : input_chunks -> Prims.bool) =
  fun projectee -> match projectee with | Info _0 -> true | uu___ -> false
let (__proj__Info__item___0 :
  input_chunks ->
    (Prims.string * Prims.bool * (Prims.string * Prims.int * Prims.int)
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Info _0 -> _0
let (uu___is_Completions : input_chunks -> Prims.bool) =
  fun projectee ->
    match projectee with | Completions _0 -> true | uu___ -> false
let (__proj__Completions__item___0 : input_chunks -> Prims.string) =
  fun projectee -> match projectee with | Completions _0 -> _0
type interactive_state =
  {
  chunk: FStarC_Compiler_Util.string_builder ;
  stdin:
    FStarC_Compiler_Util.stream_reader FStar_Pervasives_Native.option
      FStarC_Compiler_Effect.ref
    ;
  buffer: input_chunks Prims.list FStarC_Compiler_Effect.ref ;
  log:
    FStarC_Compiler_Util.out_channel FStar_Pervasives_Native.option
      FStarC_Compiler_Effect.ref
    }
let (__proj__Mkinteractive_state__item__chunk :
  interactive_state -> FStarC_Compiler_Util.string_builder) =
  fun projectee ->
    match projectee with | { chunk; stdin; buffer; log;_} -> chunk
let (__proj__Mkinteractive_state__item__stdin :
  interactive_state ->
    FStarC_Compiler_Util.stream_reader FStar_Pervasives_Native.option
      FStarC_Compiler_Effect.ref)
  =
  fun projectee ->
    match projectee with | { chunk; stdin; buffer; log;_} -> stdin
let (__proj__Mkinteractive_state__item__buffer :
  interactive_state -> input_chunks Prims.list FStarC_Compiler_Effect.ref) =
  fun projectee ->
    match projectee with | { chunk; stdin; buffer; log;_} -> buffer
let (__proj__Mkinteractive_state__item__log :
  interactive_state ->
    FStarC_Compiler_Util.out_channel FStar_Pervasives_Native.option
      FStarC_Compiler_Effect.ref)
  =
  fun projectee ->
    match projectee with | { chunk; stdin; buffer; log;_} -> log
let (the_interactive_state : interactive_state) =
  let uu___ = FStarC_Compiler_Util.new_string_builder () in
  let uu___1 = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
  let uu___2 = FStarC_Compiler_Util.mk_ref [] in
  let uu___3 = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
  { chunk = uu___; stdin = uu___1; buffer = uu___2; log = uu___3 }
let rec (read_chunk : unit -> input_chunks) =
  fun uu___ ->
    let s = the_interactive_state in
    let log =
      let uu___1 = FStarC_Compiler_Debug.any () in
      if uu___1
      then
        let transcript =
          let uu___2 = FStarC_Compiler_Effect.op_Bang s.log in
          match uu___2 with
          | FStar_Pervasives_Native.Some transcript1 -> transcript1
          | FStar_Pervasives_Native.None ->
              let transcript1 =
                FStarC_Compiler_Util.open_file_for_writing "transcript" in
              (FStarC_Compiler_Effect.op_Colon_Equals s.log
                 (FStar_Pervasives_Native.Some transcript1);
               transcript1) in
        fun line ->
          (FStarC_Compiler_Util.append_to_file transcript line;
           FStarC_Compiler_Util.flush transcript)
      else (fun uu___3 -> ()) in
    let stdin =
      let uu___1 = FStarC_Compiler_Effect.op_Bang s.stdin in
      match uu___1 with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None ->
          let i = FStarC_Compiler_Util.open_stdin () in
          (FStarC_Compiler_Effect.op_Colon_Equals s.stdin
             (FStar_Pervasives_Native.Some i);
           i) in
    let line =
      let uu___1 = FStarC_Compiler_Util.read_line stdin in
      match uu___1 with
      | FStar_Pervasives_Native.None ->
          FStarC_Compiler_Effect.exit Prims.int_zero
      | FStar_Pervasives_Native.Some l -> l in
    log line;
    (let l = FStarC_Compiler_Util.trim_string line in
     if FStarC_Compiler_Util.starts_with l "#end"
     then
       let responses =
         match FStarC_Compiler_Util.split l " " with
         | uu___2::ok::fail::[] -> (ok, fail)
         | uu___2 -> ("ok", "fail") in
       let str = FStarC_Compiler_Util.string_of_string_builder s.chunk in
       (FStarC_Compiler_Util.clear_string_builder s.chunk;
        Code (str, responses))
     else
       if FStarC_Compiler_Util.starts_with l "#pop"
       then (FStarC_Compiler_Util.clear_string_builder s.chunk; Pop l)
       else
         if FStarC_Compiler_Util.starts_with l "#push"
         then
           (FStarC_Compiler_Util.clear_string_builder s.chunk;
            (let lc_lax =
               let uu___5 =
                 FStarC_Compiler_Util.substring_from l
                   (FStarC_Compiler_String.length "#push") in
               FStarC_Compiler_Util.trim_string uu___5 in
             let lc =
               match FStarC_Compiler_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu___5 = FStarC_Compiler_Util.int_of_string l1 in
                   let uu___6 = FStarC_Compiler_Util.int_of_string c in
                   (true, uu___5, uu___6)
               | l1::c::[] ->
                   let uu___5 = FStarC_Compiler_Util.int_of_string l1 in
                   let uu___6 = FStarC_Compiler_Util.int_of_string c in
                   (false, uu___5, uu___6)
               | uu___5 ->
                   (FStarC_Errors.log_issue0
                      FStarC_Errors_Codes.Warning_WrongErrorLocation ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                      (Obj.magic
                         (Prims.strcat
                            "Error locations may be wrong, unrecognized string after #push: "
                            lc_lax));
                    (false, Prims.int_one, Prims.int_zero)) in
             Push lc))
         else
           if FStarC_Compiler_Util.starts_with l "#info "
           then
             (match FStarC_Compiler_Util.split l " " with
              | uu___5::symbol::[] ->
                  (FStarC_Compiler_Util.clear_string_builder s.chunk;
                   Info (symbol, true, FStar_Pervasives_Native.None))
              | uu___5::symbol::file::row::col::[] ->
                  (FStarC_Compiler_Util.clear_string_builder s.chunk;
                   (let uu___7 =
                      let uu___8 =
                        let uu___9 =
                          let uu___10 =
                            FStarC_Compiler_Util.int_of_string row in
                          let uu___11 =
                            FStarC_Compiler_Util.int_of_string col in
                          (file, uu___10, uu___11) in
                        FStar_Pervasives_Native.Some uu___9 in
                      (symbol, false, uu___8) in
                    Info uu___7))
              | uu___5 ->
                  (FStarC_Errors.log_issue0
                     FStarC_Errors_Codes.Error_IDEUnrecognized ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                     (Obj.magic
                        (Prims.strcat "Unrecognized \"#info\" request: " l));
                   FStarC_Compiler_Effect.exit Prims.int_one))
           else
             if FStarC_Compiler_Util.starts_with l "#completions "
             then
               (match FStarC_Compiler_Util.split l " " with
                | uu___6::prefix::"#"::[] ->
                    (FStarC_Compiler_Util.clear_string_builder s.chunk;
                     Completions prefix)
                | uu___6 ->
                    (FStarC_Errors.log_issue0
                       FStarC_Errors_Codes.Error_IDEUnrecognized ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                       (Obj.magic
                          (Prims.strcat
                             "Unrecognized \"#completions\" request: " l));
                     FStarC_Compiler_Effect.exit Prims.int_one))
             else
               if l = "#finish"
               then FStarC_Compiler_Effect.exit Prims.int_zero
               else
                 (FStarC_Compiler_Util.string_builder_append s.chunk line;
                  FStarC_Compiler_Util.string_builder_append s.chunk "\n";
                  read_chunk ()))
let (shift_chunk : unit -> input_chunks) =
  fun uu___ ->
    let s = the_interactive_state in
    let uu___1 = FStarC_Compiler_Effect.op_Bang s.buffer in
    match uu___1 with
    | [] -> read_chunk ()
    | chunk::chunks ->
        (FStarC_Compiler_Effect.op_Colon_Equals s.buffer chunks; chunk)
let (fill_buffer : unit -> unit) =
  fun uu___ ->
    let s = the_interactive_state in
    let uu___1 =
      let uu___2 = FStarC_Compiler_Effect.op_Bang s.buffer in
      let uu___3 = let uu___4 = read_chunk () in [uu___4] in
      FStarC_Compiler_List.op_At uu___2 uu___3 in
    FStarC_Compiler_Effect.op_Colon_Equals s.buffer uu___1
let (deps_of_our_file :
  Prims.string ->
    (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option *
      FStarC_Parser_Dep.deps))
  =
  fun filename ->
    let uu___ =
      FStarC_Dependencies.find_deps_if_needed [filename]
        FStarC_CheckedFiles.load_parsing_data_from_cache in
    match uu___ with
    | (deps, dep_graph) ->
        let uu___1 =
          FStarC_Compiler_List.partition
            (fun x ->
               let uu___2 = FStarC_Parser_Dep.lowercase_module_name x in
               let uu___3 = FStarC_Parser_Dep.lowercase_module_name filename in
               uu___2 <> uu___3) deps in
        (match uu___1 with
         | (deps1, same_name) ->
             let maybe_intf =
               match same_name with
               | intf::impl::[] ->
                   ((let uu___3 =
                       (let uu___4 = FStarC_Parser_Dep.is_interface intf in
                        Prims.op_Negation uu___4) ||
                         (let uu___4 =
                            FStarC_Parser_Dep.is_implementation impl in
                          Prims.op_Negation uu___4) in
                     if uu___3
                     then
                       let uu___4 =
                         FStarC_Compiler_Util.format2
                           "Found %s and %s but not an interface + implementation"
                           intf impl in
                       FStarC_Errors.log_issue0
                         FStarC_Errors_Codes.Warning_MissingInterfaceOrImplementation
                         ()
                         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                         (Obj.magic uu___4)
                     else ());
                    FStar_Pervasives_Native.Some intf)
               | impl::[] -> FStar_Pervasives_Native.None
               | uu___2 ->
                   ((let uu___4 =
                       FStarC_Compiler_Util.format1
                         "Unexpected: ended up with %s"
                         (FStarC_Compiler_String.concat " " same_name) in
                     FStarC_Errors.log_issue0
                       FStarC_Errors_Codes.Warning_UnexpectedFile ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                       (Obj.magic uu___4));
                    FStar_Pervasives_Native.None) in
             (deps1, maybe_intf, dep_graph))
type m_timestamps =
  (Prims.string FStar_Pervasives_Native.option * Prims.string *
    FStarC_Compiler_Util.time FStar_Pervasives_Native.option *
    FStarC_Compiler_Util.time) Prims.list
let rec (tc_deps :
  modul_t ->
    stack_t ->
      FStarC_TypeChecker_Env.env ->
        Prims.string Prims.list ->
          m_timestamps ->
            (stack_t * FStarC_TypeChecker_Env.env * m_timestamps))
  =
  fun m ->
    fun stack ->
      fun env ->
        fun remaining ->
          fun ts ->
            match remaining with
            | [] -> (stack, env, ts)
            | uu___ ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu___1 = FStarC_Options.lax () in
                  push_with_kind env uu___1 true "typecheck_modul" in
                let uu___1 = tc_one_file remaining env1 in
                (match uu___1 with
                 | ((intf, impl), env2, remaining1) ->
                     let uu___2 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu___3 =
                               FStarC_Parser_ParseIt.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu___3
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStarC_Parser_ParseIt.get_file_last_modification_time
                           impl in
                       (intf_t, impl_t) in
                     (match uu___2 with
                      | (intf_t, impl_t) ->
                          tc_deps m stack1 env2 remaining1
                            ((intf, impl, intf_t, impl_t) :: ts)))
let (update_deps :
  Prims.string ->
    modul_t ->
      stack_t -> env_t -> m_timestamps -> (stack_t * env_t * m_timestamps))
  =
  fun filename ->
    fun m ->
      fun stk ->
        fun env ->
          fun ts ->
            let is_stale intf impl intf_t impl_t =
              let impl_mt =
                FStarC_Parser_ParseIt.get_file_last_modification_time impl in
              (FStarC_Compiler_Util.is_before impl_t impl_mt) ||
                (match (intf, intf_t) with
                 | (FStar_Pervasives_Native.Some intf1,
                    FStar_Pervasives_Native.Some intf_t1) ->
                     let intf_mt =
                       FStarC_Parser_ParseIt.get_file_last_modification_time
                         intf1 in
                     FStarC_Compiler_Util.is_before intf_t1 intf_mt
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None) -> false
                 | (uu___, uu___1) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None") in
            let rec iterate depnames st env' ts1 good_stack good_ts =
              let match_dep depnames1 intf impl =
                match intf with
                | FStar_Pervasives_Native.None ->
                    (match depnames1 with
                     | dep::depnames' ->
                         if dep = impl
                         then (true, depnames')
                         else (false, depnames1)
                     | uu___ -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep::depnames' ->
                         if (depintf = intf1) && (dep = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu___ -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu___::ts3 ->
                    (pop env1 "";
                     (let uu___2 =
                        let uu___3 = FStarC_Compiler_List.hd stack in
                        let uu___4 = FStarC_Compiler_List.tl stack in
                        (uu___3, uu___4) in
                      match uu___2 with
                      | ((env2, uu___3), stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu___ = ts_elt in
                  (match uu___ with
                   | (intf, impl, intf_t, impl_t) ->
                       let uu___1 = match_dep depnames intf impl in
                       (match uu___1 with
                        | (b, depnames') ->
                            let uu___2 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu___2
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStarC_Compiler_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu___4 =
                                 let uu___5 = FStarC_Compiler_List.hd st in
                                 let uu___6 = FStarC_Compiler_List.tl st in
                                 (uu___5, uu___6) in
                               match uu___4 with
                               | (stack_elt, st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu___ = deps_of_our_file filename in
            match uu___ with
            | (filenames, uu___1, dep_graph) ->
                iterate filenames (FStarC_Compiler_List.rev_append stk [])
                  env (FStarC_Compiler_List.rev_append ts []) [] []
let (format_info :
  FStarC_TypeChecker_Env.env ->
    Prims.string ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Compiler_Range_Type.range ->
          Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun env ->
    fun name ->
      fun typ ->
        fun range ->
          fun doc ->
            let uu___ = FStarC_Compiler_Range_Ops.string_of_range range in
            let uu___1 = FStarC_TypeChecker_Normalize.term_to_string env typ in
            let uu___2 =
              match doc with
              | FStar_Pervasives_Native.Some docstring ->
                  FStarC_Compiler_Util.format1 "#doc %s" docstring
              | FStar_Pervasives_Native.None -> "" in
            FStarC_Compiler_Util.format4 "(defined at %s) %s: %s%s" uu___
              name uu___1 uu___2
let rec (go :
  (Prims.int * Prims.int) ->
    Prims.string -> stack_t -> modul_t -> env_t -> m_timestamps -> unit)
  =
  fun line_col ->
    fun filename ->
      fun stack ->
        fun curmod ->
          fun env ->
            fun ts ->
              let uu___ = shift_chunk () in
              match uu___ with
              | Info (symbol, fqn_only, pos_opt) ->
                  let info_at_pos_opt =
                    match pos_opt with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (file, row, col) ->
                        FStarC_TypeChecker_Err.info_at_pos env file row col in
                  let info_opt =
                    match info_at_pos_opt with
                    | FStar_Pervasives_Native.Some uu___1 -> info_at_pos_opt
                    | FStar_Pervasives_Native.None ->
                        if symbol = ""
                        then FStar_Pervasives_Native.None
                        else
                          (let lid =
                             let uu___2 =
                               FStarC_Compiler_List.map
                                 FStarC_Ident.id_of_text
                                 (FStarC_Compiler_Util.split symbol ".") in
                             FStarC_Ident.lid_of_ids uu___2 in
                           let lid1 =
                             if fqn_only
                             then lid
                             else
                               (let uu___3 =
                                  FStarC_Syntax_DsEnv.resolve_to_fully_qualified_name
                                    env.FStarC_TypeChecker_Env.dsenv lid in
                                match uu___3 with
                                | FStar_Pervasives_Native.None -> lid
                                | FStar_Pervasives_Native.Some lid2 -> lid2) in
                           let uu___2 =
                             FStarC_TypeChecker_Env.try_lookup_lid env lid1 in
                           FStarC_Compiler_Util.map_option
                             (fun uu___3 ->
                                match uu___3 with
                                | ((uu___4, typ), r) ->
                                    ((FStar_Pervasives.Inr lid1), typ, r))
                             uu___2) in
                  ((match info_opt with
                    | FStar_Pervasives_Native.None ->
                        FStarC_Compiler_Util.print_string "\n#done-nok\n"
                    | FStar_Pervasives_Native.Some (name_or_lid, typ, rng) ->
                        let uu___2 =
                          match name_or_lid with
                          | FStar_Pervasives.Inl name ->
                              (name, FStar_Pervasives_Native.None)
                          | FStar_Pervasives.Inr lid ->
                              let uu___3 = FStarC_Ident.string_of_lid lid in
                              (uu___3, FStar_Pervasives_Native.None) in
                        (match uu___2 with
                         | (name, doc) ->
                             let uu___3 = format_info env name typ rng doc in
                             FStarC_Compiler_Util.print1 "%s\n#done-ok\n"
                               uu___3));
                   go line_col filename stack curmod env ts)
              | Completions search_term ->
                  let rec measure_anchored_match search_term1 candidate =
                    match (search_term1, candidate) with
                    | ([], uu___1) ->
                        FStar_Pervasives_Native.Some ([], Prims.int_zero)
                    | (uu___1, []) -> FStar_Pervasives_Native.None
                    | (hs::ts1, hc::tc) ->
                        let hc_text = FStarC_Ident.string_of_id hc in
                        if FStarC_Compiler_Util.starts_with hc_text hs
                        then
                          (match ts1 with
                           | [] ->
                               FStar_Pervasives_Native.Some
                                 (candidate,
                                   (FStarC_Compiler_String.length hs))
                           | uu___1 ->
                               let uu___2 = measure_anchored_match ts1 tc in
                               FStarC_Compiler_Util.map_option
                                 (fun uu___3 ->
                                    match uu___3 with
                                    | (matched, len) ->
                                        ((hc :: matched),
                                          (((FStarC_Compiler_String.length
                                               hc_text)
                                              + Prims.int_one)
                                             + len))) uu___2)
                        else FStar_Pervasives_Native.None in
                  let rec locate_match needle candidate =
                    let uu___1 = measure_anchored_match needle candidate in
                    match uu___1 with
                    | FStar_Pervasives_Native.Some (matched, n) ->
                        FStar_Pervasives_Native.Some ([], matched, n)
                    | FStar_Pervasives_Native.None ->
                        (match candidate with
                         | [] -> FStar_Pervasives_Native.None
                         | hc::tc ->
                             let uu___2 = locate_match needle tc in
                             FStarC_Compiler_Util.map_option
                               (fun uu___3 ->
                                  match uu___3 with
                                  | (prefix, matched, len) ->
                                      ((hc :: prefix), matched, len)) uu___2) in
                  let str_of_ids ids =
                    let uu___1 =
                      FStarC_Compiler_List.map FStarC_Ident.string_of_id ids in
                    FStarC_Compiler_Util.concat_l "." uu___1 in
                  let match_lident_against needle lident =
                    let uu___1 =
                      let uu___2 = FStarC_Ident.ns_of_lid lident in
                      let uu___3 =
                        let uu___4 = FStarC_Ident.ident_of_lid lident in
                        [uu___4] in
                      FStarC_Compiler_List.op_At uu___2 uu___3 in
                    locate_match needle uu___1 in
                  let shorten_namespace uu___1 =
                    match uu___1 with
                    | (prefix, matched, match_len) ->
                        let naked_match =
                          match matched with
                          | uu___2::[] -> true
                          | uu___2 -> false in
                        let uu___2 =
                          FStarC_Syntax_DsEnv.shorten_module_path
                            env.FStarC_TypeChecker_Env.dsenv prefix
                            naked_match in
                        (match uu___2 with
                         | (stripped_ns, shortened) ->
                             let uu___3 = str_of_ids shortened in
                             let uu___4 = str_of_ids matched in
                             let uu___5 = str_of_ids stripped_ns in
                             (uu___3, uu___4, uu___5, match_len)) in
                  let prepare_candidate uu___1 =
                    match uu___1 with
                    | (prefix, matched, stripped_ns, match_len) ->
                        if prefix = ""
                        then (matched, stripped_ns, match_len)
                        else
                          ((Prims.strcat prefix (Prims.strcat "." matched)),
                            stripped_ns,
                            (((FStarC_Compiler_String.length prefix) +
                                match_len)
                               + Prims.int_one)) in
                  let needle = FStarC_Compiler_Util.split search_term "." in
                  let all_lidents_in_env = FStarC_TypeChecker_Env.lidents env in
                  let matches =
                    let case_a_find_transitive_includes orig_ns m id =
                      let exported_names =
                        FStarC_Syntax_DsEnv.transitive_exported_ids
                          env.FStarC_TypeChecker_Env.dsenv m in
                      let matched_length =
                        FStarC_Compiler_List.fold_left
                          (fun out ->
                             fun s ->
                               ((FStarC_Compiler_String.length s) + out) +
                                 Prims.int_one)
                          (FStarC_Compiler_String.length id) orig_ns in
                      FStarC_Compiler_List.filter_map
                        (fun n ->
                           if FStarC_Compiler_Util.starts_with n id
                           then
                             let lid =
                               let uu___1 = FStarC_Ident.ids_of_lid m in
                               let uu___2 = FStarC_Ident.id_of_text n in
                               FStarC_Ident.lid_of_ns_and_id uu___1 uu___2 in
                             let uu___1 =
                               FStarC_Syntax_DsEnv.resolve_to_fully_qualified_name
                                 env.FStarC_TypeChecker_Env.dsenv lid in
                             FStarC_Compiler_Option.map
                               (fun fqn ->
                                  let uu___2 =
                                    let uu___3 =
                                      FStarC_Compiler_List.map
                                        FStarC_Ident.id_of_text orig_ns in
                                    let uu___4 =
                                      let uu___5 =
                                        FStarC_Ident.ident_of_lid fqn in
                                      [uu___5] in
                                    FStarC_Compiler_List.op_At uu___3 uu___4 in
                                  ([], uu___2, matched_length)) uu___1
                           else FStar_Pervasives_Native.None) exported_names in
                    let case_b_find_matches_in_env uu___1 =
                      let matches1 =
                        FStarC_Compiler_List.filter_map
                          (match_lident_against needle) all_lidents_in_env in
                      FStarC_Compiler_List.filter
                        (fun uu___2 ->
                           match uu___2 with
                           | (ns, id, uu___3) ->
                               let uu___4 =
                                 let uu___5 = FStarC_Ident.lid_of_ids id in
                                 FStarC_Syntax_DsEnv.resolve_to_fully_qualified_name
                                   env.FStarC_TypeChecker_Env.dsenv uu___5 in
                               (match uu___4 with
                                | FStar_Pervasives_Native.None -> false
                                | FStar_Pervasives_Native.Some l ->
                                    let uu___5 =
                                      FStarC_Ident.lid_of_ids
                                        (FStarC_Compiler_List.op_At ns id) in
                                    FStarC_Ident.lid_equals l uu___5))
                        matches1 in
                    let uu___1 = FStarC_Compiler_Util.prefix needle in
                    match uu___1 with
                    | (ns, id) ->
                        let matched_ids =
                          match ns with
                          | [] -> case_b_find_matches_in_env ()
                          | uu___2 ->
                              let l =
                                FStarC_Ident.lid_of_path ns
                                  FStarC_Compiler_Range_Type.dummyRange in
                              let uu___3 =
                                FStarC_Syntax_DsEnv.resolve_module_name
                                  env.FStarC_TypeChecker_Env.dsenv l true in
                              (match uu___3 with
                               | FStar_Pervasives_Native.None ->
                                   case_b_find_matches_in_env ()
                               | FStar_Pervasives_Native.Some m ->
                                   case_a_find_transitive_includes ns m id) in
                        FStarC_Compiler_List.map
                          (fun x ->
                             let uu___2 = shorten_namespace x in
                             prepare_candidate uu___2) matched_ids in
                  ((let uu___2 =
                      FStarC_Compiler_Util.sort_with
                        (fun uu___3 ->
                           fun uu___4 ->
                             match (uu___3, uu___4) with
                             | ((cd1, ns1, uu___5), (cd2, ns2, uu___6)) ->
                                 (match FStarC_Compiler_String.compare cd1
                                          cd2
                                  with
                                  | uu___7 when uu___7 = Prims.int_zero ->
                                      FStarC_Compiler_String.compare ns1 ns2
                                  | n -> n)) matches in
                    FStarC_Compiler_List.iter
                      (fun uu___3 ->
                         match uu___3 with
                         | (candidate, ns, match_len) ->
                             let uu___4 =
                               FStarC_Compiler_Util.string_of_int match_len in
                             FStarC_Compiler_Util.print3 "%s %s %s \n" uu___4
                               ns candidate) uu___2);
                   FStarC_Compiler_Util.print_string "#done-ok\n";
                   go line_col filename stack curmod env ts)
              | Pop msg ->
                  (pop env msg;
                   (let uu___2 =
                      match stack with
                      | [] ->
                          (FStarC_Errors.log_issue0
                             FStarC_Errors_Codes.Error_IDETooManyPops ()
                             (Obj.magic
                                FStarC_Errors_Msg.is_error_message_string)
                             (Obj.magic "Too many pops");
                           FStarC_Compiler_Effect.exit Prims.int_one)
                      | hd::tl -> (hd, tl) in
                    match uu___2 with
                    | ((env1, curmod1), stack1) ->
                        go line_col filename stack1 curmod1 env1 ts))
              | Push (lax, l, c) ->
                  let uu___1 =
                    if
                      (FStarC_Compiler_List.length stack) =
                        (FStarC_Compiler_List.length ts)
                    then
                      let uu___2 = update_deps filename curmod stack env ts in
                      (true, uu___2)
                    else (false, (stack, env, ts)) in
                  (match uu___1 with
                   | (restore_cmd_line_options, (stack1, env1, ts1)) ->
                       let stack2 = (env1, curmod) :: stack1 in
                       let env2 =
                         push_with_kind env1 lax restore_cmd_line_options
                           "#push" in
                       go (l, c) filename stack2 curmod env2 ts1)
              | Code (text, (ok, fail)) ->
                  let fail1 curmod1 tcenv =
                    report_fail ();
                    FStarC_Compiler_Util.print1 "%s\n" fail;
                    go line_col filename stack curmod1 tcenv ts in
                  let frag =
                    {
                      FStarC_Parser_ParseIt.frag_fname = " input";
                      FStarC_Parser_ParseIt.frag_text = text;
                      FStarC_Parser_ParseIt.frag_line =
                        (FStar_Pervasives_Native.fst line_col);
                      FStarC_Parser_ParseIt.frag_col =
                        (FStar_Pervasives_Native.snd line_col)
                    } in
                  let res = check_frag env curmod (frag, []) in
                  (match res with
                   | FStar_Pervasives_Native.Some (curmod1, env1, n_errs) ->
                       if n_errs = Prims.int_zero
                       then
                         (FStarC_Compiler_Util.print1 "\n%s\n" ok;
                          go line_col filename stack curmod1 env1 ts)
                       else fail1 curmod1 env1
                   | uu___1 -> fail1 curmod env)
let (interactive_mode : Prims.string -> unit) =
  fun filename ->
    (let uu___1 =
       let uu___2 = FStarC_Options.codegen () in
       FStarC_Compiler_Option.isSome uu___2 in
     if uu___1
     then
       FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_IDEIgnoreCodeGen
         () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
         (Obj.magic
            "Code-generation is not supported in interactive mode, ignoring the codegen flag")
     else ());
    (let uu___1 = deps_of_our_file filename in
     match uu___1 with
     | (filenames, maybe_intf, dep_graph) ->
         let env = FStarC_Universal.init_env dep_graph in
         let uu___2 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu___2 with
          | (stack, env1, ts) ->
              let initial_range =
                let uu___3 =
                  FStarC_Compiler_Range_Type.mk_pos Prims.int_one
                    Prims.int_zero in
                let uu___4 =
                  FStarC_Compiler_Range_Type.mk_pos Prims.int_one
                    Prims.int_zero in
                FStarC_Compiler_Range_Type.mk_range filename uu___3 uu___4 in
              let env2 = FStarC_TypeChecker_Env.set_range env1 initial_range in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStarC_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None -> env2 in
              let uu___3 =
                (FStarC_Options.record_hints ()) ||
                  (FStarC_Options.use_hints ()) in
              if uu___3
              then
                let uu___4 =
                  let uu___5 = FStarC_Options.file_list () in
                  FStarC_Compiler_List.hd uu___5 in
                FStarC_SMTEncoding_Solver.with_hints_db uu___4
                  (fun uu___5 ->
                     go (Prims.int_one, Prims.int_zero) filename stack
                       FStar_Pervasives_Native.None env3 ts)
              else
                go (Prims.int_one, Prims.int_zero) filename stack
                  FStar_Pervasives_Native.None env3 ts))