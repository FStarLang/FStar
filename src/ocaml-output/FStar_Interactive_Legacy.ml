open Prims
let (tc_one_file :
  Prims.string Prims.list ->
    FStar_TypeChecker_Env.env ->
      ((Prims.string FStar_Pervasives_Native.option * Prims.string) *
        FStar_TypeChecker_Env.env_t * Prims.string Prims.list))
  =
  fun remaining  ->
    fun env  ->
      let uu____72085 =
        match remaining with
        | intf::impl::remaining1 when
            FStar_Universal.needs_interleaving intf impl ->
            let uu____72130 =
              FStar_Universal.tc_one_file_for_ide env
                (FStar_Pervasives_Native.Some intf) impl
                FStar_Parser_Dep.empty_parsing_data
               in
            (match uu____72130 with
             | (uu____72153,env1) ->
                 (((FStar_Pervasives_Native.Some intf), impl), env1,
                   remaining1))
        | intf_or_impl::remaining1 ->
            let uu____72178 =
              FStar_Universal.tc_one_file_for_ide env
                FStar_Pervasives_Native.None intf_or_impl
                FStar_Parser_Dep.empty_parsing_data
               in
            (match uu____72178 with
             | (uu____72201,env1) ->
                 ((FStar_Pervasives_Native.None, intf_or_impl), env1,
                   remaining1))
        | [] -> failwith "Impossible"  in
      match uu____72085 with
      | ((intf,impl),env1,remaining1) -> ((intf, impl), env1, remaining1)
  
type env_t = FStar_TypeChecker_Env.env
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t * modul_t) Prims.list
let (pop : FStar_TypeChecker_Env.env -> Prims.string -> unit) =
  fun env  ->
    fun msg  ->
      (let uu____72318 = FStar_TypeChecker_Tc.pop_context env msg  in ());
      FStar_Options.pop ()
  
let (push_with_kind :
  FStar_TypeChecker_Env.env ->
    Prims.bool -> Prims.bool -> Prims.string -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun lax1  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          let env1 =
            let uu___725_72347 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___725_72347.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___725_72347.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___725_72347.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___725_72347.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___725_72347.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___725_72347.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___725_72347.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___725_72347.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___725_72347.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___725_72347.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___725_72347.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___725_72347.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___725_72347.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___725_72347.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___725_72347.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___725_72347.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___725_72347.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___725_72347.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___725_72347.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___725_72347.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = lax1;
              FStar_TypeChecker_Env.lax_universes =
                (uu___725_72347.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___725_72347.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___725_72347.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___725_72347.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___725_72347.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___725_72347.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___725_72347.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___725_72347.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___725_72347.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___725_72347.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___725_72347.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___725_72347.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___725_72347.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___725_72347.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___725_72347.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___725_72347.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___725_72347.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___725_72347.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___725_72347.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___725_72347.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___725_72347.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___725_72347.FStar_TypeChecker_Env.nbe)
            }  in
          let res = FStar_TypeChecker_Tc.push_context env1 msg  in
          FStar_Options.push ();
          if restore_cmd_line_options1
          then
            (let uu____72352 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____72352 (fun a1  -> ()))
          else ();
          res
  
let (check_frag :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option *
          FStar_TypeChecker_Env.env_t * Prims.int)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun curmod  ->
      fun frag  ->
        try
          (fun uu___736_72403  ->
             match () with
             | () ->
                 let uu____72415 =
                   FStar_Universal.tc_one_fragment curmod env frag  in
                 (match uu____72415 with
                  | (m,env1) ->
                      let uu____72439 =
                        let uu____72449 = FStar_Errors.get_err_count ()  in
                        (m, env1, uu____72449)  in
                      FStar_Pervasives_Native.Some uu____72439)) ()
        with
        | FStar_Errors.Error (e,msg,r) when
            let uu____72485 = FStar_Options.trace_error ()  in
            Prims.op_Negation uu____72485 ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e,msg) when
            let uu____72516 = FStar_Options.trace_error ()  in
            Prims.op_Negation uu____72516 ->
            ((let uu____72519 =
                let uu____72529 =
                  let uu____72537 = FStar_TypeChecker_Env.get_range env  in
                  (e, msg, uu____72537)  in
                [uu____72529]  in
              FStar_TypeChecker_Err.add_errors env uu____72519);
             FStar_Pervasives_Native.None)
  
let (report_fail : unit -> unit) =
  fun uu____72567  ->
    (let uu____72569 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____72569 (fun a2  -> ()));
    FStar_Errors.clear ()
  
type input_chunks =
  | Push of (Prims.bool * Prims.int * Prims.int) 
  | Pop of Prims.string 
  | Code of (Prims.string * (Prims.string * Prims.string)) 
  | Info of (Prims.string * Prims.bool * (Prims.string * Prims.int *
  Prims.int) FStar_Pervasives_Native.option) 
  | Completions of Prims.string 
let (uu___is_Push : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____72659 -> false
  
let (__proj__Push__item___0 :
  input_chunks -> (Prims.bool * Prims.int * Prims.int)) =
  fun projectee  -> match projectee with | Push _0 -> _0 
let (uu___is_Pop : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____72706 -> false
  
let (__proj__Pop__item___0 : input_chunks -> Prims.string) =
  fun projectee  -> match projectee with | Pop _0 -> _0 
let (uu___is_Code : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____72739 -> false
  
let (__proj__Code__item___0 :
  input_chunks -> (Prims.string * (Prims.string * Prims.string))) =
  fun projectee  -> match projectee with | Code _0 -> _0 
let (uu___is_Info : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Info _0 -> true | uu____72810 -> false
  
let (__proj__Info__item___0 :
  input_chunks ->
    (Prims.string * Prims.bool * (Prims.string * Prims.int * Prims.int)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Info _0 -> _0 
let (uu___is_Completions : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Completions _0 -> true | uu____72887 -> false
  
let (__proj__Completions__item___0 : input_chunks -> Prims.string) =
  fun projectee  -> match projectee with | Completions _0 -> _0 
type interactive_state =
  {
  chunk: FStar_Util.string_builder ;
  stdin: FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref ;
  buffer: input_chunks Prims.list FStar_ST.ref ;
  log: FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref }
let (__proj__Mkinteractive_state__item__chunk :
  interactive_state -> FStar_Util.string_builder) =
  fun projectee  ->
    match projectee with | { chunk; stdin; buffer; log = log1;_} -> chunk
  
let (__proj__Mkinteractive_state__item__stdin :
  interactive_state ->
    FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with | { chunk; stdin; buffer; log = log1;_} -> stdin
  
let (__proj__Mkinteractive_state__item__buffer :
  interactive_state -> input_chunks Prims.list FStar_ST.ref) =
  fun projectee  ->
    match projectee with | { chunk; stdin; buffer; log = log1;_} -> buffer
  
let (__proj__Mkinteractive_state__item__log :
  interactive_state ->
    FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with | { chunk; stdin; buffer; log = log1;_} -> log1
  
let (the_interactive_state : interactive_state) =
  let uu____73074 = FStar_Util.new_string_builder ()  in
  let uu____73075 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let uu____73082 = FStar_Util.mk_ref []  in
  let uu____73089 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  {
    chunk = uu____73074;
    stdin = uu____73075;
    buffer = uu____73082;
    log = uu____73089
  } 
let rec (read_chunk : unit -> input_chunks) =
  fun uu____73101  ->
    let s = the_interactive_state  in
    let log1 =
      let uu____73109 = FStar_Options.debug_any ()  in
      if uu____73109
      then
        let transcript =
          let uu____73117 = FStar_ST.op_Bang s.log  in
          match uu____73117 with
          | FStar_Pervasives_Native.Some transcript -> transcript
          | FStar_Pervasives_Native.None  ->
              let transcript = FStar_Util.open_file_for_writing "transcript"
                 in
              (FStar_ST.op_Colon_Equals s.log
                 (FStar_Pervasives_Native.Some transcript);
               transcript)
           in
        fun line  ->
          (FStar_Util.append_to_file transcript line;
           FStar_Util.flush_file transcript)
      else (fun uu____73175  -> ())  in
    let stdin =
      let uu____73178 = FStar_ST.op_Bang s.stdin  in
      match uu____73178 with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None  ->
          let i = FStar_Util.open_stdin ()  in
          (FStar_ST.op_Colon_Equals s.stdin (FStar_Pervasives_Native.Some i);
           i)
       in
    let line =
      let uu____73232 = FStar_Util.read_line stdin  in
      match uu____73232 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some l -> l  in
    log1 line;
    (let l = FStar_Util.trim_string line  in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____73262::ok::fail1::[] -> (ok, fail1)
         | uu____73274 -> ("ok", "fail")  in
       let str = FStar_Util.string_of_string_builder s.chunk  in
       (FStar_Util.clear_string_builder s.chunk; Code (str, responses))
     else
       if FStar_Util.starts_with l "#pop"
       then (FStar_Util.clear_string_builder s.chunk; Pop l)
       else
         if FStar_Util.starts_with l "#push"
         then
           (FStar_Util.clear_string_builder s.chunk;
            (let lc_lax =
               let uu____73304 =
                 FStar_Util.substring_from l (FStar_String.length "#push")
                  in
               FStar_Util.trim_string uu____73304  in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu____73336 = FStar_Util.int_of_string l1  in
                   let uu____73338 = FStar_Util.int_of_string c  in
                   (true, uu____73336, uu____73338)
               | l1::c::[] ->
                   let uu____73351 = FStar_Util.int_of_string l1  in
                   let uu____73353 = FStar_Util.int_of_string c  in
                   (false, uu____73351, uu____73353)
               | uu____73359 ->
                   (FStar_Errors.log_issue FStar_Range.dummyRange
                      (FStar_Errors.Warning_WrongErrorLocation,
                        (Prims.op_Hat
                           "Error locations may be wrong, unrecognized string after #push: "
                           lc_lax));
                    (false, (Prims.parse_int "1"), (Prims.parse_int "0")))
                in
             Push lc))
         else
           if FStar_Util.starts_with l "#info "
           then
             (match FStar_Util.split l " " with
              | uu____73377::symbol::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   Info (symbol, true, FStar_Pervasives_Native.None))
              | uu____73408::symbol::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   (let uu____73425 =
                      let uu____73445 =
                        let uu____73457 =
                          let uu____73467 = FStar_Util.int_of_string row  in
                          let uu____73469 = FStar_Util.int_of_string col  in
                          (file, uu____73467, uu____73469)  in
                        FStar_Pervasives_Native.Some uu____73457  in
                      (symbol, false, uu____73445)  in
                    Info uu____73425))
              | uu____73497 ->
                  (FStar_Errors.log_issue FStar_Range.dummyRange
                     (FStar_Errors.Error_IDEUnrecognized,
                       (Prims.op_Hat "Unrecognized \"#info\" request: " l));
                   FStar_All.exit (Prims.parse_int "1")))
           else
             if FStar_Util.starts_with l "#completions "
             then
               (match FStar_Util.split l " " with
                | uu____73510::prefix1::"#"::[] ->
                    (FStar_Util.clear_string_builder s.chunk;
                     Completions prefix1)
                | uu____73520 ->
                    (FStar_Errors.log_issue FStar_Range.dummyRange
                       (FStar_Errors.Error_IDEUnrecognized,
                         (Prims.op_Hat
                            "Unrecognized \"#completions\" request: " l));
                     FStar_All.exit (Prims.parse_int "1")))
             else
               if l = "#finish"
               then FStar_All.exit (Prims.parse_int "0")
               else
                 (FStar_Util.string_builder_append s.chunk line;
                  FStar_Util.string_builder_append s.chunk "\n";
                  read_chunk ()))
  
let (shift_chunk : unit -> input_chunks) =
  fun uu____73544  ->
    let s = the_interactive_state  in
    let uu____73546 = FStar_ST.op_Bang s.buffer  in
    match uu____73546 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.op_Colon_Equals s.buffer chunks; chunk)
  
let (fill_buffer : unit -> unit) =
  fun uu____73605  ->
    let s = the_interactive_state  in
    let uu____73607 =
      let uu____73610 = FStar_ST.op_Bang s.buffer  in
      let uu____73636 = let uu____73639 = read_chunk ()  in [uu____73639]  in
      FStar_List.append uu____73610 uu____73636  in
    FStar_ST.op_Colon_Equals s.buffer uu____73607
  
let (deps_of_our_file :
  Prims.string ->
    (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option *
      FStar_Parser_Dep.deps))
  =
  fun filename  ->
    let uu____73683 =
      FStar_Dependencies.find_deps_if_needed [filename]
        FStar_CheckedFiles.load_parsing_data_from_cache
       in
    match uu____73683 with
    | (deps,dep_graph1) ->
        let uu____73713 =
          FStar_List.partition
            (fun x  ->
               let uu____73730 = FStar_Parser_Dep.lowercase_module_name x  in
               let uu____73732 =
                 FStar_Parser_Dep.lowercase_module_name filename  in
               uu____73730 <> uu____73732) deps
           in
        (match uu____73713 with
         | (deps1,same_name) ->
             let maybe_intf =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____73776 =
                       (let uu____73780 = FStar_Parser_Dep.is_interface intf
                           in
                        Prims.op_Negation uu____73780) ||
                         (let uu____73783 =
                            FStar_Parser_Dep.is_implementation impl  in
                          Prims.op_Negation uu____73783)
                        in
                     if uu____73776
                     then
                       let uu____73786 =
                         let uu____73792 =
                           FStar_Util.format2
                             "Found %s and %s but not an interface + implementation"
                             intf impl
                            in
                         (FStar_Errors.Warning_MissingInterfaceOrImplementation,
                           uu____73792)
                          in
                       FStar_Errors.log_issue FStar_Range.dummyRange
                         uu____73786
                     else ());
                    FStar_Pervasives_Native.Some intf)
               | impl::[] -> FStar_Pervasives_Native.None
               | uu____73804 ->
                   ((let uu____73809 =
                       let uu____73815 =
                         FStar_Util.format1 "Unexpected: ended up with %s"
                           (FStar_String.concat " " same_name)
                          in
                       (FStar_Errors.Warning_UnexpectedFile, uu____73815)  in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____73809);
                    FStar_Pervasives_Native.None)
                in
             (deps1, maybe_intf, dep_graph1))
  
type m_timestamps =
  (Prims.string FStar_Pervasives_Native.option * Prims.string *
    FStar_Util.time FStar_Pervasives_Native.option * FStar_Util.time)
    Prims.list
let rec (tc_deps :
  modul_t ->
    stack_t ->
      FStar_TypeChecker_Env.env ->
        Prims.string Prims.list ->
          m_timestamps ->
            (stack_t * FStar_TypeChecker_Env.env * m_timestamps))
  =
  fun m  ->
    fun stack  ->
      fun env  ->
        fun remaining  ->
          fun ts  ->
            match remaining with
            | [] -> (stack, env, ts)
            | uu____73888 ->
                let stack1 = (env, m) :: stack  in
                let env1 =
                  let uu____73904 = FStar_Options.lax ()  in
                  push_with_kind env uu____73904 true "typecheck_modul"  in
                let uu____73908 = tc_one_file remaining env1  in
                (match uu____73908 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____73958 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____73973 =
                               FStar_Parser_ParseIt.get_file_last_modification_time
                                 intf1
                                in
                             FStar_Pervasives_Native.Some uu____73973
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                          in
                       let impl_t =
                         FStar_Parser_ParseIt.get_file_last_modification_time
                           impl
                          in
                       (intf_t, impl_t)  in
                     (match uu____73958 with
                      | (intf_t,impl_t) ->
                          tc_deps m stack1 env2 remaining1
                            ((intf, impl, intf_t, impl_t) :: ts)))
  
let (update_deps :
  Prims.string ->
    modul_t ->
      stack_t -> env_t -> m_timestamps -> (stack_t * env_t * m_timestamps))
  =
  fun filename  ->
    fun m  ->
      fun stk  ->
        fun env  ->
          fun ts  ->
            let is_stale intf impl intf_t impl_t =
              let impl_mt =
                FStar_Parser_ParseIt.get_file_last_modification_time impl  in
              (FStar_Util.is_before impl_t impl_mt) ||
                (match (intf, intf_t) with
                 | (FStar_Pervasives_Native.Some
                    intf1,FStar_Pervasives_Native.Some intf_t1) ->
                     let intf_mt =
                       FStar_Parser_ParseIt.get_file_last_modification_time
                         intf1
                        in
                     FStar_Util.is_before intf_t1 intf_mt
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> false
                 | (uu____74112,uu____74113) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None")
               in
            let rec iterate depnames st env' ts1 good_stack good_ts =
              let match_dep depnames1 intf impl =
                match intf with
                | FStar_Pervasives_Native.None  ->
                    (match depnames1 with
                     | dep1::depnames' ->
                         if dep1 = impl
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____74261 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____74314 -> (false, depnames1))
                 in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____74397::ts3 ->
                    (pop env1 "";
                     (let uu____74445 =
                        let uu____74460 = FStar_List.hd stack  in
                        let uu____74469 = FStar_List.tl stack  in
                        (uu____74460, uu____74469)  in
                      match uu____74445 with
                      | ((env2,uu____74491),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3))
                 in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____74561 = ts_elt  in
                  (match uu____74561 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____74598 = match_dep depnames intf impl  in
                       (match uu____74598 with
                        | (b,depnames') ->
                            let uu____74623 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t)
                               in
                            if uu____74623
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1
                                 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____74643 =
                                 let uu____74652 = FStar_List.hd st  in
                                 let uu____74661 = FStar_List.tl st  in
                                 (uu____74652, uu____74661)  in
                               match uu____74643 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts  in
            let uu____74718 = deps_of_our_file filename  in
            match uu____74718 with
            | (filenames,uu____74738,dep_graph1) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
  
let (format_info :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term ->
        FStar_Range.range ->
          Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun env  ->
    fun name  ->
      fun typ  ->
        fun range  ->
          fun doc1  ->
            let uu____74841 = FStar_Range.string_of_range range  in
            let uu____74843 =
              FStar_TypeChecker_Normalize.term_to_string env typ  in
            let uu____74845 =
              match doc1 with
              | FStar_Pervasives_Native.Some docstring ->
                  FStar_Util.format1 "#doc %s" docstring
              | FStar_Pervasives_Native.None  -> ""  in
            FStar_Util.format4 "(defined at %s) %s: %s%s" uu____74841 name
              uu____74843 uu____74845
  
let rec (go :
  (Prims.int * Prims.int) ->
    Prims.string -> stack_t -> modul_t -> env_t -> m_timestamps -> unit)
  =
  fun line_col  ->
    fun filename  ->
      fun stack  ->
        fun curmod  ->
          fun env  ->
            fun ts  ->
              let uu____74900 = shift_chunk ()  in
              match uu____74900 with
              | Info (symbol,fqn_only,pos_opt) ->
                  let info_at_pos_opt =
                    match pos_opt with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (file,row,col) ->
                        FStar_TypeChecker_Err.info_at_pos env file row col
                     in
                  let info_opt =
                    match info_at_pos_opt with
                    | FStar_Pervasives_Native.Some uu____75022 ->
                        info_at_pos_opt
                    | FStar_Pervasives_Native.None  ->
                        if symbol = ""
                        then FStar_Pervasives_Native.None
                        else
                          (let lid =
                             let uu____75086 =
                               FStar_List.map FStar_Ident.id_of_text
                                 (FStar_Util.split symbol ".")
                                in
                             FStar_Ident.lid_of_ids uu____75086  in
                           let lid1 =
                             if fqn_only
                             then lid
                             else
                               (let uu____75095 =
                                  FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid
                                   in
                                match uu____75095 with
                                | FStar_Pervasives_Native.None  -> lid
                                | FStar_Pervasives_Native.Some lid1 -> lid1)
                              in
                           let uu____75099 =
                             FStar_TypeChecker_Env.try_lookup_lid env lid1
                              in
                           FStar_All.pipe_right uu____75099
                             (FStar_Util.map_option
                                (fun uu____75156  ->
                                   match uu____75156 with
                                   | ((uu____75176,typ),r) ->
                                       ((FStar_Util.Inr lid1), typ, r))))
                     in
                  ((match info_opt with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Util.print_string "\n#done-nok\n"
                    | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
                        let uu____75226 =
                          match name_or_lid with
                          | FStar_Util.Inl name ->
                              (name, FStar_Pervasives_Native.None)
                          | FStar_Util.Inr lid ->
                              let uu____75253 = FStar_Ident.string_of_lid lid
                                 in
                              let uu____75255 =
                                let uu____75259 =
                                  FStar_Syntax_DsEnv.try_lookup_doc
                                    env.FStar_TypeChecker_Env.dsenv lid
                                   in
                                FStar_All.pipe_right uu____75259
                                  (FStar_Util.map_option
                                     FStar_Pervasives_Native.fst)
                                 in
                              (uu____75253, uu____75255)
                           in
                        (match uu____75226 with
                         | (name,doc1) ->
                             let uu____75330 =
                               format_info env name typ rng doc1  in
                             FStar_Util.print1 "%s\n#done-ok\n" uu____75330));
                   go line_col filename stack curmod env ts)
              | Completions search_term ->
                  let rec measure_anchored_match search_term1 candidate =
                    match (search_term1, candidate) with
                    | ([],uu____75379) ->
                        FStar_Pervasives_Native.Some
                          ([], (Prims.parse_int "0"))
                    | (uu____75399,[]) -> FStar_Pervasives_Native.None
                    | (hs::ts1,hc::tc1) ->
                        let hc_text = FStar_Ident.text_of_id hc  in
                        if FStar_Util.starts_with hc_text hs
                        then
                          (match ts1 with
                           | [] ->
                               FStar_Pervasives_Native.Some
                                 (candidate, (FStar_String.length hs))
                           | uu____75463 ->
                               let uu____75467 =
                                 measure_anchored_match ts1 tc1  in
                               FStar_All.pipe_right uu____75467
                                 (FStar_Util.map_option
                                    (fun uu____75512  ->
                                       match uu____75512 with
                                       | (matched,len) ->
                                           ((hc :: matched),
                                             (((FStar_String.length hc_text)
                                                 + (Prims.parse_int "1"))
                                                + len)))))
                        else FStar_Pervasives_Native.None
                     in
                  let rec locate_match needle candidate =
                    let uu____75582 = measure_anchored_match needle candidate
                       in
                    match uu____75582 with
                    | FStar_Pervasives_Native.Some (matched,n1) ->
                        FStar_Pervasives_Native.Some ([], matched, n1)
                    | FStar_Pervasives_Native.None  ->
                        (match candidate with
                         | [] -> FStar_Pervasives_Native.None
                         | hc::tc1 ->
                             let uu____75671 = locate_match needle tc1  in
                             FStar_All.pipe_right uu____75671
                               (FStar_Util.map_option
                                  (fun uu____75737  ->
                                     match uu____75737 with
                                     | (prefix1,matched,len) ->
                                         ((hc :: prefix1), matched, len))))
                     in
                  let str_of_ids ids =
                    let uu____75789 =
                      FStar_List.map FStar_Ident.text_of_id ids  in
                    FStar_Util.concat_l "." uu____75789  in
                  let match_lident_against needle lident =
                    locate_match needle
                      (FStar_List.append lident.FStar_Ident.ns
                         [lident.FStar_Ident.ident])
                     in
                  let shorten_namespace uu____75853 =
                    match uu____75853 with
                    | (prefix1,matched,match_len) ->
                        let naked_match =
                          match matched with
                          | uu____75893::[] -> true
                          | uu____75895 -> false  in
                        let uu____75899 =
                          FStar_Syntax_DsEnv.shorten_module_path
                            env.FStar_TypeChecker_Env.dsenv prefix1
                            naked_match
                           in
                        (match uu____75899 with
                         | (stripped_ns,shortened) ->
                             let uu____75930 = str_of_ids shortened  in
                             let uu____75932 = str_of_ids matched  in
                             let uu____75934 = str_of_ids stripped_ns  in
                             (uu____75930, uu____75932, uu____75934,
                               match_len))
                     in
                  let prepare_candidate uu____75966 =
                    match uu____75966 with
                    | (prefix1,matched,stripped_ns,match_len) ->
                        if prefix1 = ""
                        then (matched, stripped_ns, match_len)
                        else
                          ((Prims.op_Hat prefix1 (Prims.op_Hat "." matched)),
                            stripped_ns,
                            (((FStar_String.length prefix1) + match_len) +
                               (Prims.parse_int "1")))
                     in
                  let needle = FStar_Util.split search_term "."  in
                  let all_lidents_in_env = FStar_TypeChecker_Env.lidents env
                     in
                  let matches =
                    let case_a_find_transitive_includes orig_ns m id1 =
                      let exported_names =
                        FStar_Syntax_DsEnv.transitive_exported_ids
                          env.FStar_TypeChecker_Env.dsenv m
                         in
                      let matched_length =
                        FStar_List.fold_left
                          (fun out  ->
                             fun s  ->
                               ((FStar_String.length s) + out) +
                                 (Prims.parse_int "1"))
                          (FStar_String.length id1) orig_ns
                         in
                      FStar_All.pipe_right exported_names
                        (FStar_List.filter_map
                           (fun n1  ->
                              if FStar_Util.starts_with n1 id1
                              then
                                let lid =
                                  let uu____76155 = FStar_Ident.ids_of_lid m
                                     in
                                  let uu____76158 = FStar_Ident.id_of_text n1
                                     in
                                  FStar_Ident.lid_of_ns_and_id uu____76155
                                    uu____76158
                                   in
                                let uu____76159 =
                                  FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid
                                   in
                                FStar_Option.map
                                  (fun fqn  ->
                                     let uu____76176 =
                                       let uu____76179 =
                                         FStar_List.map
                                           FStar_Ident.id_of_text orig_ns
                                          in
                                       FStar_List.append uu____76179
                                         [fqn.FStar_Ident.ident]
                                        in
                                     ([], uu____76176, matched_length))
                                  uu____76159
                              else FStar_Pervasives_Native.None))
                       in
                    let case_b_find_matches_in_env uu____76219 =
                      let matches =
                        FStar_List.filter_map (match_lident_against needle)
                          all_lidents_in_env
                         in
                      FStar_All.pipe_right matches
                        (FStar_List.filter
                           (fun uu____76300  ->
                              match uu____76300 with
                              | (ns,id1,uu____76315) ->
                                  let uu____76326 =
                                    let uu____76329 =
                                      FStar_Ident.lid_of_ids id1  in
                                    FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                      env.FStar_TypeChecker_Env.dsenv
                                      uu____76329
                                     in
                                  (match uu____76326 with
                                   | FStar_Pervasives_Native.None  -> false
                                   | FStar_Pervasives_Native.Some l ->
                                       let uu____76333 =
                                         FStar_Ident.lid_of_ids
                                           (FStar_List.append ns id1)
                                          in
                                       FStar_Ident.lid_equals l uu____76333)))
                       in
                    let uu____76334 = FStar_Util.prefix needle  in
                    match uu____76334 with
                    | (ns,id1) ->
                        let matched_ids =
                          match ns with
                          | [] -> case_b_find_matches_in_env ()
                          | uu____76393 ->
                              let l =
                                FStar_Ident.lid_of_path ns
                                  FStar_Range.dummyRange
                                 in
                              let uu____76398 =
                                FStar_Syntax_DsEnv.resolve_module_name
                                  env.FStar_TypeChecker_Env.dsenv l true
                                 in
                              (match uu____76398 with
                               | FStar_Pervasives_Native.None  ->
                                   case_b_find_matches_in_env ()
                               | FStar_Pervasives_Native.Some m ->
                                   case_a_find_transitive_includes ns m id1)
                           in
                        FStar_All.pipe_right matched_ids
                          (FStar_List.map
                             (fun x  ->
                                let uu____76474 = shorten_namespace x  in
                                prepare_candidate uu____76474))
                     in
                  ((let uu____76488 =
                      FStar_Util.sort_with
                        (fun uu____76517  ->
                           fun uu____76518  ->
                             match (uu____76517, uu____76518) with
                             | ((cd1,ns1,uu____76558),(cd2,ns2,uu____76561))
                                 ->
                                 (match FStar_String.compare cd1 cd2 with
                                  | _76593 when
                                      _76593 = (Prims.parse_int "0") ->
                                      FStar_String.compare ns1 ns2
                                  | n1 -> n1)) matches
                       in
                    FStar_List.iter
                      (fun uu____76610  ->
                         match uu____76610 with
                         | (candidate,ns,match_len) ->
                             let uu____76629 =
                               FStar_Util.string_of_int match_len  in
                             FStar_Util.print3 "%s %s %s \n" uu____76629 ns
                               candidate) uu____76488);
                   FStar_Util.print_string "#done-ok\n";
                   go line_col filename stack curmod env ts)
              | Pop msg ->
                  (pop env msg;
                   (let uu____76637 =
                      match stack with
                      | [] ->
                          (FStar_Errors.log_issue FStar_Range.dummyRange
                             (FStar_Errors.Error_IDETooManyPops,
                               "too many pops");
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd1::tl1 -> (hd1, tl1)  in
                    match uu____76637 with
                    | ((env1,curmod1),stack1) ->
                        go line_col filename stack1 curmod1 env1 ts))
              | Push (lax1,l,c) ->
                  let uu____76706 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____76748 =
                        update_deps filename curmod stack env ts  in
                      (true, uu____76748)
                    else (false, (stack, env, ts))  in
                  (match uu____76706 with
                   | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
                       let stack2 = (env1, curmod) :: stack1  in
                       let env2 =
                         push_with_kind env1 lax1 restore_cmd_line_options1
                           "#push"
                          in
                       go (l, c) filename stack2 curmod env2 ts1)
              | Code (text,(ok,fail1)) ->
                  let fail2 curmod1 tcenv =
                    report_fail ();
                    FStar_Util.print1 "%s\n" fail1;
                    go line_col filename stack curmod1 tcenv ts  in
                  let frag =
                    {
                      FStar_Parser_ParseIt.frag_text = text;
                      FStar_Parser_ParseIt.frag_line =
                        (FStar_Pervasives_Native.fst line_col);
                      FStar_Parser_ParseIt.frag_col =
                        (FStar_Pervasives_Native.snd line_col)
                    }  in
                  let res = check_frag env curmod frag  in
                  (match res with
                   | FStar_Pervasives_Native.Some (curmod1,env1,n_errs) ->
                       if n_errs = (Prims.parse_int "0")
                       then
                         (FStar_Util.print1 "\n%s\n" ok;
                          go line_col filename stack curmod1 env1 ts)
                       else fail2 curmod1 env1
                   | uu____76871 -> fail2 curmod env)
  
let (interactive_mode : Prims.string -> unit) =
  fun filename  ->
    (let uu____76892 =
       let uu____76894 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____76894  in
     if uu____76892
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen,
           "code-generation is not supported in interactive mode, ignoring the codegen flag")
     else ());
    (let uu____76902 = deps_of_our_file filename  in
     match uu____76902 with
     | (filenames,maybe_intf,dep_graph1) ->
         let env = FStar_Universal.init_env dep_graph1  in
         let uu____76931 =
           tc_deps FStar_Pervasives_Native.None [] env filenames []  in
         (match uu____76931 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____76960 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0")
                   in
                let uu____76963 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range "<input>" uu____76960 uu____76963  in
              let env2 = FStar_TypeChecker_Env.set_range env1 initial_range
                 in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2  in
              let uu____76973 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ())
                 in
              if uu____76973
              then
                let uu____76976 =
                  let uu____76978 = FStar_Options.file_list ()  in
                  FStar_List.hd uu____76978  in
                FStar_SMTEncoding_Solver.with_hints_db uu____76976
                  (fun uu____76984  ->
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack FStar_Pervasives_Native.None env3 ts)
              else
                go ((Prims.parse_int "1"), (Prims.parse_int "0")) filename
                  stack FStar_Pervasives_Native.None env3 ts))
  