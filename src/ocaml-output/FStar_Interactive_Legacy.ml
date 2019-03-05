open Prims
let (tc_one_file :
  Prims.string Prims.list ->
    FStar_TypeChecker_Env.env ->
      ((Prims.string FStar_Pervasives_Native.option * Prims.string) *
        FStar_TypeChecker_Env.env_t * Prims.string Prims.list))
  =
  fun remaining  ->
    fun env  ->
      let uu____77045 =
        match remaining with
        | intf::impl::remaining1 when
            FStar_Universal.needs_interleaving intf impl ->
            let uu____77090 =
              FStar_Universal.tc_one_file_for_ide env
                (FStar_Pervasives_Native.Some intf) impl
                FStar_Parser_Dep.empty_parsing_data
               in
            (match uu____77090 with
             | (uu____77113,env1) ->
                 (((FStar_Pervasives_Native.Some intf), impl), env1,
                   remaining1))
        | intf_or_impl::remaining1 ->
            let uu____77138 =
              FStar_Universal.tc_one_file_for_ide env
                FStar_Pervasives_Native.None intf_or_impl
                FStar_Parser_Dep.empty_parsing_data
               in
            (match uu____77138 with
             | (uu____77161,env1) ->
                 ((FStar_Pervasives_Native.None, intf_or_impl), env1,
                   remaining1))
        | [] -> failwith "Impossible"  in
      match uu____77045 with
      | ((intf,impl),env1,remaining1) -> ((intf, impl), env1, remaining1)
  
type env_t = FStar_TypeChecker_Env.env
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t * modul_t) Prims.list
let (pop : FStar_TypeChecker_Env.env -> Prims.string -> unit) =
  fun env  ->
    fun msg  ->
      (let uu____77278 = FStar_TypeChecker_Tc.pop_context env msg  in ());
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
            let uu___725_77307 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___725_77307.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___725_77307.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___725_77307.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___725_77307.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___725_77307.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___725_77307.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___725_77307.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___725_77307.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___725_77307.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___725_77307.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___725_77307.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___725_77307.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___725_77307.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___725_77307.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___725_77307.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___725_77307.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___725_77307.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___725_77307.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___725_77307.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___725_77307.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = lax1;
              FStar_TypeChecker_Env.lax_universes =
                (uu___725_77307.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___725_77307.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___725_77307.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___725_77307.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___725_77307.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___725_77307.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___725_77307.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___725_77307.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___725_77307.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___725_77307.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___725_77307.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___725_77307.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___725_77307.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___725_77307.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___725_77307.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___725_77307.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___725_77307.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___725_77307.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___725_77307.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___725_77307.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___725_77307.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___725_77307.FStar_TypeChecker_Env.nbe)
            }  in
          let res = FStar_TypeChecker_Tc.push_context env1 msg  in
          FStar_Options.push ();
          if restore_cmd_line_options1
          then
            (let uu____77312 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____77312 (fun a1  -> ()))
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
          (fun uu___736_77363  ->
             match () with
             | () ->
                 let uu____77375 =
                   FStar_Universal.tc_one_fragment curmod env frag  in
                 (match uu____77375 with
                  | (m,env1) ->
                      let uu____77399 =
                        let uu____77409 = FStar_Errors.get_err_count ()  in
                        (m, env1, uu____77409)  in
                      FStar_Pervasives_Native.Some uu____77399)) ()
        with
        | FStar_Errors.Error (e,msg,r) when
            let uu____77445 = FStar_Options.trace_error ()  in
            Prims.op_Negation uu____77445 ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e,msg) when
            let uu____77476 = FStar_Options.trace_error ()  in
            Prims.op_Negation uu____77476 ->
            ((let uu____77479 =
                let uu____77489 =
                  let uu____77497 = FStar_TypeChecker_Env.get_range env  in
                  (e, msg, uu____77497)  in
                [uu____77489]  in
              FStar_TypeChecker_Err.add_errors env uu____77479);
             FStar_Pervasives_Native.None)
  
let (report_fail : unit -> unit) =
  fun uu____77527  ->
    (let uu____77529 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____77529 (fun a2  -> ()));
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
    match projectee with | Push _0 -> true | uu____77619 -> false
  
let (__proj__Push__item___0 :
  input_chunks -> (Prims.bool * Prims.int * Prims.int)) =
  fun projectee  -> match projectee with | Push _0 -> _0 
let (uu___is_Pop : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____77667 -> false
  
let (__proj__Pop__item___0 : input_chunks -> Prims.string) =
  fun projectee  -> match projectee with | Pop _0 -> _0 
let (uu___is_Code : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____77701 -> false
  
let (__proj__Code__item___0 :
  input_chunks -> (Prims.string * (Prims.string * Prims.string))) =
  fun projectee  -> match projectee with | Code _0 -> _0 
let (uu___is_Info : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Info _0 -> true | uu____77773 -> false
  
let (__proj__Info__item___0 :
  input_chunks ->
    (Prims.string * Prims.bool * (Prims.string * Prims.int * Prims.int)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Info _0 -> _0 
let (uu___is_Completions : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Completions _0 -> true | uu____77851 -> false
  
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
  let uu____78171 = FStar_Util.new_string_builder ()  in
  let uu____78172 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let uu____78179 = FStar_Util.mk_ref []  in
  let uu____78186 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  {
    chunk = uu____78171;
    stdin = uu____78172;
    buffer = uu____78179;
    log = uu____78186
  } 
let rec (read_chunk : unit -> input_chunks) =
  fun uu____78264  ->
    let s = the_interactive_state  in
    let log1 =
      let uu____78272 = FStar_Options.debug_any ()  in
      if uu____78272
      then
        let transcript =
          let uu____78280 = FStar_ST.op_Bang s.log  in
          match uu____78280 with
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
      else (fun uu____78338  -> ())  in
    let stdin =
      let uu____78341 = FStar_ST.op_Bang s.stdin  in
      match uu____78341 with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None  ->
          let i = FStar_Util.open_stdin ()  in
          (FStar_ST.op_Colon_Equals s.stdin (FStar_Pervasives_Native.Some i);
           i)
       in
    let line =
      let uu____78395 = FStar_Util.read_line stdin  in
      match uu____78395 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some l -> l  in
    log1 line;
    (let l = FStar_Util.trim_string line  in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____78425::ok::fail1::[] -> (ok, fail1)
         | uu____78437 -> ("ok", "fail")  in
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
               let uu____78467 =
                 FStar_Util.substring_from l (FStar_String.length "#push")
                  in
               FStar_Util.trim_string uu____78467  in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu____78499 = FStar_Util.int_of_string l1  in
                   let uu____78501 = FStar_Util.int_of_string c  in
                   (true, uu____78499, uu____78501)
               | l1::c::[] ->
                   let uu____78514 = FStar_Util.int_of_string l1  in
                   let uu____78516 = FStar_Util.int_of_string c  in
                   (false, uu____78514, uu____78516)
               | uu____78522 ->
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
              | uu____78540::symbol::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   Info (symbol, true, FStar_Pervasives_Native.None))
              | uu____78571::symbol::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   (let uu____78588 =
                      let uu____78608 =
                        let uu____78620 =
                          let uu____78630 = FStar_Util.int_of_string row  in
                          let uu____78632 = FStar_Util.int_of_string col  in
                          (file, uu____78630, uu____78632)  in
                        FStar_Pervasives_Native.Some uu____78620  in
                      (symbol, false, uu____78608)  in
                    Info uu____78588))
              | uu____78660 ->
                  (FStar_Errors.log_issue FStar_Range.dummyRange
                     (FStar_Errors.Error_IDEUnrecognized,
                       (Prims.op_Hat "Unrecognized \"#info\" request: " l));
                   FStar_All.exit (Prims.parse_int "1")))
           else
             if FStar_Util.starts_with l "#completions "
             then
               (match FStar_Util.split l " " with
                | uu____78673::prefix1::"#"::[] ->
                    (FStar_Util.clear_string_builder s.chunk;
                     Completions prefix1)
                | uu____78683 ->
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
  fun uu____78707  ->
    let s = the_interactive_state  in
    let uu____78709 = FStar_ST.op_Bang s.buffer  in
    match uu____78709 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.op_Colon_Equals s.buffer chunks; chunk)
  
let (fill_buffer : unit -> unit) =
  fun uu____78768  ->
    let s = the_interactive_state  in
    let uu____78770 =
      let uu____78773 = FStar_ST.op_Bang s.buffer  in
      let uu____78799 = let uu____78802 = read_chunk ()  in [uu____78802]  in
      FStar_List.append uu____78773 uu____78799  in
    FStar_ST.op_Colon_Equals s.buffer uu____78770
  
let (deps_of_our_file :
  Prims.string ->
    (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option *
      FStar_Parser_Dep.deps))
  =
  fun filename  ->
    let uu____78846 =
      FStar_Dependencies.find_deps_if_needed [filename]
        FStar_Universal.load_parsing_data_from_cache
       in
    match uu____78846 with
    | (deps,dep_graph1) ->
        let uu____78876 =
          FStar_List.partition
            (fun x  ->
               let uu____78893 = FStar_Parser_Dep.lowercase_module_name x  in
               let uu____78895 =
                 FStar_Parser_Dep.lowercase_module_name filename  in
               uu____78893 <> uu____78895) deps
           in
        (match uu____78876 with
         | (deps1,same_name) ->
             let maybe_intf =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____78939 =
                       (let uu____78943 = FStar_Parser_Dep.is_interface intf
                           in
                        Prims.op_Negation uu____78943) ||
                         (let uu____78946 =
                            FStar_Parser_Dep.is_implementation impl  in
                          Prims.op_Negation uu____78946)
                        in
                     if uu____78939
                     then
                       let uu____78949 =
                         let uu____78955 =
                           FStar_Util.format2
                             "Found %s and %s but not an interface + implementation"
                             intf impl
                            in
                         (FStar_Errors.Warning_MissingInterfaceOrImplementation,
                           uu____78955)
                          in
                       FStar_Errors.log_issue FStar_Range.dummyRange
                         uu____78949
                     else ());
                    FStar_Pervasives_Native.Some intf)
               | impl::[] -> FStar_Pervasives_Native.None
               | uu____78967 ->
                   ((let uu____78972 =
                       let uu____78978 =
                         FStar_Util.format1 "Unexpected: ended up with %s"
                           (FStar_String.concat " " same_name)
                          in
                       (FStar_Errors.Warning_UnexpectedFile, uu____78978)  in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____78972);
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
            | uu____79051 ->
                let stack1 = (env, m) :: stack  in
                let env1 =
                  let uu____79067 = FStar_Options.lax ()  in
                  push_with_kind env uu____79067 true "typecheck_modul"  in
                let uu____79071 = tc_one_file remaining env1  in
                (match uu____79071 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____79121 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____79136 =
                               FStar_Parser_ParseIt.get_file_last_modification_time
                                 intf1
                                in
                             FStar_Pervasives_Native.Some uu____79136
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                          in
                       let impl_t =
                         FStar_Parser_ParseIt.get_file_last_modification_time
                           impl
                          in
                       (intf_t, impl_t)  in
                     (match uu____79121 with
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
                 | (uu____79275,uu____79276) ->
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
                     | uu____79424 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____79477 -> (false, depnames1))
                 in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____79560::ts3 ->
                    (pop env1 "";
                     (let uu____79608 =
                        let uu____79623 = FStar_List.hd stack  in
                        let uu____79632 = FStar_List.tl stack  in
                        (uu____79623, uu____79632)  in
                      match uu____79608 with
                      | ((env2,uu____79654),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3))
                 in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____79724 = ts_elt  in
                  (match uu____79724 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____79761 = match_dep depnames intf impl  in
                       (match uu____79761 with
                        | (b,depnames') ->
                            let uu____79786 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t)
                               in
                            if uu____79786
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1
                                 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____79806 =
                                 let uu____79815 = FStar_List.hd st  in
                                 let uu____79824 = FStar_List.tl st  in
                                 (uu____79815, uu____79824)  in
                               match uu____79806 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts  in
            let uu____79881 = deps_of_our_file filename  in
            match uu____79881 with
            | (filenames,uu____79901,dep_graph1) ->
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
            let uu____80004 = FStar_Range.string_of_range range  in
            let uu____80006 =
              FStar_TypeChecker_Normalize.term_to_string env typ  in
            let uu____80008 =
              match doc1 with
              | FStar_Pervasives_Native.Some docstring ->
                  FStar_Util.format1 "#doc %s" docstring
              | FStar_Pervasives_Native.None  -> ""  in
            FStar_Util.format4 "(defined at %s) %s: %s%s" uu____80004 name
              uu____80006 uu____80008
  
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
              let uu____80063 = shift_chunk ()  in
              match uu____80063 with
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
                    | FStar_Pervasives_Native.Some uu____80185 ->
                        info_at_pos_opt
                    | FStar_Pervasives_Native.None  ->
                        if symbol = ""
                        then FStar_Pervasives_Native.None
                        else
                          (let lid =
                             let uu____80249 =
                               FStar_List.map FStar_Ident.id_of_text
                                 (FStar_Util.split symbol ".")
                                in
                             FStar_Ident.lid_of_ids uu____80249  in
                           let lid1 =
                             if fqn_only
                             then lid
                             else
                               (let uu____80258 =
                                  FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid
                                   in
                                match uu____80258 with
                                | FStar_Pervasives_Native.None  -> lid
                                | FStar_Pervasives_Native.Some lid1 -> lid1)
                              in
                           let uu____80262 =
                             FStar_TypeChecker_Env.try_lookup_lid env lid1
                              in
                           FStar_All.pipe_right uu____80262
                             (FStar_Util.map_option
                                (fun uu____80319  ->
                                   match uu____80319 with
                                   | ((uu____80339,typ),r) ->
                                       ((FStar_Util.Inr lid1), typ, r))))
                     in
                  ((match info_opt with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Util.print_string "\n#done-nok\n"
                    | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
                        let uu____80389 =
                          match name_or_lid with
                          | FStar_Util.Inl name ->
                              (name, FStar_Pervasives_Native.None)
                          | FStar_Util.Inr lid ->
                              let uu____80416 = FStar_Ident.string_of_lid lid
                                 in
                              let uu____80418 =
                                let uu____80422 =
                                  FStar_Syntax_DsEnv.try_lookup_doc
                                    env.FStar_TypeChecker_Env.dsenv lid
                                   in
                                FStar_All.pipe_right uu____80422
                                  (FStar_Util.map_option
                                     FStar_Pervasives_Native.fst)
                                 in
                              (uu____80416, uu____80418)
                           in
                        (match uu____80389 with
                         | (name,doc1) ->
                             let uu____80493 =
                               format_info env name typ rng doc1  in
                             FStar_Util.print1 "%s\n#done-ok\n" uu____80493));
                   go line_col filename stack curmod env ts)
              | Completions search_term ->
                  let rec measure_anchored_match search_term1 candidate =
                    match (search_term1, candidate) with
                    | ([],uu____80542) ->
                        FStar_Pervasives_Native.Some
                          ([], (Prims.parse_int "0"))
                    | (uu____80562,[]) -> FStar_Pervasives_Native.None
                    | (hs::ts1,hc::tc1) ->
                        let hc_text = FStar_Ident.text_of_id hc  in
                        if FStar_Util.starts_with hc_text hs
                        then
                          (match ts1 with
                           | [] ->
                               FStar_Pervasives_Native.Some
                                 (candidate, (FStar_String.length hs))
                           | uu____80626 ->
                               let uu____80630 =
                                 measure_anchored_match ts1 tc1  in
                               FStar_All.pipe_right uu____80630
                                 (FStar_Util.map_option
                                    (fun uu____80675  ->
                                       match uu____80675 with
                                       | (matched,len) ->
                                           ((hc :: matched),
                                             (((FStar_String.length hc_text)
                                                 + (Prims.parse_int "1"))
                                                + len)))))
                        else FStar_Pervasives_Native.None
                     in
                  let rec locate_match needle candidate =
                    let uu____80745 = measure_anchored_match needle candidate
                       in
                    match uu____80745 with
                    | FStar_Pervasives_Native.Some (matched,n1) ->
                        FStar_Pervasives_Native.Some ([], matched, n1)
                    | FStar_Pervasives_Native.None  ->
                        (match candidate with
                         | [] -> FStar_Pervasives_Native.None
                         | hc::tc1 ->
                             let uu____80834 = locate_match needle tc1  in
                             FStar_All.pipe_right uu____80834
                               (FStar_Util.map_option
                                  (fun uu____80900  ->
                                     match uu____80900 with
                                     | (prefix1,matched,len) ->
                                         ((hc :: prefix1), matched, len))))
                     in
                  let str_of_ids ids =
                    let uu____80952 =
                      FStar_List.map FStar_Ident.text_of_id ids  in
                    FStar_Util.concat_l "." uu____80952  in
                  let match_lident_against needle lident =
                    locate_match needle
                      (FStar_List.append lident.FStar_Ident.ns
                         [lident.FStar_Ident.ident])
                     in
                  let shorten_namespace uu____81016 =
                    match uu____81016 with
                    | (prefix1,matched,match_len) ->
                        let naked_match =
                          match matched with
                          | uu____81056::[] -> true
                          | uu____81058 -> false  in
                        let uu____81062 =
                          FStar_Syntax_DsEnv.shorten_module_path
                            env.FStar_TypeChecker_Env.dsenv prefix1
                            naked_match
                           in
                        (match uu____81062 with
                         | (stripped_ns,shortened) ->
                             let uu____81093 = str_of_ids shortened  in
                             let uu____81095 = str_of_ids matched  in
                             let uu____81097 = str_of_ids stripped_ns  in
                             (uu____81093, uu____81095, uu____81097,
                               match_len))
                     in
                  let prepare_candidate uu____81129 =
                    match uu____81129 with
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
                                  let uu____81318 = FStar_Ident.ids_of_lid m
                                     in
                                  let uu____81321 = FStar_Ident.id_of_text n1
                                     in
                                  FStar_Ident.lid_of_ns_and_id uu____81318
                                    uu____81321
                                   in
                                let uu____81322 =
                                  FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid
                                   in
                                FStar_Option.map
                                  (fun fqn  ->
                                     let uu____81339 =
                                       let uu____81342 =
                                         FStar_List.map
                                           FStar_Ident.id_of_text orig_ns
                                          in
                                       FStar_List.append uu____81342
                                         [fqn.FStar_Ident.ident]
                                        in
                                     ([], uu____81339, matched_length))
                                  uu____81322
                              else FStar_Pervasives_Native.None))
                       in
                    let case_b_find_matches_in_env uu____81382 =
                      let matches =
                        FStar_List.filter_map (match_lident_against needle)
                          all_lidents_in_env
                         in
                      FStar_All.pipe_right matches
                        (FStar_List.filter
                           (fun uu____81463  ->
                              match uu____81463 with
                              | (ns,id1,uu____81478) ->
                                  let uu____81489 =
                                    let uu____81492 =
                                      FStar_Ident.lid_of_ids id1  in
                                    FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                      env.FStar_TypeChecker_Env.dsenv
                                      uu____81492
                                     in
                                  (match uu____81489 with
                                   | FStar_Pervasives_Native.None  -> false
                                   | FStar_Pervasives_Native.Some l ->
                                       let uu____81496 =
                                         FStar_Ident.lid_of_ids
                                           (FStar_List.append ns id1)
                                          in
                                       FStar_Ident.lid_equals l uu____81496)))
                       in
                    let uu____81497 = FStar_Util.prefix needle  in
                    match uu____81497 with
                    | (ns,id1) ->
                        let matched_ids =
                          match ns with
                          | [] -> case_b_find_matches_in_env ()
                          | uu____81556 ->
                              let l =
                                FStar_Ident.lid_of_path ns
                                  FStar_Range.dummyRange
                                 in
                              let uu____81561 =
                                FStar_Syntax_DsEnv.resolve_module_name
                                  env.FStar_TypeChecker_Env.dsenv l true
                                 in
                              (match uu____81561 with
                               | FStar_Pervasives_Native.None  ->
                                   case_b_find_matches_in_env ()
                               | FStar_Pervasives_Native.Some m ->
                                   case_a_find_transitive_includes ns m id1)
                           in
                        FStar_All.pipe_right matched_ids
                          (FStar_List.map
                             (fun x  ->
                                let uu____81637 = shorten_namespace x  in
                                prepare_candidate uu____81637))
                     in
                  ((let uu____81651 =
                      FStar_Util.sort_with
                        (fun uu____81680  ->
                           fun uu____81681  ->
                             match (uu____81680, uu____81681) with
                             | ((cd1,ns1,uu____81721),(cd2,ns2,uu____81724))
                                 ->
                                 (match FStar_String.compare cd1 cd2 with
                                  | _81756 when
                                      _81756 = (Prims.parse_int "0") ->
                                      FStar_String.compare ns1 ns2
                                  | n1 -> n1)) matches
                       in
                    FStar_List.iter
                      (fun uu____81773  ->
                         match uu____81773 with
                         | (candidate,ns,match_len) ->
                             let uu____81792 =
                               FStar_Util.string_of_int match_len  in
                             FStar_Util.print3 "%s %s %s \n" uu____81792 ns
                               candidate) uu____81651);
                   FStar_Util.print_string "#done-ok\n";
                   go line_col filename stack curmod env ts)
              | Pop msg ->
                  (pop env msg;
                   (let uu____81800 =
                      match stack with
                      | [] ->
                          (FStar_Errors.log_issue FStar_Range.dummyRange
                             (FStar_Errors.Error_IDETooManyPops,
                               "too many pops");
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd1::tl1 -> (hd1, tl1)  in
                    match uu____81800 with
                    | ((env1,curmod1),stack1) ->
                        go line_col filename stack1 curmod1 env1 ts))
              | Push (lax1,l,c) ->
                  let uu____81869 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____81911 =
                        update_deps filename curmod stack env ts  in
                      (true, uu____81911)
                    else (false, (stack, env, ts))  in
                  (match uu____81869 with
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
                   | uu____82034 -> fail2 curmod env)
  
let (interactive_mode : Prims.string -> unit) =
  fun filename  ->
    (let uu____82055 =
       let uu____82057 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____82057  in
     if uu____82055
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen,
           "code-generation is not supported in interactive mode, ignoring the codegen flag")
     else ());
    (let uu____82065 = deps_of_our_file filename  in
     match uu____82065 with
     | (filenames,maybe_intf,dep_graph1) ->
         let env = FStar_Universal.init_env dep_graph1  in
         let uu____82094 =
           tc_deps FStar_Pervasives_Native.None [] env filenames []  in
         (match uu____82094 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____82123 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0")
                   in
                let uu____82126 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range "<input>" uu____82123 uu____82126  in
              let env2 = FStar_TypeChecker_Env.set_range env1 initial_range
                 in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2  in
              let uu____82136 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ())
                 in
              if uu____82136
              then
                let uu____82139 =
                  let uu____82141 = FStar_Options.file_list ()  in
                  FStar_List.hd uu____82141  in
                FStar_SMTEncoding_Solver.with_hints_db uu____82139
                  (fun uu____82147  ->
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack FStar_Pervasives_Native.None env3 ts)
              else
                go ((Prims.parse_int "1"), (Prims.parse_int "0")) filename
                  stack FStar_Pervasives_Native.None env3 ts))
  