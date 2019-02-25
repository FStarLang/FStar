open Prims
let (tc_one_file :
  Prims.string Prims.list ->
    FStar_TypeChecker_Env.env ->
      ((Prims.string FStar_Pervasives_Native.option * Prims.string) *
        FStar_TypeChecker_Env.env_t * Prims.string Prims.list))
  =
  fun remaining  ->
    fun env  ->
      let uu____76925 =
        match remaining with
        | intf::impl::remaining1 when
            FStar_Universal.needs_interleaving intf impl ->
            let uu____76970 =
              FStar_Universal.tc_one_file_for_ide env
                (FStar_Pervasives_Native.Some intf) impl
                FStar_Parser_Dep.empty_parsing_data
               in
            (match uu____76970 with
             | (uu____76993,env1) ->
                 (((FStar_Pervasives_Native.Some intf), impl), env1,
                   remaining1))
        | intf_or_impl::remaining1 ->
            let uu____77018 =
              FStar_Universal.tc_one_file_for_ide env
                FStar_Pervasives_Native.None intf_or_impl
                FStar_Parser_Dep.empty_parsing_data
               in
            (match uu____77018 with
             | (uu____77041,env1) ->
                 ((FStar_Pervasives_Native.None, intf_or_impl), env1,
                   remaining1))
        | [] -> failwith "Impossible"  in
      match uu____76925 with
      | ((intf,impl),env1,remaining1) -> ((intf, impl), env1, remaining1)
  
type env_t = FStar_TypeChecker_Env.env
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t * modul_t) Prims.list
let (pop : FStar_TypeChecker_Env.env -> Prims.string -> unit) =
  fun env  ->
    fun msg  ->
      (let uu____77158 = FStar_TypeChecker_Tc.pop_context env msg  in ());
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
            let uu___725_77187 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___725_77187.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___725_77187.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___725_77187.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___725_77187.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___725_77187.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___725_77187.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___725_77187.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___725_77187.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___725_77187.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___725_77187.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___725_77187.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___725_77187.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___725_77187.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___725_77187.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___725_77187.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___725_77187.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___725_77187.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___725_77187.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___725_77187.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___725_77187.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = lax1;
              FStar_TypeChecker_Env.lax_universes =
                (uu___725_77187.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___725_77187.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___725_77187.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___725_77187.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___725_77187.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___725_77187.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___725_77187.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___725_77187.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___725_77187.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___725_77187.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___725_77187.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___725_77187.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___725_77187.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___725_77187.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___725_77187.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___725_77187.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___725_77187.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___725_77187.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___725_77187.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___725_77187.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___725_77187.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___725_77187.FStar_TypeChecker_Env.nbe)
            }  in
          let res = FStar_TypeChecker_Tc.push_context env1 msg  in
          FStar_Options.push ();
          if restore_cmd_line_options1
          then
            (let uu____77192 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____77192 (fun a1  -> ()))
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
          (fun uu___736_77243  ->
             match () with
             | () ->
                 let uu____77255 =
                   FStar_Universal.tc_one_fragment curmod env frag  in
                 (match uu____77255 with
                  | (m,env1) ->
                      let uu____77279 =
                        let uu____77289 = FStar_Errors.get_err_count ()  in
                        (m, env1, uu____77289)  in
                      FStar_Pervasives_Native.Some uu____77279)) ()
        with
        | FStar_Errors.Error (e,msg,r) when
            let uu____77325 = FStar_Options.trace_error ()  in
            Prims.op_Negation uu____77325 ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e,msg) when
            let uu____77356 = FStar_Options.trace_error ()  in
            Prims.op_Negation uu____77356 ->
            ((let uu____77359 =
                let uu____77369 =
                  let uu____77377 = FStar_TypeChecker_Env.get_range env  in
                  (e, msg, uu____77377)  in
                [uu____77369]  in
              FStar_TypeChecker_Err.add_errors env uu____77359);
             FStar_Pervasives_Native.None)
  
let (report_fail : unit -> unit) =
  fun uu____77407  ->
    (let uu____77409 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____77409 (fun a2  -> ()));
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
    match projectee with | Push _0 -> true | uu____77499 -> false
  
let (__proj__Push__item___0 :
  input_chunks -> (Prims.bool * Prims.int * Prims.int)) =
  fun projectee  -> match projectee with | Push _0 -> _0 
let (uu___is_Pop : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____77547 -> false
  
let (__proj__Pop__item___0 : input_chunks -> Prims.string) =
  fun projectee  -> match projectee with | Pop _0 -> _0 
let (uu___is_Code : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____77581 -> false
  
let (__proj__Code__item___0 :
  input_chunks -> (Prims.string * (Prims.string * Prims.string))) =
  fun projectee  -> match projectee with | Code _0 -> _0 
let (uu___is_Info : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Info _0 -> true | uu____77653 -> false
  
let (__proj__Info__item___0 :
  input_chunks ->
    (Prims.string * Prims.bool * (Prims.string * Prims.int * Prims.int)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Info _0 -> _0 
let (uu___is_Completions : input_chunks -> Prims.bool) =
  fun projectee  ->
    match projectee with | Completions _0 -> true | uu____77731 -> false
  
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
  let uu____78051 = FStar_Util.new_string_builder ()  in
  let uu____78052 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let uu____78059 = FStar_Util.mk_ref []  in
  let uu____78066 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  {
    chunk = uu____78051;
    stdin = uu____78052;
    buffer = uu____78059;
    log = uu____78066
  } 
let rec (read_chunk : unit -> input_chunks) =
  fun uu____78144  ->
    let s = the_interactive_state  in
    let log1 =
      let uu____78152 = FStar_Options.debug_any ()  in
      if uu____78152
      then
        let transcript =
          let uu____78160 = FStar_ST.op_Bang s.log  in
          match uu____78160 with
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
      else (fun uu____78218  -> ())  in
    let stdin =
      let uu____78221 = FStar_ST.op_Bang s.stdin  in
      match uu____78221 with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None  ->
          let i = FStar_Util.open_stdin ()  in
          (FStar_ST.op_Colon_Equals s.stdin (FStar_Pervasives_Native.Some i);
           i)
       in
    let line =
      let uu____78275 = FStar_Util.read_line stdin  in
      match uu____78275 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some l -> l  in
    log1 line;
    (let l = FStar_Util.trim_string line  in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____78305::ok::fail1::[] -> (ok, fail1)
         | uu____78317 -> ("ok", "fail")  in
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
               let uu____78347 =
                 FStar_Util.substring_from l (FStar_String.length "#push")
                  in
               FStar_Util.trim_string uu____78347  in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu____78379 = FStar_Util.int_of_string l1  in
                   let uu____78381 = FStar_Util.int_of_string c  in
                   (true, uu____78379, uu____78381)
               | l1::c::[] ->
                   let uu____78394 = FStar_Util.int_of_string l1  in
                   let uu____78396 = FStar_Util.int_of_string c  in
                   (false, uu____78394, uu____78396)
               | uu____78402 ->
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
              | uu____78420::symbol::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   Info (symbol, true, FStar_Pervasives_Native.None))
              | uu____78451::symbol::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   (let uu____78468 =
                      let uu____78488 =
                        let uu____78500 =
                          let uu____78510 = FStar_Util.int_of_string row  in
                          let uu____78512 = FStar_Util.int_of_string col  in
                          (file, uu____78510, uu____78512)  in
                        FStar_Pervasives_Native.Some uu____78500  in
                      (symbol, false, uu____78488)  in
                    Info uu____78468))
              | uu____78540 ->
                  (FStar_Errors.log_issue FStar_Range.dummyRange
                     (FStar_Errors.Error_IDEUnrecognized,
                       (Prims.op_Hat "Unrecognized \"#info\" request: " l));
                   FStar_All.exit (Prims.parse_int "1")))
           else
             if FStar_Util.starts_with l "#completions "
             then
               (match FStar_Util.split l " " with
                | uu____78553::prefix1::"#"::[] ->
                    (FStar_Util.clear_string_builder s.chunk;
                     Completions prefix1)
                | uu____78563 ->
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
  fun uu____78587  ->
    let s = the_interactive_state  in
    let uu____78589 = FStar_ST.op_Bang s.buffer  in
    match uu____78589 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.op_Colon_Equals s.buffer chunks; chunk)
  
let (fill_buffer : unit -> unit) =
  fun uu____78648  ->
    let s = the_interactive_state  in
    let uu____78650 =
      let uu____78653 = FStar_ST.op_Bang s.buffer  in
      let uu____78679 = let uu____78682 = read_chunk ()  in [uu____78682]  in
      FStar_List.append uu____78653 uu____78679  in
    FStar_ST.op_Colon_Equals s.buffer uu____78650
  
let (deps_of_our_file :
  Prims.string ->
    (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option *
      FStar_Parser_Dep.deps))
  =
  fun filename  ->
    let uu____78726 =
      FStar_Dependencies.find_deps_if_needed [filename]
        FStar_Universal.load_parsing_data_from_cache
       in
    match uu____78726 with
    | (deps,dep_graph1) ->
        let uu____78756 =
          FStar_List.partition
            (fun x  ->
               let uu____78773 = FStar_Parser_Dep.lowercase_module_name x  in
               let uu____78775 =
                 FStar_Parser_Dep.lowercase_module_name filename  in
               uu____78773 <> uu____78775) deps
           in
        (match uu____78756 with
         | (deps1,same_name) ->
             let maybe_intf =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____78819 =
                       (let uu____78823 = FStar_Parser_Dep.is_interface intf
                           in
                        Prims.op_Negation uu____78823) ||
                         (let uu____78826 =
                            FStar_Parser_Dep.is_implementation impl  in
                          Prims.op_Negation uu____78826)
                        in
                     if uu____78819
                     then
                       let uu____78829 =
                         let uu____78835 =
                           FStar_Util.format2
                             "Found %s and %s but not an interface + implementation"
                             intf impl
                            in
                         (FStar_Errors.Warning_MissingInterfaceOrImplementation,
                           uu____78835)
                          in
                       FStar_Errors.log_issue FStar_Range.dummyRange
                         uu____78829
                     else ());
                    FStar_Pervasives_Native.Some intf)
               | impl::[] -> FStar_Pervasives_Native.None
               | uu____78847 ->
                   ((let uu____78852 =
                       let uu____78858 =
                         FStar_Util.format1 "Unexpected: ended up with %s"
                           (FStar_String.concat " " same_name)
                          in
                       (FStar_Errors.Warning_UnexpectedFile, uu____78858)  in
                     FStar_Errors.log_issue FStar_Range.dummyRange
                       uu____78852);
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
            | uu____78931 ->
                let stack1 = (env, m) :: stack  in
                let env1 =
                  let uu____78947 = FStar_Options.lax ()  in
                  push_with_kind env uu____78947 true "typecheck_modul"  in
                let uu____78951 = tc_one_file remaining env1  in
                (match uu____78951 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____79001 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____79016 =
                               FStar_Parser_ParseIt.get_file_last_modification_time
                                 intf1
                                in
                             FStar_Pervasives_Native.Some uu____79016
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                          in
                       let impl_t =
                         FStar_Parser_ParseIt.get_file_last_modification_time
                           impl
                          in
                       (intf_t, impl_t)  in
                     (match uu____79001 with
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
                 | (uu____79155,uu____79156) ->
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
                     | uu____79304 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____79357 -> (false, depnames1))
                 in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____79440::ts3 ->
                    (pop env1 "";
                     (let uu____79488 =
                        let uu____79503 = FStar_List.hd stack  in
                        let uu____79512 = FStar_List.tl stack  in
                        (uu____79503, uu____79512)  in
                      match uu____79488 with
                      | ((env2,uu____79534),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3))
                 in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____79604 = ts_elt  in
                  (match uu____79604 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____79641 = match_dep depnames intf impl  in
                       (match uu____79641 with
                        | (b,depnames') ->
                            let uu____79666 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t)
                               in
                            if uu____79666
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1
                                 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____79686 =
                                 let uu____79695 = FStar_List.hd st  in
                                 let uu____79704 = FStar_List.tl st  in
                                 (uu____79695, uu____79704)  in
                               match uu____79686 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts  in
            let uu____79761 = deps_of_our_file filename  in
            match uu____79761 with
            | (filenames,uu____79781,dep_graph1) ->
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
            let uu____79884 = FStar_Range.string_of_range range  in
            let uu____79886 =
              FStar_TypeChecker_Normalize.term_to_string env typ  in
            let uu____79888 =
              match doc1 with
              | FStar_Pervasives_Native.Some docstring ->
                  FStar_Util.format1 "#doc %s" docstring
              | FStar_Pervasives_Native.None  -> ""  in
            FStar_Util.format4 "(defined at %s) %s: %s%s" uu____79884 name
              uu____79886 uu____79888
  
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
              let uu____79943 = shift_chunk ()  in
              match uu____79943 with
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
                    | FStar_Pervasives_Native.Some uu____80065 ->
                        info_at_pos_opt
                    | FStar_Pervasives_Native.None  ->
                        if symbol = ""
                        then FStar_Pervasives_Native.None
                        else
                          (let lid =
                             let uu____80129 =
                               FStar_List.map FStar_Ident.id_of_text
                                 (FStar_Util.split symbol ".")
                                in
                             FStar_Ident.lid_of_ids uu____80129  in
                           let lid1 =
                             if fqn_only
                             then lid
                             else
                               (let uu____80138 =
                                  FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid
                                   in
                                match uu____80138 with
                                | FStar_Pervasives_Native.None  -> lid
                                | FStar_Pervasives_Native.Some lid1 -> lid1)
                              in
                           let uu____80142 =
                             FStar_TypeChecker_Env.try_lookup_lid env lid1
                              in
                           FStar_All.pipe_right uu____80142
                             (FStar_Util.map_option
                                (fun uu____80199  ->
                                   match uu____80199 with
                                   | ((uu____80219,typ),r) ->
                                       ((FStar_Util.Inr lid1), typ, r))))
                     in
                  ((match info_opt with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Util.print_string "\n#done-nok\n"
                    | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
                        let uu____80269 =
                          match name_or_lid with
                          | FStar_Util.Inl name ->
                              (name, FStar_Pervasives_Native.None)
                          | FStar_Util.Inr lid ->
                              let uu____80296 = FStar_Ident.string_of_lid lid
                                 in
                              let uu____80298 =
                                let uu____80302 =
                                  FStar_Syntax_DsEnv.try_lookup_doc
                                    env.FStar_TypeChecker_Env.dsenv lid
                                   in
                                FStar_All.pipe_right uu____80302
                                  (FStar_Util.map_option
                                     FStar_Pervasives_Native.fst)
                                 in
                              (uu____80296, uu____80298)
                           in
                        (match uu____80269 with
                         | (name,doc1) ->
                             let uu____80373 =
                               format_info env name typ rng doc1  in
                             FStar_Util.print1 "%s\n#done-ok\n" uu____80373));
                   go line_col filename stack curmod env ts)
              | Completions search_term ->
                  let rec measure_anchored_match search_term1 candidate =
                    match (search_term1, candidate) with
                    | ([],uu____80422) ->
                        FStar_Pervasives_Native.Some
                          ([], (Prims.parse_int "0"))
                    | (uu____80442,[]) -> FStar_Pervasives_Native.None
                    | (hs::ts1,hc::tc1) ->
                        let hc_text = FStar_Ident.text_of_id hc  in
                        if FStar_Util.starts_with hc_text hs
                        then
                          (match ts1 with
                           | [] ->
                               FStar_Pervasives_Native.Some
                                 (candidate, (FStar_String.length hs))
                           | uu____80506 ->
                               let uu____80510 =
                                 measure_anchored_match ts1 tc1  in
                               FStar_All.pipe_right uu____80510
                                 (FStar_Util.map_option
                                    (fun uu____80555  ->
                                       match uu____80555 with
                                       | (matched,len) ->
                                           ((hc :: matched),
                                             (((FStar_String.length hc_text)
                                                 + (Prims.parse_int "1"))
                                                + len)))))
                        else FStar_Pervasives_Native.None
                     in
                  let rec locate_match needle candidate =
                    let uu____80625 = measure_anchored_match needle candidate
                       in
                    match uu____80625 with
                    | FStar_Pervasives_Native.Some (matched,n1) ->
                        FStar_Pervasives_Native.Some ([], matched, n1)
                    | FStar_Pervasives_Native.None  ->
                        (match candidate with
                         | [] -> FStar_Pervasives_Native.None
                         | hc::tc1 ->
                             let uu____80714 = locate_match needle tc1  in
                             FStar_All.pipe_right uu____80714
                               (FStar_Util.map_option
                                  (fun uu____80780  ->
                                     match uu____80780 with
                                     | (prefix1,matched,len) ->
                                         ((hc :: prefix1), matched, len))))
                     in
                  let str_of_ids ids =
                    let uu____80832 =
                      FStar_List.map FStar_Ident.text_of_id ids  in
                    FStar_Util.concat_l "." uu____80832  in
                  let match_lident_against needle lident =
                    locate_match needle
                      (FStar_List.append lident.FStar_Ident.ns
                         [lident.FStar_Ident.ident])
                     in
                  let shorten_namespace uu____80896 =
                    match uu____80896 with
                    | (prefix1,matched,match_len) ->
                        let naked_match =
                          match matched with
                          | uu____80936::[] -> true
                          | uu____80938 -> false  in
                        let uu____80942 =
                          FStar_Syntax_DsEnv.shorten_module_path
                            env.FStar_TypeChecker_Env.dsenv prefix1
                            naked_match
                           in
                        (match uu____80942 with
                         | (stripped_ns,shortened) ->
                             let uu____80973 = str_of_ids shortened  in
                             let uu____80975 = str_of_ids matched  in
                             let uu____80977 = str_of_ids stripped_ns  in
                             (uu____80973, uu____80975, uu____80977,
                               match_len))
                     in
                  let prepare_candidate uu____81009 =
                    match uu____81009 with
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
                                  let uu____81198 = FStar_Ident.ids_of_lid m
                                     in
                                  let uu____81201 = FStar_Ident.id_of_text n1
                                     in
                                  FStar_Ident.lid_of_ns_and_id uu____81198
                                    uu____81201
                                   in
                                let uu____81202 =
                                  FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid
                                   in
                                FStar_Option.map
                                  (fun fqn  ->
                                     let uu____81219 =
                                       let uu____81222 =
                                         FStar_List.map
                                           FStar_Ident.id_of_text orig_ns
                                          in
                                       FStar_List.append uu____81222
                                         [fqn.FStar_Ident.ident]
                                        in
                                     ([], uu____81219, matched_length))
                                  uu____81202
                              else FStar_Pervasives_Native.None))
                       in
                    let case_b_find_matches_in_env uu____81262 =
                      let matches =
                        FStar_List.filter_map (match_lident_against needle)
                          all_lidents_in_env
                         in
                      FStar_All.pipe_right matches
                        (FStar_List.filter
                           (fun uu____81343  ->
                              match uu____81343 with
                              | (ns,id1,uu____81358) ->
                                  let uu____81369 =
                                    let uu____81372 =
                                      FStar_Ident.lid_of_ids id1  in
                                    FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                                      env.FStar_TypeChecker_Env.dsenv
                                      uu____81372
                                     in
                                  (match uu____81369 with
                                   | FStar_Pervasives_Native.None  -> false
                                   | FStar_Pervasives_Native.Some l ->
                                       let uu____81376 =
                                         FStar_Ident.lid_of_ids
                                           (FStar_List.append ns id1)
                                          in
                                       FStar_Ident.lid_equals l uu____81376)))
                       in
                    let uu____81377 = FStar_Util.prefix needle  in
                    match uu____81377 with
                    | (ns,id1) ->
                        let matched_ids =
                          match ns with
                          | [] -> case_b_find_matches_in_env ()
                          | uu____81436 ->
                              let l =
                                FStar_Ident.lid_of_path ns
                                  FStar_Range.dummyRange
                                 in
                              let uu____81441 =
                                FStar_Syntax_DsEnv.resolve_module_name
                                  env.FStar_TypeChecker_Env.dsenv l true
                                 in
                              (match uu____81441 with
                               | FStar_Pervasives_Native.None  ->
                                   case_b_find_matches_in_env ()
                               | FStar_Pervasives_Native.Some m ->
                                   case_a_find_transitive_includes ns m id1)
                           in
                        FStar_All.pipe_right matched_ids
                          (FStar_List.map
                             (fun x  ->
                                let uu____81517 = shorten_namespace x  in
                                prepare_candidate uu____81517))
                     in
                  ((let uu____81531 =
                      FStar_Util.sort_with
                        (fun uu____81560  ->
                           fun uu____81561  ->
                             match (uu____81560, uu____81561) with
                             | ((cd1,ns1,uu____81601),(cd2,ns2,uu____81604))
                                 ->
                                 (match FStar_String.compare cd1 cd2 with
                                  | _81636 when
                                      _81636 = (Prims.parse_int "0") ->
                                      FStar_String.compare ns1 ns2
                                  | n1 -> n1)) matches
                       in
                    FStar_List.iter
                      (fun uu____81653  ->
                         match uu____81653 with
                         | (candidate,ns,match_len) ->
                             let uu____81672 =
                               FStar_Util.string_of_int match_len  in
                             FStar_Util.print3 "%s %s %s \n" uu____81672 ns
                               candidate) uu____81531);
                   FStar_Util.print_string "#done-ok\n";
                   go line_col filename stack curmod env ts)
              | Pop msg ->
                  (pop env msg;
                   (let uu____81680 =
                      match stack with
                      | [] ->
                          (FStar_Errors.log_issue FStar_Range.dummyRange
                             (FStar_Errors.Error_IDETooManyPops,
                               "too many pops");
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd1::tl1 -> (hd1, tl1)  in
                    match uu____81680 with
                    | ((env1,curmod1),stack1) ->
                        go line_col filename stack1 curmod1 env1 ts))
              | Push (lax1,l,c) ->
                  let uu____81749 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____81791 =
                        update_deps filename curmod stack env ts  in
                      (true, uu____81791)
                    else (false, (stack, env, ts))  in
                  (match uu____81749 with
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
                   | uu____81914 -> fail2 curmod env)
  
let (interactive_mode : Prims.string -> unit) =
  fun filename  ->
    (let uu____81935 =
       let uu____81937 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____81937  in
     if uu____81935
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen,
           "code-generation is not supported in interactive mode, ignoring the codegen flag")
     else ());
    (let uu____81945 = deps_of_our_file filename  in
     match uu____81945 with
     | (filenames,maybe_intf,dep_graph1) ->
         let env = FStar_Universal.init_env dep_graph1  in
         let uu____81974 =
           tc_deps FStar_Pervasives_Native.None [] env filenames []  in
         (match uu____81974 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____82003 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0")
                   in
                let uu____82006 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range "<input>" uu____82003 uu____82006  in
              let env2 = FStar_TypeChecker_Env.set_range env1 initial_range
                 in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2  in
              let uu____82016 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ())
                 in
              if uu____82016
              then
                let uu____82019 =
                  let uu____82021 = FStar_Options.file_list ()  in
                  FStar_List.hd uu____82021  in
                FStar_SMTEncoding_Solver.with_hints_db uu____82019
                  (fun uu____82027  ->
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack FStar_Pervasives_Native.None env3 ts)
              else
                go ((Prims.parse_int "1"), (Prims.parse_int "0")) filename
                  stack FStar_Pervasives_Native.None env3 ts))
  