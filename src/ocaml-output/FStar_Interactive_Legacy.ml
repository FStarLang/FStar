open Prims
let tc_one_file:
  Prims.string Prims.list ->
    FStar_TypeChecker_Env.env ->
      ((Prims.string FStar_Pervasives_Native.option,Prims.string)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,Prims.string
                                                                    Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun remaining  ->
    fun env  ->
      let uu____27 =
        match remaining with
        | intf::impl::remaining1 when
            FStar_Universal.needs_interleaving intf impl ->
            let uu____61 =
              FStar_Universal.tc_one_file env
                (FStar_Pervasives_Native.Some intf) impl in
            (match uu____61 with
             | (uu____84,env1) ->
                 (((FStar_Pervasives_Native.Some intf), impl), env1,
                   remaining1))
        | intf_or_impl::remaining1 ->
            let uu____108 =
              FStar_Universal.tc_one_file env FStar_Pervasives_Native.None
                intf_or_impl in
            (match uu____108 with
             | (uu____131,env1) ->
                 ((FStar_Pervasives_Native.None, intf_or_impl), env1,
                   remaining1))
        | [] -> failwith "Impossible" in
      match uu____27 with
      | ((intf,impl),env1,remaining1) -> ((intf, impl), env1, remaining1)
let tc_prims: Prims.unit -> FStar_TypeChecker_Env.env =
  fun uu____210  ->
    let uu____211 =
      let uu____220 = FStar_Universal.init_env () in
      FStar_Universal.tc_prims uu____220 in
    match uu____211 with | (uu____221,env) -> env
type env_t = FStar_TypeChecker_Env.env[@@deriving show]
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
[@@deriving show]
type stack_t = (env_t,modul_t) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
let pop: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  -> FStar_Universal.pop_context env msg; FStar_Options.pop ()
let push_with_kind:
  FStar_TypeChecker_Env.env ->
    Prims.bool -> Prims.bool -> Prims.string -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun lax1  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          let env1 =
            let uu___270_265 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___270_265.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___270_265.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___270_265.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___270_265.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___270_265.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___270_265.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___270_265.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___270_265.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___270_265.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___270_265.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___270_265.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___270_265.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___270_265.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___270_265.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___270_265.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___270_265.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___270_265.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___270_265.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = lax1;
              FStar_TypeChecker_Env.lax_universes =
                (uu___270_265.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___270_265.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___270_265.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___270_265.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___270_265.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___270_265.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___270_265.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___270_265.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___270_265.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___270_265.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___270_265.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___270_265.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___270_265.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___270_265.FStar_TypeChecker_Env.dsenv)
            } in
          let res = FStar_Universal.push_context env1 msg in
          FStar_Options.push ();
          if restore_cmd_line_options1
          then
            (let uu____269 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____269 FStar_Pervasives.ignore)
          else ();
          res
let cleanup: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  -> FStar_TypeChecker_Env.cleanup_interactive env
let check_frag:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
      (FStar_Parser_ParseIt.input_frag,Prims.bool)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env,
          Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option
  =
  fun env  ->
    fun curmod  ->
      fun frag  ->
        try
          let uu____335 = FStar_Universal.tc_one_fragment curmod env frag in
          match uu____335 with
          | FStar_Pervasives_Native.Some (m,env1) ->
              let uu____366 =
                let uu____375 = FStar_Errors.get_err_count () in
                (m, env1, uu____375) in
              FStar_Pervasives_Native.Some uu____366
          | uu____386 -> FStar_Pervasives_Native.None
        with
        | FStar_Errors.Error (msg,r) when
            let uu____420 = FStar_Options.trace_error () in
            Prims.op_Negation uu____420 ->
            (FStar_TypeChecker_Err.add_errors env [(msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err msg when
            let uu____439 = FStar_Options.trace_error () in
            Prims.op_Negation uu____439 ->
            ((let uu____441 =
                let uu____448 =
                  let uu____453 = FStar_TypeChecker_Env.get_range env in
                  (msg, uu____453) in
                [uu____448] in
              FStar_TypeChecker_Err.add_errors env uu____441);
             FStar_Pervasives_Native.None)
let report_fail: Prims.unit -> Prims.unit =
  fun uu____473  ->
    (let uu____475 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____475 FStar_Pervasives.ignore);
    FStar_Errors.clear ()
type input_chunks =
  | Push of (Prims.bool,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  | Pop of Prims.string
  | Code of
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2
  | Info of
  (Prims.string,Prims.bool,(Prims.string,Prims.int,Prims.int)
                             FStar_Pervasives_Native.tuple3
                             FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3
  | Completions of Prims.string[@@deriving show]
let uu___is_Push: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____541 -> false
let __proj__Push__item___0:
  input_chunks ->
    (Prims.bool,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_Pop: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____573 -> false
let __proj__Pop__item___0: input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Pop _0 -> _0
let uu___is_Code: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____595 -> false
let __proj__Code__item___0:
  input_chunks ->
    (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Code _0 -> _0
let uu___is_Info: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Info _0 -> true | uu____647 -> false
let __proj__Info__item___0:
  input_chunks ->
    (Prims.string,Prims.bool,(Prims.string,Prims.int,Prims.int)
                               FStar_Pervasives_Native.tuple3
                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Info _0 -> _0
let uu___is_Completions: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Completions _0 -> true | uu____703 -> false
let __proj__Completions__item___0: input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Completions _0 -> _0
type interactive_state =
  {
  chunk: FStar_Util.string_builder;
  stdin:
    FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref;
  buffer: input_chunks Prims.list FStar_ST.ref;
  log: FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref;}
[@@deriving show]
let __proj__Mkinteractive_state__item__chunk:
  interactive_state -> FStar_Util.string_builder =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__chunk
let __proj__Mkinteractive_state__item__stdin:
  interactive_state ->
    FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__stdin
let __proj__Mkinteractive_state__item__buffer:
  interactive_state -> input_chunks Prims.list FStar_ST.ref =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__buffer
let __proj__Mkinteractive_state__item__log:
  interactive_state ->
    FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__log
let the_interactive_state: interactive_state =
  let uu____946 = FStar_Util.new_string_builder () in
  let uu____947 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let uu____954 = FStar_Util.mk_ref [] in
  let uu____961 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  { chunk = uu____946; stdin = uu____947; buffer = uu____954; log = uu____961
  }
let rec read_chunk: Prims.unit -> input_chunks =
  fun uu____1013  ->
    let s = the_interactive_state in
    let log1 =
      let uu____1018 = FStar_Options.debug_any () in
      if uu____1018
      then
        let transcript =
          let uu____1022 = FStar_ST.op_Bang s.log in
          match uu____1022 with
          | FStar_Pervasives_Native.Some transcript -> transcript
          | FStar_Pervasives_Native.None  ->
              let transcript = FStar_Util.open_file_for_writing "transcript" in
              (FStar_ST.op_Colon_Equals s.log
                 (FStar_Pervasives_Native.Some transcript);
               transcript) in
        fun line  ->
          (FStar_Util.append_to_file transcript line;
           FStar_Util.flush_file transcript)
      else (fun uu____1131  -> ()) in
    let stdin =
      let uu____1133 = FStar_ST.op_Bang s.stdin in
      match uu____1133 with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None  ->
          let i = FStar_Util.open_stdin () in
          (FStar_ST.op_Colon_Equals s.stdin (FStar_Pervasives_Native.Some i);
           i) in
    let line =
      let uu____1240 = FStar_Util.read_line stdin in
      match uu____1240 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some l -> l in
    log1 line;
    (let l = FStar_Util.trim_string line in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____1255::ok::fail4::[] -> (ok, fail4)
         | uu____1258 -> ("ok", "fail") in
       let str = FStar_Util.string_of_string_builder s.chunk in
       (FStar_Util.clear_string_builder s.chunk; Code (str, responses))
     else
       if FStar_Util.starts_with l "#pop"
       then (FStar_Util.clear_string_builder s.chunk; Pop l)
       else
         if FStar_Util.starts_with l "#push"
         then
           (FStar_Util.clear_string_builder s.chunk;
            (let lc_lax =
               let uu____1272 =
                 FStar_Util.substring_from l (FStar_String.length "#push") in
               FStar_Util.trim_string uu____1272 in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu____1288 = FStar_Util.int_of_string l1 in
                   let uu____1289 = FStar_Util.int_of_string c in
                   (true, uu____1288, uu____1289)
               | l1::c::[] ->
                   let uu____1292 = FStar_Util.int_of_string l1 in
                   let uu____1293 = FStar_Util.int_of_string c in
                   (false, uu____1292, uu____1293)
               | uu____1294 ->
                   (FStar_Util.print_warning
                      (Prims.strcat
                         "Error locations may be wrong, unrecognized string after #push: "
                         lc_lax);
                    (false, (Prims.parse_int "1"), (Prims.parse_int "0"))) in
             Push lc))
         else
           if FStar_Util.starts_with l "#info "
           then
             (match FStar_Util.split l " " with
              | uu____1299::symbol::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   Info (symbol, true, FStar_Pervasives_Native.None))
              | uu____1316::symbol::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   (let uu____1322 =
                      let uu____1337 =
                        let uu____1346 =
                          let uu____1353 = FStar_Util.int_of_string row in
                          let uu____1354 = FStar_Util.int_of_string col in
                          (file, uu____1353, uu____1354) in
                        FStar_Pervasives_Native.Some uu____1346 in
                      (symbol, false, uu____1337) in
                    Info uu____1322))
              | uu____1369 ->
                  (FStar_Util.print_error
                     (Prims.strcat "Unrecognized \"#info\" request: " l);
                   FStar_All.exit (Prims.parse_int "1")))
           else
             if FStar_Util.starts_with l "#completions "
             then
               (match FStar_Util.split l " " with
                | uu____1374::prefix1::"#"::[] ->
                    (FStar_Util.clear_string_builder s.chunk;
                     Completions prefix1)
                | uu____1377 ->
                    (FStar_Util.print_error
                       (Prims.strcat
                          "Unrecognized \"#completions\" request: " l);
                     FStar_All.exit (Prims.parse_int "1")))
             else
               if l = "#finish"
               then FStar_All.exit (Prims.parse_int "0")
               else
                 (FStar_Util.string_builder_append s.chunk line;
                  FStar_Util.string_builder_append s.chunk "\n";
                  read_chunk ()))
let shift_chunk: Prims.unit -> input_chunks =
  fun uu____1388  ->
    let s = the_interactive_state in
    let uu____1390 = FStar_ST.op_Bang s.buffer in
    match uu____1390 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.op_Colon_Equals s.buffer chunks; chunk)
let fill_buffer: Prims.unit -> Prims.unit =
  fun uu____1501  ->
    let s = the_interactive_state in
    let uu____1503 =
      let uu____1506 = FStar_ST.op_Bang s.buffer in
      let uu____1559 = let uu____1562 = read_chunk () in [uu____1562] in
      FStar_List.append uu____1506 uu____1559 in
    FStar_ST.op_Colon_Equals s.buffer uu____1503
let deps_of_our_file:
  Prims.string ->
    (Prims.string Prims.list,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename] in
    let uu____1628 =
      FStar_List.partition
        (fun x  ->
           let uu____1641 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____1642 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____1641 <> uu____1642) deps in
    match uu____1628 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____1669 =
                  (let uu____1672 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____1672) ||
                    (let uu____1674 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____1674) in
                if uu____1669
                then
                  let uu____1675 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____1675
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____1678 ->
              ((let uu____1682 =
                  FStar_Util.format1 "Unexpected: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____1682);
               FStar_Pervasives_Native.None) in
        (deps1, maybe_intf)
type m_timestamps =
  (Prims.string FStar_Pervasives_Native.option,Prims.string,FStar_Util.time
                                                              FStar_Pervasives_Native.option,
    FStar_Util.time) FStar_Pervasives_Native.tuple4 Prims.list[@@deriving
                                                                show]
let rec tc_deps:
  modul_t ->
    stack_t ->
      FStar_TypeChecker_Env.env ->
        Prims.string Prims.list ->
          m_timestamps ->
            (stack_t,FStar_TypeChecker_Env.env,m_timestamps)
              FStar_Pervasives_Native.tuple3
  =
  fun m  ->
    fun stack  ->
      fun env  ->
        fun remaining  ->
          fun ts  ->
            match remaining with
            | [] -> (stack, env, ts)
            | uu____1737 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____1752 = FStar_Options.lax () in
                  push_with_kind env uu____1752 true "typecheck_modul" in
                let uu____1753 = tc_one_file remaining env1 in
                (match uu____1753 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____1792 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____1805 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____1805
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____1792 with
                      | (intf_t,impl_t) ->
                          tc_deps m stack1 env2 remaining1
                            ((intf, impl, intf_t, impl_t) :: ts)))
let update_deps:
  Prims.string ->
    modul_t ->
      stack_t ->
        env_t ->
          m_timestamps ->
            (stack_t,env_t,m_timestamps) FStar_Pervasives_Native.tuple3
  =
  fun filename  ->
    fun m  ->
      fun stk  ->
        fun env  ->
          fun ts  ->
            let is_stale intf impl intf_t impl_t =
              let impl_mt = FStar_Util.get_file_last_modification_time impl in
              (FStar_Util.is_before impl_t impl_mt) ||
                (match (intf, intf_t) with
                 | (FStar_Pervasives_Native.Some
                    intf1,FStar_Pervasives_Native.Some intf_t1) ->
                     let intf_mt =
                       FStar_Util.get_file_last_modification_time intf1 in
                     FStar_Util.is_before intf_t1 intf_mt
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> false
                 | (uu____1909,uu____1910) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None") in
            let rec iterate depnames st env' ts1 good_stack good_ts =
              let match_dep depnames1 intf impl =
                match intf with
                | FStar_Pervasives_Native.None  ->
                    (match depnames1 with
                     | dep1::depnames' ->
                         if dep1 = impl
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____2005 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____2033 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____2100::ts3 ->
                    (pop env1 "";
                     (let uu____2141 =
                        let uu____2156 = FStar_List.hd stack in
                        let uu____2165 = FStar_List.tl stack in
                        (uu____2156, uu____2165) in
                      match uu____2141 with
                      | ((env2,uu____2187),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____2251 = ts_elt in
                  (match uu____2251 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____2282 = match_dep depnames intf impl in
                       (match uu____2282 with
                        | (b,depnames') ->
                            let uu____2301 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____2301
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____2318 =
                                 let uu____2333 = FStar_List.hd st in
                                 let uu____2342 = FStar_List.tl st in
                                 (uu____2333, uu____2342) in
                               match uu____2318 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____2419 = deps_of_our_file filename in
            match uu____2419 with
            | (filenames,uu____2435) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let format_info:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term ->
        FStar_Range.range ->
          Prims.string FStar_Pervasives_Native.option -> Prims.string
  =
  fun env  ->
    fun name  ->
      fun typ  ->
        fun range  ->
          fun doc1  ->
            let uu____2516 = FStar_Range.string_of_range range in
            let uu____2517 =
              FStar_TypeChecker_Normalize.term_to_string env typ in
            let uu____2518 =
              match doc1 with
              | FStar_Pervasives_Native.Some docstring ->
                  FStar_Util.format1 "#doc %s" docstring
              | FStar_Pervasives_Native.None  -> "" in
            FStar_Util.format4 "(defined at %s) %s: %s%s" uu____2516 name
              uu____2517 uu____2518
let rec go:
  (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2 ->
    Prims.string -> stack_t -> modul_t -> env_t -> m_timestamps -> Prims.unit
  =
  fun line_col  ->
    fun filename  ->
      fun stack  ->
        fun curmod  ->
          fun env  ->
            fun ts  ->
              let uu____2552 = shift_chunk () in
              match uu____2552 with
              | Info (symbol,fqn_only,pos_opt) ->
                  let info_at_pos_opt =
                    match pos_opt with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (file,row,col) ->
                        FStar_TypeChecker_Err.info_at_pos env file row col in
                  let info_opt =
                    match info_at_pos_opt with
                    | FStar_Pervasives_Native.Some uu____2647 ->
                        info_at_pos_opt
                    | FStar_Pervasives_Native.None  ->
                        if symbol = ""
                        then FStar_Pervasives_Native.None
                        else
                          (let lid =
                             let uu____2702 =
                               FStar_List.map FStar_Ident.id_of_text
                                 (FStar_Util.split symbol ".") in
                             FStar_Ident.lid_of_ids uu____2702 in
                           let lid1 =
                             if fqn_only
                             then lid
                             else
                               (let uu____2707 =
                                  FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid in
                                match uu____2707 with
                                | FStar_Pervasives_Native.None  -> lid
                                | FStar_Pervasives_Native.Some lid1 -> lid1) in
                           let uu____2711 =
                             FStar_TypeChecker_Env.try_lookup_lid env lid1 in
                           FStar_All.pipe_right uu____2711
                             (FStar_Util.map_option
                                (fun uu____2766  ->
                                   match uu____2766 with
                                   | ((uu____2785,typ),r) ->
                                       ((FStar_Util.Inr lid1), typ, r)))) in
                  ((match info_opt with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Util.print_string "\n#done-nok\n"
                    | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
                        let uu____2828 =
                          match name_or_lid with
                          | FStar_Util.Inl name ->
                              (name, FStar_Pervasives_Native.None)
                          | FStar_Util.Inr lid ->
                              let uu____2845 = FStar_Ident.string_of_lid lid in
                              let uu____2846 =
                                let uu____2849 =
                                  FStar_ToSyntax_Env.try_lookup_doc
                                    env.FStar_TypeChecker_Env.dsenv lid in
                                FStar_All.pipe_right uu____2849
                                  (FStar_Util.map_option
                                     FStar_Pervasives_Native.fst) in
                              (uu____2845, uu____2846) in
                        (match uu____2828 with
                         | (name,doc1) ->
                             let uu____2880 =
                               format_info env name typ rng doc1 in
                             FStar_Util.print1 "%s\n#done-ok\n" uu____2880));
                   go line_col filename stack curmod env ts)
              | Completions search_term ->
                  let rec measure_anchored_match search_term1 candidate =
                    match (search_term1, candidate) with
                    | ([],uu____2917) ->
                        FStar_Pervasives_Native.Some
                          ([], (Prims.parse_int "0"))
                    | (uu____2932,[]) -> FStar_Pervasives_Native.None
                    | (hs::ts1,hc::tc) ->
                        let hc_text = FStar_Ident.text_of_id hc in
                        if FStar_Util.starts_with hc_text hs
                        then
                          (match ts1 with
                           | [] ->
                               FStar_Pervasives_Native.Some
                                 (candidate, (FStar_String.length hs))
                           | uu____2982 ->
                               let uu____2985 = measure_anchored_match ts1 tc in
                               FStar_All.pipe_right uu____2985
                                 (FStar_Util.map_option
                                    (fun uu____3025  ->
                                       match uu____3025 with
                                       | (matched,len) ->
                                           ((hc :: matched),
                                             (((FStar_String.length hc_text)
                                                 + (Prims.parse_int "1"))
                                                + len)))))
                        else FStar_Pervasives_Native.None in
                  let rec locate_match needle candidate =
                    let uu____3080 = measure_anchored_match needle candidate in
                    match uu____3080 with
                    | FStar_Pervasives_Native.Some (matched,n1) ->
                        FStar_Pervasives_Native.Some ([], matched, n1)
                    | FStar_Pervasives_Native.None  ->
                        (match candidate with
                         | [] -> FStar_Pervasives_Native.None
                         | hc::tc ->
                             let uu____3159 = locate_match needle tc in
                             FStar_All.pipe_right uu____3159
                               (FStar_Util.map_option
                                  (fun uu____3220  ->
                                     match uu____3220 with
                                     | (prefix1,matched,len) ->
                                         ((hc :: prefix1), matched, len)))) in
                  let str_of_ids ids =
                    let uu____3264 =
                      FStar_List.map FStar_Ident.text_of_id ids in
                    FStar_Util.concat_l "." uu____3264 in
                  let match_lident_against needle lident =
                    locate_match needle
                      (FStar_List.append lident.FStar_Ident.ns
                         [lident.FStar_Ident.ident]) in
                  let shorten_namespace uu____3311 =
                    match uu____3311 with
                    | (prefix1,matched,match_len) ->
                        let naked_match =
                          match matched with
                          | uu____3342::[] -> true
                          | uu____3343 -> false in
                        let uu____3346 =
                          FStar_ToSyntax_Env.shorten_module_path
                            env.FStar_TypeChecker_Env.dsenv prefix1
                            naked_match in
                        (match uu____3346 with
                         | (stripped_ns,shortened) ->
                             let uu____3373 = str_of_ids shortened in
                             let uu____3374 = str_of_ids matched in
                             let uu____3375 = str_of_ids stripped_ns in
                             (uu____3373, uu____3374, uu____3375, match_len)) in
                  let prepare_candidate uu____3393 =
                    match uu____3393 with
                    | (prefix1,matched,stripped_ns,match_len) ->
                        if prefix1 = ""
                        then (matched, stripped_ns, match_len)
                        else
                          ((Prims.strcat prefix1 (Prims.strcat "." matched)),
                            stripped_ns,
                            (((FStar_String.length prefix1) + match_len) +
                               (Prims.parse_int "1"))) in
                  let needle = FStar_Util.split search_term "." in
                  let all_lidents_in_env = FStar_TypeChecker_Env.lidents env in
                  let matches =
                    let case_a_find_transitive_includes orig_ns m id =
                      let exported_names =
                        FStar_ToSyntax_Env.transitive_exported_ids
                          env.FStar_TypeChecker_Env.dsenv m in
                      let matched_length =
                        FStar_List.fold_left
                          (fun out  ->
                             fun s  ->
                               ((FStar_String.length s) + out) +
                                 (Prims.parse_int "1"))
                          (FStar_String.length id) orig_ns in
                      FStar_All.pipe_right exported_names
                        (FStar_List.filter_map
                           (fun n1  ->
                              if FStar_Util.starts_with n1 id
                              then
                                let lid =
                                  FStar_Ident.lid_of_ns_and_id
                                    (FStar_Ident.ids_of_lid m)
                                    (FStar_Ident.id_of_text n1) in
                                let uu____3521 =
                                  FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid in
                                FStar_Option.map
                                  (fun fqn  ->
                                     let uu____3537 =
                                       let uu____3540 =
                                         FStar_List.map
                                           FStar_Ident.id_of_text orig_ns in
                                       FStar_List.append uu____3540
                                         [fqn.FStar_Ident.ident] in
                                     ([], uu____3537, matched_length))
                                  uu____3521
                              else FStar_Pervasives_Native.None)) in
                    let case_b_find_matches_in_env uu____3573 =
                      let matches =
                        FStar_List.filter_map (match_lident_against needle)
                          all_lidents_in_env in
                      FStar_All.pipe_right matches
                        (FStar_List.filter
                           (fun uu____3648  ->
                              match uu____3648 with
                              | (ns,id,uu____3661) ->
                                  let uu____3670 =
                                    let uu____3673 =
                                      FStar_Ident.lid_of_ids id in
                                    FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                      env.FStar_TypeChecker_Env.dsenv
                                      uu____3673 in
                                  (match uu____3670 with
                                   | FStar_Pervasives_Native.None  -> false
                                   | FStar_Pervasives_Native.Some l ->
                                       let uu____3675 =
                                         FStar_Ident.lid_of_ids
                                           (FStar_List.append ns id) in
                                       FStar_Ident.lid_equals l uu____3675))) in
                    let uu____3676 = FStar_Util.prefix needle in
                    match uu____3676 with
                    | (ns,id) ->
                        let matched_ids =
                          match ns with
                          | [] -> case_b_find_matches_in_env ()
                          | uu____3722 ->
                              let l =
                                FStar_Ident.lid_of_path ns
                                  FStar_Range.dummyRange in
                              let uu____3726 =
                                FStar_ToSyntax_Env.resolve_module_name
                                  env.FStar_TypeChecker_Env.dsenv l true in
                              (match uu____3726 with
                               | FStar_Pervasives_Native.None  ->
                                   case_b_find_matches_in_env ()
                               | FStar_Pervasives_Native.Some m ->
                                   case_a_find_transitive_includes ns m id) in
                        FStar_All.pipe_right matched_ids
                          (FStar_List.map
                             (fun x  ->
                                let uu____3791 = shorten_namespace x in
                                prepare_candidate uu____3791)) in
                  ((let uu____3801 =
                      FStar_Util.sort_with
                        (fun uu____3824  ->
                           fun uu____3825  ->
                             match (uu____3824, uu____3825) with
                             | ((cd1,ns1,uu____3852),(cd2,ns2,uu____3855)) ->
                                 (match FStar_String.compare cd1 cd2 with
                                  | _0_50 when _0_50 = (Prims.parse_int "0")
                                      -> FStar_String.compare ns1 ns2
                                  | n1 -> n1)) matches in
                    FStar_List.iter
                      (fun uu____3880  ->
                         match uu____3880 with
                         | (candidate,ns,match_len) ->
                             let uu____3890 =
                               FStar_Util.string_of_int match_len in
                             FStar_Util.print3 "%s %s %s \n" uu____3890 ns
                               candidate) uu____3801);
                   FStar_Util.print_string "#done-ok\n";
                   go line_col filename stack curmod env ts)
              | Pop msg ->
                  (pop env msg;
                   (let uu____3894 =
                      match stack with
                      | [] ->
                          (FStar_Util.print_error "too many pops";
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd1::tl1 -> (hd1, tl1) in
                    match uu____3894 with
                    | ((env1,curmod1),stack1) ->
                        (if
                           (FStar_List.length stack1) =
                             (FStar_List.length ts)
                         then cleanup env1
                         else ();
                         go line_col filename stack1 curmod1 env1 ts)))
              | Push (lax1,l,c) ->
                  let uu____4008 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____4045 =
                        update_deps filename curmod stack env ts in
                      (true, uu____4045)
                    else (false, (stack, env, ts)) in
                  (match uu____4008 with
                   | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
                       let stack2 = (env1, curmod) :: stack1 in
                       let env2 =
                         push_with_kind env1 lax1 restore_cmd_line_options1
                           "#push" in
                       go (l, c) filename stack2 curmod env2 ts1)
              | Code (text1,(ok,fail4)) ->
                  let fail5 curmod1 tcenv =
                    report_fail ();
                    FStar_Util.print1 "%s\n" fail4;
                    go line_col filename stack curmod1 tcenv ts in
                  let frag =
                    {
                      FStar_Parser_ParseIt.frag_text = text1;
                      FStar_Parser_ParseIt.frag_line =
                        (FStar_Pervasives_Native.fst line_col);
                      FStar_Parser_ParseIt.frag_col =
                        (FStar_Pervasives_Native.snd line_col)
                    } in
                  let res = check_frag env curmod (frag, false) in
                  (match res with
                   | FStar_Pervasives_Native.Some (curmod1,env1,n_errs) ->
                       if n_errs = (Prims.parse_int "0")
                       then
                         (FStar_Util.print1 "\n%s\n" ok;
                          go line_col filename stack curmod1 env1 ts)
                       else fail5 curmod1 env1
                   | uu____4132 -> fail5 curmod env)
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    (let uu____4148 =
       let uu____4149 = FStar_Options.codegen () in
       FStar_Option.isSome uu____4149 in
     if uu____4148
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____4153 = deps_of_our_file filename in
     match uu____4153 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____4173 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu____4173 with
          | (stack,env1,ts) ->
              let initial_range1 =
                let uu____4200 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____4201 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____4200 uu____4201 in
              let env2 = FStar_TypeChecker_Env.set_range env1 initial_range1 in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2 in
              let uu____4205 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ()) in
              if uu____4205
              then
                let uu____4206 =
                  let uu____4207 = FStar_Options.file_list () in
                  FStar_List.hd uu____4207 in
                FStar_SMTEncoding_Solver.with_hints_db uu____4206
                  (fun uu____4211  ->
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack FStar_Pervasives_Native.None env3 ts)
              else
                go ((Prims.parse_int "1"), (Prims.parse_int "0")) filename
                  stack FStar_Pervasives_Native.None env3 ts))