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
            let uu___312_241 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___312_241.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___312_241.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___312_241.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___312_241.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___312_241.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___312_241.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___312_241.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___312_241.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___312_241.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___312_241.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___312_241.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___312_241.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___312_241.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___312_241.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___312_241.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___312_241.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___312_241.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___312_241.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = lax1;
              FStar_TypeChecker_Env.lax_universes =
                (uu___312_241.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___312_241.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___312_241.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___312_241.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___312_241.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___312_241.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___312_241.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___312_241.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___312_241.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___312_241.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___312_241.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___312_241.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___312_241.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___312_241.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___312_241.FStar_TypeChecker_Env.dep_graph)
            } in
          let res = FStar_Universal.push_context env1 msg in
          FStar_Options.push ();
          if restore_cmd_line_options1
          then
            (let uu____245 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____245 FStar_Pervasives.ignore)
          else ();
          res
let check_frag:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env,
          Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option
  =
  fun env  ->
    fun curmod  ->
      fun frag  ->
        try
          let uu____299 = FStar_Universal.tc_one_fragment curmod env frag in
          match uu____299 with
          | (m,env1) ->
              let uu____322 =
                let uu____331 = FStar_Errors.get_err_count () in
                (m, env1, uu____331) in
              FStar_Pervasives_Native.Some uu____322
        with
        | FStar_Errors.Error (msg,r) when
            let uu____359 = FStar_Options.trace_error () in
            Prims.op_Negation uu____359 ->
            (FStar_TypeChecker_Err.add_errors env [(msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err msg when
            let uu____378 = FStar_Options.trace_error () in
            Prims.op_Negation uu____378 ->
            ((let uu____380 =
                let uu____387 =
                  let uu____392 = FStar_TypeChecker_Env.get_range env in
                  (msg, uu____392) in
                [uu____387] in
              FStar_TypeChecker_Err.add_errors env uu____380);
             FStar_Pervasives_Native.None)
let report_fail: Prims.unit -> Prims.unit =
  fun uu____412  ->
    (let uu____414 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____414 FStar_Pervasives.ignore);
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
    match projectee with | Push _0 -> true | uu____480 -> false
let __proj__Push__item___0:
  input_chunks ->
    (Prims.bool,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_Pop: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____512 -> false
let __proj__Pop__item___0: input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Pop _0 -> _0
let uu___is_Code: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____534 -> false
let __proj__Code__item___0:
  input_chunks ->
    (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Code _0 -> _0
let uu___is_Info: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Info _0 -> true | uu____586 -> false
let __proj__Info__item___0:
  input_chunks ->
    (Prims.string,Prims.bool,(Prims.string,Prims.int,Prims.int)
                               FStar_Pervasives_Native.tuple3
                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Info _0 -> _0
let uu___is_Completions: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Completions _0 -> true | uu____642 -> false
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
  let uu____885 = FStar_Util.new_string_builder () in
  let uu____886 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let uu____893 = FStar_Util.mk_ref [] in
  let uu____900 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  { chunk = uu____885; stdin = uu____886; buffer = uu____893; log = uu____900
  }
let rec read_chunk: Prims.unit -> input_chunks =
  fun uu____952  ->
    let s = the_interactive_state in
    let log1 =
      let uu____957 = FStar_Options.debug_any () in
      if uu____957
      then
        let transcript =
          let uu____961 = FStar_ST.op_Bang s.log in
          match uu____961 with
          | FStar_Pervasives_Native.Some transcript -> transcript
          | FStar_Pervasives_Native.None  ->
              let transcript = FStar_Util.open_file_for_writing "transcript" in
              (FStar_ST.op_Colon_Equals s.log
                 (FStar_Pervasives_Native.Some transcript);
               transcript) in
        fun line  ->
          (FStar_Util.append_to_file transcript line;
           FStar_Util.flush_file transcript)
      else (fun uu____1070  -> ()) in
    let stdin =
      let uu____1072 = FStar_ST.op_Bang s.stdin in
      match uu____1072 with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None  ->
          let i = FStar_Util.open_stdin () in
          (FStar_ST.op_Colon_Equals s.stdin (FStar_Pervasives_Native.Some i);
           i) in
    let line =
      let uu____1179 = FStar_Util.read_line stdin in
      match uu____1179 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some l -> l in
    log1 line;
    (let l = FStar_Util.trim_string line in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____1194::ok::fail4::[] -> (ok, fail4)
         | uu____1197 -> ("ok", "fail") in
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
               let uu____1211 =
                 FStar_Util.substring_from l (FStar_String.length "#push") in
               FStar_Util.trim_string uu____1211 in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu____1227 = FStar_Util.int_of_string l1 in
                   let uu____1228 = FStar_Util.int_of_string c in
                   (true, uu____1227, uu____1228)
               | l1::c::[] ->
                   let uu____1231 = FStar_Util.int_of_string l1 in
                   let uu____1232 = FStar_Util.int_of_string c in
                   (false, uu____1231, uu____1232)
               | uu____1233 ->
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
              | uu____1238::symbol::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   Info (symbol, true, FStar_Pervasives_Native.None))
              | uu____1255::symbol::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   (let uu____1261 =
                      let uu____1276 =
                        let uu____1285 =
                          let uu____1292 = FStar_Util.int_of_string row in
                          let uu____1293 = FStar_Util.int_of_string col in
                          (file, uu____1292, uu____1293) in
                        FStar_Pervasives_Native.Some uu____1285 in
                      (symbol, false, uu____1276) in
                    Info uu____1261))
              | uu____1308 ->
                  (FStar_Util.print_error
                     (Prims.strcat "Unrecognized \"#info\" request: " l);
                   FStar_All.exit (Prims.parse_int "1")))
           else
             if FStar_Util.starts_with l "#completions "
             then
               (match FStar_Util.split l " " with
                | uu____1313::prefix1::"#"::[] ->
                    (FStar_Util.clear_string_builder s.chunk;
                     Completions prefix1)
                | uu____1316 ->
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
  fun uu____1327  ->
    let s = the_interactive_state in
    let uu____1329 = FStar_ST.op_Bang s.buffer in
    match uu____1329 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.op_Colon_Equals s.buffer chunks; chunk)
let fill_buffer: Prims.unit -> Prims.unit =
  fun uu____1440  ->
    let s = the_interactive_state in
    let uu____1442 =
      let uu____1445 = FStar_ST.op_Bang s.buffer in
      let uu____1498 = let uu____1501 = read_chunk () in [uu____1501] in
      FStar_List.append uu____1445 uu____1498 in
    FStar_ST.op_Colon_Equals s.buffer uu____1442
let deps_of_our_file:
  Prims.string ->
    (Prims.string Prims.list,Prims.string FStar_Pervasives_Native.option,
      FStar_Parser_Dep.deps) FStar_Pervasives_Native.tuple3
  =
  fun filename  ->
    let uu____1566 = FStar_Dependencies.find_deps_if_needed [filename] in
    match uu____1566 with
    | (deps,dep_graph1) ->
        let uu____1589 =
          FStar_List.partition
            (fun x  ->
               let uu____1602 = FStar_Parser_Dep.lowercase_module_name x in
               let uu____1603 =
                 FStar_Parser_Dep.lowercase_module_name filename in
               uu____1602 <> uu____1603) deps in
        (match uu____1589 with
         | (deps1,same_name) ->
             let maybe_intf =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____1632 =
                       (let uu____1635 = FStar_Parser_Dep.is_interface intf in
                        Prims.op_Negation uu____1635) ||
                         (let uu____1637 =
                            FStar_Parser_Dep.is_implementation impl in
                          Prims.op_Negation uu____1637) in
                     if uu____1632
                     then
                       let uu____1638 =
                         FStar_Util.format2
                           "Found %s and %s but not an interface + implementation"
                           intf impl in
                       FStar_Util.print_warning uu____1638
                     else ());
                    FStar_Pervasives_Native.Some intf)
               | impl::[] -> FStar_Pervasives_Native.None
               | uu____1641 ->
                   ((let uu____1645 =
                       FStar_Util.format1 "Unexpected: ended up with %s"
                         (FStar_String.concat " " same_name) in
                     FStar_Util.print_warning uu____1645);
                    FStar_Pervasives_Native.None) in
             (deps1, maybe_intf, dep_graph1))
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
            | uu____1700 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____1715 = FStar_Options.lax () in
                  push_with_kind env uu____1715 true "typecheck_modul" in
                let uu____1716 = tc_one_file remaining env1 in
                (match uu____1716 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____1755 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____1768 =
                               FStar_Parser_ParseIt.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____1768
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Parser_ParseIt.get_file_last_modification_time
                           impl in
                       (intf_t, impl_t) in
                     (match uu____1755 with
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
              let impl_mt =
                FStar_Parser_ParseIt.get_file_last_modification_time impl in
              (FStar_Util.is_before impl_t impl_mt) ||
                (match (intf, intf_t) with
                 | (FStar_Pervasives_Native.Some
                    intf1,FStar_Pervasives_Native.Some intf_t1) ->
                     let intf_mt =
                       FStar_Parser_ParseIt.get_file_last_modification_time
                         intf1 in
                     FStar_Util.is_before intf_t1 intf_mt
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> false
                 | (uu____1872,uu____1873) ->
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
                     | uu____1968 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1996 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____2063::ts3 ->
                    (pop env1 "";
                     (let uu____2104 =
                        let uu____2119 = FStar_List.hd stack in
                        let uu____2128 = FStar_List.tl stack in
                        (uu____2119, uu____2128) in
                      match uu____2104 with
                      | ((env2,uu____2150),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____2214 = ts_elt in
                  (match uu____2214 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____2245 = match_dep depnames intf impl in
                       (match uu____2245 with
                        | (b,depnames') ->
                            let uu____2264 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____2264
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____2281 =
                                 let uu____2296 = FStar_List.hd st in
                                 let uu____2305 = FStar_List.tl st in
                                 (uu____2296, uu____2305) in
                               match uu____2281 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____2382 = deps_of_our_file filename in
            match uu____2382 with
            | (filenames,uu____2400,dep_graph1) ->
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
            let uu____2482 = FStar_Range.string_of_range range in
            let uu____2483 =
              FStar_TypeChecker_Normalize.term_to_string env typ in
            let uu____2484 =
              match doc1 with
              | FStar_Pervasives_Native.Some docstring ->
                  FStar_Util.format1 "#doc %s" docstring
              | FStar_Pervasives_Native.None  -> "" in
            FStar_Util.format4 "(defined at %s) %s: %s%s" uu____2482 name
              uu____2483 uu____2484
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
              let uu____2518 = shift_chunk () in
              match uu____2518 with
              | Info (symbol,fqn_only,pos_opt) ->
                  let info_at_pos_opt =
                    match pos_opt with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (file,row,col) ->
                        FStar_TypeChecker_Err.info_at_pos env file row col in
                  let info_opt =
                    match info_at_pos_opt with
                    | FStar_Pervasives_Native.Some uu____2613 ->
                        info_at_pos_opt
                    | FStar_Pervasives_Native.None  ->
                        if symbol = ""
                        then FStar_Pervasives_Native.None
                        else
                          (let lid =
                             let uu____2668 =
                               FStar_List.map FStar_Ident.id_of_text
                                 (FStar_Util.split symbol ".") in
                             FStar_Ident.lid_of_ids uu____2668 in
                           let lid1 =
                             if fqn_only
                             then lid
                             else
                               (let uu____2673 =
                                  FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid in
                                match uu____2673 with
                                | FStar_Pervasives_Native.None  -> lid
                                | FStar_Pervasives_Native.Some lid1 -> lid1) in
                           let uu____2677 =
                             FStar_TypeChecker_Env.try_lookup_lid env lid1 in
                           FStar_All.pipe_right uu____2677
                             (FStar_Util.map_option
                                (fun uu____2732  ->
                                   match uu____2732 with
                                   | ((uu____2751,typ),r) ->
                                       ((FStar_Util.Inr lid1), typ, r)))) in
                  ((match info_opt with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Util.print_string "\n#done-nok\n"
                    | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
                        let uu____2794 =
                          match name_or_lid with
                          | FStar_Util.Inl name ->
                              (name, FStar_Pervasives_Native.None)
                          | FStar_Util.Inr lid ->
                              let uu____2811 = FStar_Ident.string_of_lid lid in
                              let uu____2812 =
                                let uu____2815 =
                                  FStar_ToSyntax_Env.try_lookup_doc
                                    env.FStar_TypeChecker_Env.dsenv lid in
                                FStar_All.pipe_right uu____2815
                                  (FStar_Util.map_option
                                     FStar_Pervasives_Native.fst) in
                              (uu____2811, uu____2812) in
                        (match uu____2794 with
                         | (name,doc1) ->
                             let uu____2846 =
                               format_info env name typ rng doc1 in
                             FStar_Util.print1 "%s\n#done-ok\n" uu____2846));
                   go line_col filename stack curmod env ts)
              | Completions search_term ->
                  let rec measure_anchored_match search_term1 candidate =
                    match (search_term1, candidate) with
                    | ([],uu____2883) ->
                        FStar_Pervasives_Native.Some
                          ([], (Prims.parse_int "0"))
                    | (uu____2898,[]) -> FStar_Pervasives_Native.None
                    | (hs::ts1,hc::tc1) ->
                        let hc_text = FStar_Ident.text_of_id hc in
                        if FStar_Util.starts_with hc_text hs
                        then
                          (match ts1 with
                           | [] ->
                               FStar_Pervasives_Native.Some
                                 (candidate, (FStar_String.length hs))
                           | uu____2948 ->
                               let uu____2951 =
                                 measure_anchored_match ts1 tc1 in
                               FStar_All.pipe_right uu____2951
                                 (FStar_Util.map_option
                                    (fun uu____2991  ->
                                       match uu____2991 with
                                       | (matched,len) ->
                                           ((hc :: matched),
                                             (((FStar_String.length hc_text)
                                                 + (Prims.parse_int "1"))
                                                + len)))))
                        else FStar_Pervasives_Native.None in
                  let rec locate_match needle candidate =
                    let uu____3046 = measure_anchored_match needle candidate in
                    match uu____3046 with
                    | FStar_Pervasives_Native.Some (matched,n1) ->
                        FStar_Pervasives_Native.Some ([], matched, n1)
                    | FStar_Pervasives_Native.None  ->
                        (match candidate with
                         | [] -> FStar_Pervasives_Native.None
                         | hc::tc1 ->
                             let uu____3125 = locate_match needle tc1 in
                             FStar_All.pipe_right uu____3125
                               (FStar_Util.map_option
                                  (fun uu____3186  ->
                                     match uu____3186 with
                                     | (prefix1,matched,len) ->
                                         ((hc :: prefix1), matched, len)))) in
                  let str_of_ids ids =
                    let uu____3230 =
                      FStar_List.map FStar_Ident.text_of_id ids in
                    FStar_Util.concat_l "." uu____3230 in
                  let match_lident_against needle lident =
                    locate_match needle
                      (FStar_List.append lident.FStar_Ident.ns
                         [lident.FStar_Ident.ident]) in
                  let shorten_namespace uu____3277 =
                    match uu____3277 with
                    | (prefix1,matched,match_len) ->
                        let naked_match =
                          match matched with
                          | uu____3308::[] -> true
                          | uu____3309 -> false in
                        let uu____3312 =
                          FStar_ToSyntax_Env.shorten_module_path
                            env.FStar_TypeChecker_Env.dsenv prefix1
                            naked_match in
                        (match uu____3312 with
                         | (stripped_ns,shortened) ->
                             let uu____3339 = str_of_ids shortened in
                             let uu____3340 = str_of_ids matched in
                             let uu____3341 = str_of_ids stripped_ns in
                             (uu____3339, uu____3340, uu____3341, match_len)) in
                  let prepare_candidate uu____3359 =
                    match uu____3359 with
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
                                let uu____3487 =
                                  FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                    env.FStar_TypeChecker_Env.dsenv lid in
                                FStar_Option.map
                                  (fun fqn  ->
                                     let uu____3503 =
                                       let uu____3506 =
                                         FStar_List.map
                                           FStar_Ident.id_of_text orig_ns in
                                       FStar_List.append uu____3506
                                         [fqn.FStar_Ident.ident] in
                                     ([], uu____3503, matched_length))
                                  uu____3487
                              else FStar_Pervasives_Native.None)) in
                    let case_b_find_matches_in_env uu____3539 =
                      let matches =
                        FStar_List.filter_map (match_lident_against needle)
                          all_lidents_in_env in
                      FStar_All.pipe_right matches
                        (FStar_List.filter
                           (fun uu____3614  ->
                              match uu____3614 with
                              | (ns,id,uu____3627) ->
                                  let uu____3636 =
                                    let uu____3639 =
                                      FStar_Ident.lid_of_ids id in
                                    FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                      env.FStar_TypeChecker_Env.dsenv
                                      uu____3639 in
                                  (match uu____3636 with
                                   | FStar_Pervasives_Native.None  -> false
                                   | FStar_Pervasives_Native.Some l ->
                                       let uu____3641 =
                                         FStar_Ident.lid_of_ids
                                           (FStar_List.append ns id) in
                                       FStar_Ident.lid_equals l uu____3641))) in
                    let uu____3642 = FStar_Util.prefix needle in
                    match uu____3642 with
                    | (ns,id) ->
                        let matched_ids =
                          match ns with
                          | [] -> case_b_find_matches_in_env ()
                          | uu____3688 ->
                              let l =
                                FStar_Ident.lid_of_path ns
                                  FStar_Range.dummyRange in
                              let uu____3692 =
                                FStar_ToSyntax_Env.resolve_module_name
                                  env.FStar_TypeChecker_Env.dsenv l true in
                              (match uu____3692 with
                               | FStar_Pervasives_Native.None  ->
                                   case_b_find_matches_in_env ()
                               | FStar_Pervasives_Native.Some m ->
                                   case_a_find_transitive_includes ns m id) in
                        FStar_All.pipe_right matched_ids
                          (FStar_List.map
                             (fun x  ->
                                let uu____3757 = shorten_namespace x in
                                prepare_candidate uu____3757)) in
                  ((let uu____3767 =
                      FStar_Util.sort_with
                        (fun uu____3790  ->
                           fun uu____3791  ->
                             match (uu____3790, uu____3791) with
                             | ((cd1,ns1,uu____3818),(cd2,ns2,uu____3821)) ->
                                 (match FStar_String.compare cd1 cd2 with
                                  | _0_79 when _0_79 = (Prims.parse_int "0")
                                      -> FStar_String.compare ns1 ns2
                                  | n1 -> n1)) matches in
                    FStar_List.iter
                      (fun uu____3846  ->
                         match uu____3846 with
                         | (candidate,ns,match_len) ->
                             let uu____3856 =
                               FStar_Util.string_of_int match_len in
                             FStar_Util.print3 "%s %s %s \n" uu____3856 ns
                               candidate) uu____3767);
                   FStar_Util.print_string "#done-ok\n";
                   go line_col filename stack curmod env ts)
              | Pop msg ->
                  (pop env msg;
                   (let uu____3860 =
                      match stack with
                      | [] ->
                          (FStar_Util.print_error "too many pops";
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd1::tl1 -> (hd1, tl1) in
                    match uu____3860 with
                    | ((env1,curmod1),stack1) ->
                        go line_col filename stack1 curmod1 env1 ts))
              | Push (lax1,l,c) ->
                  let uu____3956 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____3993 =
                        update_deps filename curmod stack env ts in
                      (true, uu____3993)
                    else (false, (stack, env, ts)) in
                  (match uu____3956 with
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
                  let res = check_frag env curmod frag in
                  (match res with
                   | FStar_Pervasives_Native.Some (curmod1,env1,n_errs) ->
                       if n_errs = (Prims.parse_int "0")
                       then
                         (FStar_Util.print1 "\n%s\n" ok;
                          go line_col filename stack curmod1 env1 ts)
                       else fail5 curmod1 env1
                   | uu____4080 -> fail5 curmod env)
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    (let uu____4096 =
       let uu____4097 = FStar_Options.codegen () in
       FStar_Option.isSome uu____4097 in
     if uu____4096
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____4101 = deps_of_our_file filename in
     match uu____4101 with
     | (filenames,maybe_intf,dep_graph1) ->
         let env = FStar_Universal.init_env dep_graph1 in
         let uu____4124 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu____4124 with
          | (stack,env1,ts) ->
              let initial_range1 =
                let uu____4151 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____4152 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____4151 uu____4152 in
              let env2 = FStar_TypeChecker_Env.set_range env1 initial_range1 in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2 in
              let uu____4156 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ()) in
              if uu____4156
              then
                let uu____4157 =
                  let uu____4158 = FStar_Options.file_list () in
                  FStar_List.hd uu____4158 in
                FStar_SMTEncoding_Solver.with_hints_db uu____4157
                  (fun uu____4162  ->
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack FStar_Pervasives_Native.None env3 ts)
              else
                go ((Prims.parse_int "1"), (Prims.parse_int "0")) filename
                  stack FStar_Pervasives_Native.None env3 ts))