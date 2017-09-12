open Prims
let tc_one_file:
  Prims.string Prims.list ->
    FStar_Universal.uenv ->
      ((Prims.string FStar_Pervasives_Native.option,Prims.string)
         FStar_Pervasives_Native.tuple2,(FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
                                          FStar_Pervasives_Native.tuple2,
        Prims.string Prims.list) FStar_Pervasives_Native.tuple3
  =
  fun remaining  ->
    fun uenv  ->
      let uu____31 = uenv in
      match uu____31 with
      | (dsenv,env) ->
          let uu____52 =
            match remaining with
            | intf::impl::remaining1 when
                FStar_Universal.needs_interleaving intf impl ->
                let uu____90 =
                  FStar_Universal.tc_one_file dsenv env
                    (FStar_Pervasives_Native.Some intf) impl in
                (match uu____90 with
                 | (uu____117,dsenv1,env1) ->
                     (((FStar_Pervasives_Native.Some intf), impl), dsenv1,
                       env1, remaining1))
            | intf_or_impl::remaining1 ->
                let uu____142 =
                  FStar_Universal.tc_one_file dsenv env
                    FStar_Pervasives_Native.None intf_or_impl in
                (match uu____142 with
                 | (uu____169,dsenv1,env1) ->
                     ((FStar_Pervasives_Native.None, intf_or_impl), dsenv1,
                       env1, remaining1))
            | [] -> failwith "Impossible" in
          (match uu____52 with
           | ((intf,impl),dsenv1,env1,remaining1) ->
               ((intf, impl), (dsenv1, env1), remaining1))
let tc_prims:
  Prims.unit ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____264  ->
    let uu____265 = FStar_Universal.tc_prims () in
    match uu____265 with | (uu____280,dsenv,env) -> (dsenv, env)
type env_t =
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t,modul_t) FStar_Pervasives_Native.tuple2 Prims.list
let pop:
  'Auu____309 .
    ('Auu____309,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.string -> Prims.unit
  =
  fun uu____320  ->
    fun msg  ->
      match uu____320 with
      | (uu____326,env) ->
          (FStar_Universal.pop_context env msg; FStar_Options.pop ())
type push_kind =
  | SyntaxCheck
  | LaxCheck
  | FullCheck
let uu___is_SyntaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____333 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____338 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____343 -> false
let push:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    push_kind ->
      Prims.bool ->
        Prims.string ->
          (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2
  =
  fun uu____364  ->
    fun kind  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____364 with
          | (dsenv,tcenv) ->
              let tcenv1 =
                let uu___205_379 = tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___205_379.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___205_379.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___205_379.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___205_379.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___205_379.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___205_379.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___205_379.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___205_379.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___205_379.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___205_379.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___205_379.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___205_379.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___205_379.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___205_379.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___205_379.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___205_379.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___205_379.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___205_379.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = (kind = LaxCheck);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___205_379.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___205_379.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___205_379.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.type_of =
                    (uu___205_379.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___205_379.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___205_379.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___205_379.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___205_379.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___205_379.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___205_379.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___205_379.FStar_TypeChecker_Env.identifier_info)
                } in
              let dsenv1 =
                FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck) in
              let res = FStar_Universal.push_context (dsenv1, tcenv1) msg in
              (FStar_Options.push ();
               if restore_cmd_line_options1
               then
                 (let uu____388 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____388 FStar_Pervasives.ignore)
               else ();
               res)
let mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____401  ->
    match uu____401 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.mark dsenv in
        let env1 = FStar_TypeChecker_Env.mark env in
        (FStar_Options.push (); (dsenv1, env1))
let reset_mark:
  'Auu____419 .
    ('Auu____419,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____431  ->
    match uu____431 with
    | (uu____436,env) ->
        let dsenv = FStar_ToSyntax_Env.reset_mark () in
        let env1 = FStar_TypeChecker_Env.reset_mark env in
        (FStar_Options.pop (); (dsenv, env1))
let cleanup:
  'Auu____445 .
    ('Auu____445,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.unit
  =
  fun uu____453  ->
    match uu____453 with
    | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
let commit_mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____471  ->
    match uu____471 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.commit_mark dsenv in
        let env1 = FStar_TypeChecker_Env.commit_mark env in (dsenv1, env1)
let check_frag:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
      (FStar_Parser_ParseIt.input_frag,Prims.bool)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,(FStar_ToSyntax_Env.env,
                                                                    FStar_TypeChecker_Env.env)
                                                                    FStar_Pervasives_Native.tuple2,
          Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option
  =
  fun uu____517  ->
    fun curmod  ->
      fun frag  ->
        match uu____517 with
        | (dsenv,env) ->
            (try
               let uu____581 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag in
               match uu____581 with
               | FStar_Pervasives_Native.Some (m,dsenv1,env1) ->
                   let uu____621 =
                     let uu____634 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____634) in
                   FStar_Pervasives_Native.Some uu____621
               | uu____653 -> FStar_Pervasives_Native.None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____697 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____697 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____720 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____720 ->
                 ((let uu____722 =
                     let uu____729 =
                       let uu____734 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____734) in
                     [uu____729] in
                   FStar_TypeChecker_Err.add_errors env uu____722);
                  FStar_Pervasives_Native.None))
let deps_of_our_file:
  Prims.string ->
    (Prims.string Prims.list,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename] in
    let uu____770 =
      FStar_List.partition
        (fun x  ->
           let uu____783 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____784 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____783 <> uu____784) deps in
    match uu____770 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____811 =
                  (let uu____814 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____814) ||
                    (let uu____816 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____816) in
                if uu____811
                then
                  let uu____817 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____817
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____820 ->
              ((let uu____824 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____824);
               FStar_Pervasives_Native.None) in
        (deps1, maybe_intf)
type m_timestamps =
  (Prims.string FStar_Pervasives_Native.option,Prims.string,FStar_Util.time
                                                              FStar_Pervasives_Native.option,
    FStar_Util.time) FStar_Pervasives_Native.tuple4 Prims.list
let rec tc_deps:
  modul_t ->
    stack_t ->
      env_t ->
        Prims.string Prims.list ->
          m_timestamps ->
            (stack_t,env_t,m_timestamps) FStar_Pervasives_Native.tuple3
  =
  fun m  ->
    fun stack  ->
      fun env  ->
        fun remaining  ->
          fun ts  ->
            match remaining with
            | [] -> (stack, env, ts)
            | uu____879 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____898 =
                    let uu____899 = FStar_Options.lax () in
                    if uu____899 then LaxCheck else FullCheck in
                  push env uu____898 true "typecheck_modul" in
                let uu____901 = tc_one_file remaining env1 in
                (match uu____901 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____952 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____965 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____965
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____952 with
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
                 | (uu____1069,uu____1070) ->
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
                     | uu____1165 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1193 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1276::ts3 ->
                    (pop env1 "";
                     (let uu____1317 =
                        let uu____1332 = FStar_List.hd stack in
                        let uu____1341 = FStar_List.tl stack in
                        (uu____1332, uu____1341) in
                      match uu____1317 with
                      | ((env2,uu____1367),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1431 = ts_elt in
                  (match uu____1431 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1462 = match_dep depnames intf impl in
                       (match uu____1462 with
                        | (b,depnames') ->
                            let uu____1481 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1481
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1502 =
                                 let uu____1517 = FStar_List.hd st in
                                 let uu____1526 = FStar_List.tl st in
                                 (uu____1517, uu____1526) in
                               match uu____1502 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1603 = deps_of_our_file filename in
            match uu____1603 with
            | (filenames,uu____1619) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___195_1679  ->
    match uu___195_1679 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1683 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1683
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1685 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1688 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1706 -> true
    | uu____1711 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1727 -> uu____1727
let js_fail: 'Auu____1738 . Prims.string -> FStar_Util.json -> 'Auu____1738 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___196_1750  ->
    match uu___196_1750 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___197_1756  ->
    match uu___197_1756 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list:
  'Auu____1765 .
    (FStar_Util.json -> 'Auu____1765) ->
      FStar_Util.json -> 'Auu____1765 Prims.list
  =
  fun k  ->
    fun uu___198_1778  ->
      match uu___198_1778 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___199_1796  ->
    match uu___199_1796 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1821 = js_str s in
    match uu____1821 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1822 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1827 = js_str s in
    match uu____1827 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | uu____1828 -> js_fail "reduction rule" s
type query' =
  | Exit
  | DescribeProtocol
  | DescribeRepl
  | Pop
  | Push of (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
  FStar_Pervasives_Native.tuple5
  | AutoComplete of Prims.string
  | Lookup of
  (Prims.string,(Prims.string,Prims.int,Prims.int)
                  FStar_Pervasives_Native.tuple3
                  FStar_Pervasives_Native.option,Prims.string Prims.list)
  FStar_Pervasives_Native.tuple3
  | Compute of
  (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                  FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | Search of Prims.string
  | MissingCurrentModule
  | ProtocolViolation of Prims.string
and query = {
  qq: query';
  qid: Prims.string;}
let uu___is_Exit: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1899 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1904 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1909 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1914 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1930 -> false
let __proj__Push__item___0:
  query' ->
    (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1974 -> false
let __proj__AutoComplete__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2004 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,(Prims.string,Prims.int,Prims.int)
                    FStar_Pervasives_Native.tuple3
                    FStar_Pervasives_Native.option,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2074 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2112 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_MissingCurrentModule: query' -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MissingCurrentModule  -> true
    | uu____2125 -> false
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2131 -> false
let __proj__ProtocolViolation__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0
let __proj__Mkquery__item__qq: query -> query' =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qq
let __proj__Mkquery__item__qid: query -> Prims.string =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qid
let query_needs_current_module: query' -> Prims.bool =
  fun uu___200_2155  ->
    match uu___200_2155 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Pop  -> false
    | Push uu____2156 -> false
    | MissingCurrentModule  -> false
    | ProtocolViolation uu____2167 -> false
    | AutoComplete uu____2168 -> true
    | Lookup uu____2169 -> true
    | Compute uu____2186 -> true
    | Search uu____2195 -> true
let interactive_protocol_vernum: Prims.int = Prims.parse_int "2"
let interactive_protocol_features: Prims.string Prims.list =
  ["autocomplete";
  "compute";
  "describe-protocol";
  "describe-repl";
  "exit";
  "lookup";
  "lookup/documentation";
  "lookup/definition";
  "pop";
  "peek";
  "push";
  "search"]
exception InvalidQuery of Prims.string
let uu___is_InvalidQuery: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____2205 -> true
    | uu____2206 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2214 -> uu____2214
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2219 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2224 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2229 -> false
let try_assoc:
  'Auu____2238 'Auu____2239 .
    'Auu____2239 ->
      ('Auu____2239,'Auu____2238) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2238 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2262 =
        FStar_Util.try_find
          (fun uu____2276  ->
             match uu____2276 with | (k,uu____2282) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2262
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2299 =
          let uu____2300 =
            let uu____2301 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2301 in
          ProtocolViolation uu____2300 in
        { qq = uu____2299; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2328 = try_assoc key a in
      match uu____2328 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2332 =
            let uu____2333 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____2333 in
          FStar_Exn.raise uu____2332 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____2348 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2348 js_str in
    try
      let query =
        let uu____2357 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____2357 js_str in
      let args =
        let uu____2365 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____2365 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____2382 = try_assoc k args in
        match uu____2382 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____2390 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____2391 =
              let uu____2402 =
                let uu____2403 = arg "kind" in
                FStar_All.pipe_right uu____2403 js_pushkind in
              let uu____2404 =
                let uu____2405 = arg "code" in
                FStar_All.pipe_right uu____2405 js_str in
              let uu____2406 =
                let uu____2407 = arg "line" in
                FStar_All.pipe_right uu____2407 js_int in
              let uu____2408 =
                let uu____2409 = arg "column" in
                FStar_All.pipe_right uu____2409 js_int in
              (uu____2402, uu____2404, uu____2406, uu____2408,
                (query = "peek")) in
            Push uu____2391
        | "push" ->
            let uu____2410 =
              let uu____2421 =
                let uu____2422 = arg "kind" in
                FStar_All.pipe_right uu____2422 js_pushkind in
              let uu____2423 =
                let uu____2424 = arg "code" in
                FStar_All.pipe_right uu____2424 js_str in
              let uu____2425 =
                let uu____2426 = arg "line" in
                FStar_All.pipe_right uu____2426 js_int in
              let uu____2427 =
                let uu____2428 = arg "column" in
                FStar_All.pipe_right uu____2428 js_int in
              (uu____2421, uu____2423, uu____2425, uu____2427,
                (query = "peek")) in
            Push uu____2410
        | "autocomplete" ->
            let uu____2429 =
              let uu____2430 = arg "partial-symbol" in
              FStar_All.pipe_right uu____2430 js_str in
            AutoComplete uu____2429
        | "lookup" ->
            let uu____2431 =
              let uu____2448 =
                let uu____2449 = arg "symbol" in
                FStar_All.pipe_right uu____2449 js_str in
              let uu____2450 =
                let uu____2459 =
                  let uu____2468 = try_arg "location" in
                  FStar_All.pipe_right uu____2468
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____2459
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____2526 =
                          let uu____2527 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____2527 js_str in
                        let uu____2528 =
                          let uu____2529 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____2529 js_int in
                        let uu____2530 =
                          let uu____2531 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____2531 js_int in
                        (uu____2526, uu____2528, uu____2530))) in
              let uu____2532 =
                let uu____2535 = arg "requested-info" in
                FStar_All.pipe_right uu____2535 (js_list js_str) in
              (uu____2448, uu____2450, uu____2532) in
            Lookup uu____2431
        | "compute" ->
            let uu____2548 =
              let uu____2557 =
                let uu____2558 = arg "term" in
                FStar_All.pipe_right uu____2558 js_str in
              let uu____2559 =
                let uu____2564 = try_arg "rules" in
                FStar_All.pipe_right uu____2564
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____2557, uu____2559) in
            Compute uu____2548
        | "search" ->
            let uu____2579 =
              let uu____2580 = arg "terms" in
              FStar_All.pipe_right uu____2580 js_str in
            Search uu____2579
        | uu____2581 ->
            let uu____2582 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____2582 in
      { qq = uu____2390; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____2596 = FStar_Util.read_line stream in
      match uu____2596 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some line ->
          let uu____2600 = FStar_Util.json_of_string line in
          (match uu____2600 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               unpack_interactive_query request)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let rec json_of_fstar_option: FStar_Options.option_val -> FStar_Util.json =
  fun uu___201_2613  ->
    match uu___201_2613 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____2621 = FStar_List.map json_of_fstar_option vs in
        FStar_Util.JsonList uu____2621
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let json_of_opt:
  'Auu____2630 .
    ('Auu____2630 -> FStar_Util.json) ->
      'Auu____2630 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____2648 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____2648
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____2655 =
      let uu____2658 =
        let uu____2659 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____2659 in
      let uu____2660 =
        let uu____2663 =
          let uu____2664 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____2664 in
        [uu____2663] in
      uu____2658 :: uu____2660 in
    FStar_Util.JsonList uu____2655
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____2677 =
          let uu____2684 =
            let uu____2691 =
              let uu____2696 = json_of_pos b in ("beg", uu____2696) in
            let uu____2697 =
              let uu____2704 =
                let uu____2709 = json_of_pos e in ("end", uu____2709) in
              [uu____2704] in
            uu____2691 :: uu____2697 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____2684 in
        FStar_Util.JsonAssoc uu____2677
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2730 = FStar_Range.file_of_use_range r in
    let uu____2731 = FStar_Range.start_of_use_range r in
    let uu____2732 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____2730 uu____2731 uu____2732
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2737 = FStar_Range.file_of_range r in
    let uu____2738 = FStar_Range.start_of_range r in
    let uu____2739 = FStar_Range.end_of_range r in
    json_of_range_fields uu____2737 uu____2738 uu____2739
let json_of_issue_level: FStar_Errors.issue_level -> FStar_Util.json =
  fun i  ->
    FStar_Util.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented  -> "not-implemented"
       | FStar_Errors.EInfo  -> "info"
       | FStar_Errors.EWarning  -> "warning"
       | FStar_Errors.EError  -> "error")
let json_of_issue: FStar_Errors.issue -> FStar_Util.json =
  fun issue  ->
    let uu____2748 =
      let uu____2755 =
        let uu____2762 =
          let uu____2769 =
            let uu____2774 =
              let uu____2775 =
                let uu____2778 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____2784 = json_of_use_range r in [uu____2784] in
                let uu____2785 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____2791 = json_of_def_range r in [uu____2791]
                  | uu____2792 -> [] in
                FStar_List.append uu____2778 uu____2785 in
              FStar_Util.JsonList uu____2775 in
            ("ranges", uu____2774) in
          [uu____2769] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____2762 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____2755 in
    FStar_Util.JsonAssoc uu____2748
type lookup_result =
  {
  lr_name: Prims.string;
  lr_def_range: FStar_Range.range FStar_Pervasives_Native.option;
  lr_typ: Prims.string FStar_Pervasives_Native.option;
  lr_doc: Prims.string FStar_Pervasives_Native.option;
  lr_def: Prims.string FStar_Pervasives_Native.option;}
let __proj__Mklookup_result__item__lr_name: lookup_result -> Prims.string =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_name
let __proj__Mklookup_result__item__lr_def_range:
  lookup_result -> FStar_Range.range FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_def_range
let __proj__Mklookup_result__item__lr_typ:
  lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_typ
let __proj__Mklookup_result__item__lr_doc:
  lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_doc
let __proj__Mklookup_result__item__lr_def:
  lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_def
let json_of_lookup_result: lookup_result -> FStar_Util.json =
  fun lr  ->
    let uu____2944 =
      let uu____2951 =
        let uu____2958 =
          let uu____2963 = json_of_opt json_of_def_range lr.lr_def_range in
          ("defined-at", uu____2963) in
        let uu____2964 =
          let uu____2971 =
            let uu____2976 =
              json_of_opt (fun _0_42  -> FStar_Util.JsonStr _0_42) lr.lr_typ in
            ("type", uu____2976) in
          let uu____2977 =
            let uu____2984 =
              let uu____2989 =
                json_of_opt (fun _0_43  -> FStar_Util.JsonStr _0_43)
                  lr.lr_doc in
              ("documentation", uu____2989) in
            let uu____2990 =
              let uu____2997 =
                let uu____3002 =
                  json_of_opt (fun _0_44  -> FStar_Util.JsonStr _0_44)
                    lr.lr_def in
                ("definition", uu____3002) in
              [uu____2997] in
            uu____2984 :: uu____2990 in
          uu____2971 :: uu____2977 in
        uu____2958 :: uu____2964 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____2951 in
    FStar_Util.JsonAssoc uu____2944
let json_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3035 =
      FStar_List.map (fun _0_45  -> FStar_Util.JsonStr _0_45)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_46  -> FStar_Util.JsonList _0_46) uu____3035 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____3057 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____3057);
    FStar_Util.print_raw "\n"
let write_response:
  Prims.string -> query_status -> FStar_Util.json -> Prims.unit =
  fun qid  ->
    fun status  ->
      fun response  ->
        let qid1 = FStar_Util.JsonStr qid in
        let status1 =
          match status with
          | QueryOK  -> FStar_Util.JsonStr "success"
          | QueryNOK  -> FStar_Util.JsonStr "failure"
          | QueryViolatesProtocol  -> FStar_Util.JsonStr "protocol-violation" in
        write_json
          (FStar_Util.JsonAssoc
             [("kind", (FStar_Util.JsonStr "response"));
             ("query-id", qid1);
             ("status", status1);
             ("response", response)])
let write_message: Prims.string -> FStar_Util.json -> Prims.unit =
  fun level  ->
    fun contents  ->
      write_json
        (FStar_Util.JsonAssoc
           [("kind", (FStar_Util.JsonStr "message"));
           ("level", (FStar_Util.JsonStr level));
           ("contents", contents)])
let write_hello: Prims.unit -> Prims.unit =
  fun uu____3119  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____3122 =
        FStar_List.map (fun _0_47  -> FStar_Util.JsonStr _0_47)
          interactive_protocol_features in
      FStar_Util.JsonList uu____3122 in
    write_json
      (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info"))
         :: json_of_protocol_info))
type repl_state =
  {
  repl_line: Prims.int;
  repl_column: Prims.int;
  repl_fname: Prims.string;
  repl_stack: stack_t;
  repl_curmod: modul_t;
  repl_env: env_t;
  repl_ts: m_timestamps;
  repl_stdin: FStar_Util.stream_reader;}
let __proj__Mkrepl_state__item__repl_line: repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_line
let __proj__Mkrepl_state__item__repl_column: repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_column
let __proj__Mkrepl_state__item__repl_fname: repl_state -> Prims.string =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_fname
let __proj__Mkrepl_state__item__repl_stack: repl_state -> stack_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_stack
let __proj__Mkrepl_state__item__repl_curmod: repl_state -> modul_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_curmod
let __proj__Mkrepl_state__item__repl_env: repl_state -> env_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_env
let __proj__Mkrepl_state__item__repl_ts: repl_state -> m_timestamps =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_ts
let __proj__Mkrepl_state__item__repl_stdin:
  repl_state -> FStar_Util.stream_reader =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_stdin
let json_of_repl_state:
  repl_state ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun st  ->
    let opts_and_defaults =
      let opt_docs =
        let uu____3283 = FStar_Options.docs () in
        FStar_Util.smap_of_list uu____3283 in
      let get_doc k = FStar_Util.smap_try_find opt_docs k in
      FStar_List.map
        (fun uu____3315  ->
           match uu____3315 with
           | (k,v1) ->
               let uu____3332 = FStar_Options.get_option k in
               let uu____3333 = get_doc k in (k, uu____3332, uu____3333, v1))
        FStar_Options.defaults in
    let uu____3338 =
      let uu____3343 =
        let uu____3344 =
          FStar_List.map
            (fun uu____3364  ->
               match uu____3364 with
               | (uu____3377,fstname,uu____3379,uu____3380) ->
                   FStar_Util.JsonStr fstname) st.repl_ts in
        FStar_Util.JsonList uu____3344 in
      ("loaded-dependencies", uu____3343) in
    let uu____3389 =
      let uu____3396 =
        let uu____3401 =
          let uu____3402 =
            FStar_List.map
              (fun uu____3421  ->
                 match uu____3421 with
                 | (name,value,doc1,dflt1) ->
                     let uu____3440 =
                       let uu____3447 =
                         let uu____3454 =
                           let uu____3459 = json_of_fstar_option value in
                           ("value", uu____3459) in
                         let uu____3460 =
                           let uu____3467 =
                             let uu____3472 = json_of_fstar_option dflt1 in
                             ("default", uu____3472) in
                           let uu____3473 =
                             let uu____3480 =
                               let uu____3485 =
                                 json_of_opt
                                   (fun _0_48  -> FStar_Util.JsonStr _0_48)
                                   doc1 in
                               ("documentation", uu____3485) in
                             [uu____3480] in
                           uu____3467 :: uu____3473 in
                         uu____3454 :: uu____3460 in
                       ("name", (FStar_Util.JsonStr name)) :: uu____3447 in
                     FStar_Util.JsonAssoc uu____3440) opts_and_defaults in
          FStar_Util.JsonList uu____3402 in
        ("options", uu____3401) in
      [uu____3396] in
    uu____3338 :: uu____3389
let with_printed_effect_args:
  'Auu____3522 . (Prims.unit -> 'Auu____3522) -> 'Auu____3522 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____3534  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____3545  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
let sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____3551  -> FStar_Syntax_Print.sigelt_to_string se)
let run_exit:
  'Auu____3558 'Auu____3559 .
    'Auu____3559 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3558,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol:
  'Auu____3590 'Auu____3591 .
    'Auu____3591 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3591,'Auu____3590) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl:
  'Auu____3620 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____3620) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____3637 =
      let uu____3642 =
        let uu____3643 = json_of_repl_state st in
        FStar_Util.JsonAssoc uu____3643 in
      (QueryOK, uu____3642) in
    (uu____3637, (FStar_Util.Inl st))
let run_protocol_violation:
  'Auu____3666 'Auu____3667 .
    'Auu____3667 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____3667,'Auu____3666) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_missing_current_module:
  'Auu____3706 'Auu____3707 'Auu____3708 .
    'Auu____3708 ->
      'Auu____3707 ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____3708,'Auu____3706) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr "Current module unset")),
        (FStar_Util.Inl st))
let nothing_left_to_pop: repl_state -> Prims.bool =
  fun st  ->
    (FStar_List.length st.repl_stack) <= (FStar_List.length st.repl_ts)
let run_pop:
  'Auu____3761 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____3761) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    if nothing_left_to_pop st
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (match st.repl_stack with
       | [] -> failwith "impossible"
       | (env,curmod)::stack ->
           (pop st.repl_env "#pop";
            (let st' =
               let uu___212_3830 = st in
               {
                 repl_line = (uu___212_3830.repl_line);
                 repl_column = (uu___212_3830.repl_column);
                 repl_fname = (uu___212_3830.repl_fname);
                 repl_stack = stack;
                 repl_curmod = curmod;
                 repl_env = env;
                 repl_ts = (uu___212_3830.repl_ts);
                 repl_stdin = (uu___212_3830.repl_stdin)
               } in
             if nothing_left_to_pop st' then cleanup env else ();
             ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))))
let run_push:
  'Auu____3855 .
    repl_state ->
      push_kind ->
        Prims.string ->
          Prims.int ->
            Prims.int ->
              Prims.bool ->
                ((query_status,FStar_Util.json)
                   FStar_Pervasives_Native.tuple2,(repl_state,'Auu____3855)
                                                    FStar_Util.either)
                  FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun kind  ->
      fun text1  ->
        fun line  ->
          fun column  ->
            fun peek_only  ->
              let uu____3892 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
              match uu____3892 with
              | (stack,env,ts) ->
                  let uu____3914 =
                    if nothing_left_to_pop st
                    then
                      let uu____3935 =
                        update_deps st.repl_fname st.repl_curmod stack env ts in
                      (true, uu____3935)
                    else (false, (stack, env, ts)) in
                  (match uu____3914 with
                   | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
                       let stack2 = (env1, (st.repl_curmod)) :: stack1 in
                       let env2 =
                         push env1 kind restore_cmd_line_options1 "#push" in
                       let env_mark = mark env2 in
                       let frag =
                         {
                           FStar_Parser_ParseIt.frag_text = text1;
                           FStar_Parser_ParseIt.frag_line = line;
                           FStar_Parser_ParseIt.frag_col = column
                         } in
                       let res =
                         check_frag env_mark st.repl_curmod (frag, false) in
                       let errors =
                         let uu____4017 = FStar_Errors.report_all () in
                         FStar_All.pipe_right uu____4017
                           (FStar_List.map json_of_issue) in
                       (FStar_Errors.clear ();
                        (let st' =
                           let uu___213_4026 = st in
                           {
                             repl_line = line;
                             repl_column = column;
                             repl_fname = (uu___213_4026.repl_fname);
                             repl_stack = stack2;
                             repl_curmod = (uu___213_4026.repl_curmod);
                             repl_env = (uu___213_4026.repl_env);
                             repl_ts = ts1;
                             repl_stdin = (uu___213_4026.repl_stdin)
                           } in
                         match res with
                         | FStar_Pervasives_Native.Some (curmod,env3,nerrs)
                             when
                             (nerrs = (Prims.parse_int "0")) &&
                               (peek_only = false)
                             ->
                             let env4 = commit_mark env3 in
                             ((QueryOK, (FStar_Util.JsonList errors)),
                               (FStar_Util.Inl
                                  (let uu___214_4080 = st' in
                                   {
                                     repl_line = (uu___214_4080.repl_line);
                                     repl_column =
                                       (uu___214_4080.repl_column);
                                     repl_fname = (uu___214_4080.repl_fname);
                                     repl_stack = (uu___214_4080.repl_stack);
                                     repl_curmod = curmod;
                                     repl_env = env4;
                                     repl_ts = (uu___214_4080.repl_ts);
                                     repl_stdin = (uu___214_4080.repl_stdin)
                                   })))
                         | uu____4081 ->
                             let env3 = reset_mark env_mark in
                             let uu____4101 =
                               run_pop
                                 (let uu___215_4115 = st' in
                                  {
                                    repl_line = (uu___215_4115.repl_line);
                                    repl_column = (uu___215_4115.repl_column);
                                    repl_fname = (uu___215_4115.repl_fname);
                                    repl_stack = (uu___215_4115.repl_stack);
                                    repl_curmod = (uu___215_4115.repl_curmod);
                                    repl_env = env3;
                                    repl_ts = (uu___215_4115.repl_ts);
                                    repl_stdin = (uu___215_4115.repl_stdin)
                                  }) in
                             (match uu____4101 with
                              | (uu____4128,st'') ->
                                  let status =
                                    if peek_only then QueryOK else QueryNOK in
                                  ((status, (FStar_Util.JsonList errors)),
                                    st'')))))
let run_lookup:
  'Auu____4166 .
    repl_state ->
      Prims.string ->
        (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option ->
          Prims.string Prims.list ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____4166) FStar_Util.either)
              FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____4215 = st.repl_env in
          match uu____4215 with
          | (dsenv,tcenv) ->
              let info_of_lid_str lid_str =
                let lid =
                  let uu____4247 =
                    FStar_List.map FStar_Ident.id_of_text
                      (FStar_Util.split lid_str ".") in
                  FStar_Ident.lid_of_ids uu____4247 in
                let lid1 =
                  let uu____4251 =
                    FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                      lid in
                  FStar_All.pipe_left (FStar_Util.dflt lid) uu____4251 in
                let uu____4256 =
                  FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
                FStar_All.pipe_right uu____4256
                  (FStar_Util.map_option
                     (fun uu____4311  ->
                        match uu____4311 with
                        | ((uu____4330,typ),r) ->
                            ((FStar_Util.Inr lid1), typ, r))) in
              let docs_of_lid lid =
                let uu____4347 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
                FStar_All.pipe_right uu____4347
                  (FStar_Util.map_option FStar_Pervasives_Native.fst) in
              let def_of_lid lid =
                let uu____4376 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
                FStar_Util.bind_opt uu____4376
                  (fun uu___202_4420  ->
                     match uu___202_4420 with
                     | (FStar_Util.Inr (se,uu____4442),uu____4443) ->
                         let uu____4472 = sigelt_to_string se in
                         FStar_Pervasives_Native.Some uu____4472
                     | uu____4473 -> FStar_Pervasives_Native.None) in
              let info_at_pos_opt =
                FStar_Util.bind_opt pos_opt
                  (fun uu____4525  ->
                     match uu____4525 with
                     | (file,row,col) ->
                         FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
              let info_opt =
                match info_at_pos_opt with
                | FStar_Pervasives_Native.Some uu____4572 -> info_at_pos_opt
                | FStar_Pervasives_Native.None  ->
                    if symbol = ""
                    then FStar_Pervasives_Native.None
                    else info_of_lid_str symbol in
              let response =
                match info_opt with
                | FStar_Pervasives_Native.None  ->
                    (QueryNOK, FStar_Util.JsonNull)
                | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
                    let name =
                      match name_or_lid with
                      | FStar_Util.Inl name -> name
                      | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid in
                    let typ_str =
                      if FStar_List.mem "type" requested_info
                      then
                        let uu____4674 = term_to_string tcenv typ in
                        FStar_Pervasives_Native.Some uu____4674
                      else FStar_Pervasives_Native.None in
                    let doc_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "documentation" requested_info ->
                          docs_of_lid lid
                      | uu____4682 -> FStar_Pervasives_Native.None in
                    let def_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "definition" requested_info ->
                          def_of_lid lid
                      | uu____4693 -> FStar_Pervasives_Native.None in
                    let def_range =
                      if FStar_List.mem "defined-at" requested_info
                      then FStar_Pervasives_Native.Some rng
                      else FStar_Pervasives_Native.None in
                    let result =
                      {
                        lr_name = name;
                        lr_def_range = def_range;
                        lr_typ = typ_str;
                        lr_doc = doc_str;
                        lr_def = def_str
                      } in
                    let uu____4705 = json_of_lookup_result result in
                    (QueryOK, uu____4705) in
              (response, (FStar_Util.Inl st))
let run_completions:
  'Auu____4720 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4720) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      let uu____4741 = st.repl_env in
      match uu____4741 with
      | (dsenv,tcenv) ->
          let rec measure_anchored_match search_term1 candidate =
            match (search_term1, candidate) with
            | ([],uu____4791) ->
                FStar_Pervasives_Native.Some ([], (Prims.parse_int "0"))
            | (uu____4806,[]) -> FStar_Pervasives_Native.None
            | (hs::ts,hc::tc) ->
                let hc_text = FStar_Ident.text_of_id hc in
                if FStar_Util.starts_with hc_text hs
                then
                  (match ts with
                   | [] ->
                       FStar_Pervasives_Native.Some
                         (candidate, (FStar_String.length hs))
                   | uu____4856 ->
                       let uu____4859 = measure_anchored_match ts tc in
                       FStar_All.pipe_right uu____4859
                         (FStar_Util.map_option
                            (fun uu____4899  ->
                               match uu____4899 with
                               | (matched,len) ->
                                   ((hc :: matched),
                                     (((FStar_String.length hc_text) +
                                         (Prims.parse_int "1"))
                                        + len)))))
                else FStar_Pervasives_Native.None in
          let rec locate_match needle candidate =
            let uu____4954 = measure_anchored_match needle candidate in
            match uu____4954 with
            | FStar_Pervasives_Native.Some (matched,n1) ->
                FStar_Pervasives_Native.Some ([], matched, n1)
            | FStar_Pervasives_Native.None  ->
                (match candidate with
                 | [] -> FStar_Pervasives_Native.None
                 | hc::tc ->
                     let uu____5033 = locate_match needle tc in
                     FStar_All.pipe_right uu____5033
                       (FStar_Util.map_option
                          (fun uu____5094  ->
                             match uu____5094 with
                             | (prefix1,matched,len) ->
                                 ((hc :: prefix1), matched, len)))) in
          let str_of_ids ids =
            let uu____5138 = FStar_List.map FStar_Ident.text_of_id ids in
            FStar_Util.concat_l "." uu____5138 in
          let match_lident_against needle lident =
            locate_match needle
              (FStar_List.append lident.FStar_Ident.ns
                 [lident.FStar_Ident.ident]) in
          let shorten_namespace uu____5185 =
            match uu____5185 with
            | (prefix1,matched,match_len) ->
                let naked_match =
                  match matched with
                  | uu____5216::[] -> true
                  | uu____5217 -> false in
                let uu____5220 =
                  FStar_ToSyntax_Env.shorten_module_path dsenv prefix1
                    naked_match in
                (match uu____5220 with
                 | (stripped_ns,shortened) ->
                     let uu____5247 = str_of_ids shortened in
                     let uu____5248 = str_of_ids matched in
                     let uu____5249 = str_of_ids stripped_ns in
                     (uu____5247, uu____5248, uu____5249, match_len)) in
          let prepare_candidate uu____5267 =
            match uu____5267 with
            | (prefix1,matched,stripped_ns,match_len) ->
                if prefix1 = ""
                then (matched, stripped_ns, match_len)
                else
                  ((Prims.strcat prefix1 (Prims.strcat "." matched)),
                    stripped_ns,
                    (((FStar_String.length prefix1) + match_len) +
                       (Prims.parse_int "1"))) in
          let needle = FStar_Util.split search_term "." in
          let all_lidents_in_env = FStar_TypeChecker_Env.lidents tcenv in
          let matches =
            let case_a_find_transitive_includes orig_ns m id =
              let exported_names =
                FStar_ToSyntax_Env.transitive_exported_ids dsenv m in
              let matched_length =
                FStar_List.fold_left
                  (fun out  ->
                     fun s  ->
                       ((FStar_String.length s) + out) +
                         (Prims.parse_int "1")) (FStar_String.length id)
                  orig_ns in
              FStar_All.pipe_right exported_names
                (FStar_List.filter_map
                   (fun n1  ->
                      if FStar_Util.starts_with n1 id
                      then
                        let lid =
                          FStar_Ident.lid_of_ns_and_id
                            (FStar_Ident.ids_of_lid m)
                            (FStar_Ident.id_of_text n1) in
                        let uu____5395 =
                          FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                            dsenv lid in
                        FStar_Option.map
                          (fun fqn  ->
                             let uu____5411 =
                               let uu____5414 =
                                 FStar_List.map FStar_Ident.id_of_text
                                   orig_ns in
                               FStar_List.append uu____5414
                                 [fqn.FStar_Ident.ident] in
                             ([], uu____5411, matched_length)) uu____5395
                      else FStar_Pervasives_Native.None)) in
            let case_b_find_matches_in_env uu____5447 =
              let matches =
                FStar_List.filter_map (match_lident_against needle)
                  all_lidents_in_env in
              FStar_All.pipe_right matches
                (FStar_List.filter
                   (fun uu____5522  ->
                      match uu____5522 with
                      | (ns,id,uu____5535) ->
                          let uu____5544 =
                            let uu____5547 = FStar_Ident.lid_of_ids id in
                            FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                              dsenv uu____5547 in
                          (match uu____5544 with
                           | FStar_Pervasives_Native.None  -> false
                           | FStar_Pervasives_Native.Some l ->
                               let uu____5549 =
                                 FStar_Ident.lid_of_ids
                                   (FStar_List.append ns id) in
                               FStar_Ident.lid_equals l uu____5549))) in
            let uu____5550 = FStar_Util.prefix needle in
            match uu____5550 with
            | (ns,id) ->
                let matched_ids =
                  match ns with
                  | [] -> case_b_find_matches_in_env ()
                  | uu____5596 ->
                      let l =
                        FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
                      let uu____5600 =
                        FStar_ToSyntax_Env.resolve_module_name dsenv l true in
                      (match uu____5600 with
                       | FStar_Pervasives_Native.None  ->
                           case_b_find_matches_in_env ()
                       | FStar_Pervasives_Native.Some m ->
                           case_a_find_transitive_includes ns m id) in
                FStar_All.pipe_right matched_ids
                  (FStar_List.map
                     (fun x  ->
                        let uu____5665 = shorten_namespace x in
                        prepare_candidate uu____5665)) in
          let json_candidates =
            let uu____5677 =
              FStar_Util.sort_with
                (fun uu____5700  ->
                   fun uu____5701  ->
                     match (uu____5700, uu____5701) with
                     | ((cd1,ns1,uu____5728),(cd2,ns2,uu____5731)) ->
                         (match FStar_String.compare cd1 cd2 with
                          | _0_49 when _0_49 = (Prims.parse_int "0") ->
                              FStar_String.compare ns1 ns2
                          | n1 -> n1)) matches in
            FStar_List.map
              (fun uu____5755  ->
                 match uu____5755 with
                 | (candidate,ns,match_len) ->
                     FStar_Util.JsonList
                       [FStar_Util.JsonInt match_len;
                       FStar_Util.JsonStr ns;
                       FStar_Util.JsonStr candidate]) uu____5677 in
          ((QueryOK, (FStar_Util.JsonList json_candidates)),
            (FStar_Util.Inl st))
let run_compute:
  'Auu____5781 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____5781) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun term  ->
      fun rules  ->
        let run_and_rewind st1 task =
          let env_mark = mark st1.repl_env in
          let results = task st1 in
          let env = reset_mark env_mark in
          let st' =
            let uu___216_5862 = st1 in
            {
              repl_line = (uu___216_5862.repl_line);
              repl_column = (uu___216_5862.repl_column);
              repl_fname = (uu___216_5862.repl_fname);
              repl_stack = (uu___216_5862.repl_stack);
              repl_curmod = (uu___216_5862.repl_curmod);
              repl_env = env;
              repl_ts = (uu___216_5862.repl_ts);
              repl_stdin = (uu___216_5862.repl_stdin)
            } in
          (results, (FStar_Util.Inl st')) in
        let dummy_let_fragment term1 =
          let dummy_decl =
            FStar_Util.format1 "let __compute_dummy__ = (%s)" term1 in
          {
            FStar_Parser_ParseIt.frag_text = dummy_decl;
            FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0");
            FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
          } in
        let normalize_term1 tcenv rules1 t =
          FStar_TypeChecker_Normalize.normalize rules1 tcenv t in
        let find_let_body ses =
          match ses with
          | {
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                ((uu____5902,{ FStar_Syntax_Syntax.lbname = uu____5903;
                               FStar_Syntax_Syntax.lbunivs = uu____5904;
                               FStar_Syntax_Syntax.lbtyp = uu____5905;
                               FStar_Syntax_Syntax.lbeff = uu____5906;
                               FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____5908);
              FStar_Syntax_Syntax.sigrng = uu____5909;
              FStar_Syntax_Syntax.sigquals = uu____5910;
              FStar_Syntax_Syntax.sigmeta = uu____5911;
              FStar_Syntax_Syntax.sigattrs = uu____5912;_}::[] ->
              FStar_Pervasives_Native.Some def
          | uu____5941 -> FStar_Pervasives_Native.None in
        let parse1 frag =
          let uu____5954 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
          match uu____5954 with
          | FStar_Util.Inl (FStar_Util.Inr decls,uu____5978) ->
              FStar_Pervasives_Native.Some decls
          | uu____6023 -> FStar_Pervasives_Native.None in
        let desugar dsenv decls =
          let uu____6055 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
          FStar_Pervasives_Native.snd uu____6055 in
        let typecheck tcenv decls =
          let uu____6073 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
          match uu____6073 with | (ses,uu____6087,uu____6088) -> ses in
        let rules1 =
          FStar_List.append
            (match rules with
             | FStar_Pervasives_Native.Some rules1 -> rules1
             | FStar_Pervasives_Native.None  ->
                 [FStar_TypeChecker_Normalize.Beta;
                 FStar_TypeChecker_Normalize.Iota;
                 FStar_TypeChecker_Normalize.Zeta;
                 FStar_TypeChecker_Normalize.UnfoldUntil
                   FStar_Syntax_Syntax.Delta_constant])
            [FStar_TypeChecker_Normalize.Inlining;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.Primops] in
        run_and_rewind st
          (fun st1  ->
             let uu____6116 = st1.repl_env in
             match uu____6116 with
             | (dsenv,tcenv) ->
                 let frag = dummy_let_fragment term in
                 (match st1.repl_curmod with
                  | FStar_Pervasives_Native.None  ->
                      (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                  | uu____6128 ->
                      let uu____6129 = parse1 frag in
                      (match uu____6129 with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr "Count not parse this term"))
                       | FStar_Pervasives_Native.Some decls ->
                           (try
                              let decls1 = desugar dsenv decls in
                              let ses = typecheck tcenv decls1 in
                              match find_let_body ses with
                              | FStar_Pervasives_Native.None  ->
                                  (QueryNOK,
                                    (FStar_Util.JsonStr
                                       "Typechecking yielded an unexpected term"))
                              | FStar_Pervasives_Native.Some def ->
                                  let normalized =
                                    normalize_term1 tcenv rules1 def in
                                  let uu____6173 =
                                    let uu____6174 =
                                      term_to_string tcenv normalized in
                                    FStar_Util.JsonStr uu____6174 in
                                  (QueryOK, uu____6173)
                            with
                            | e ->
                                let uu____6184 =
                                  let uu____6185 =
                                    FStar_Errors.issue_of_exn e in
                                  match uu____6185 with
                                  | FStar_Pervasives_Native.Some issue ->
                                      let uu____6189 =
                                        FStar_Errors.format_issue issue in
                                      FStar_Util.JsonStr uu____6189
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Exn.raise e in
                                (QueryNOK, uu____6184)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____6211 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____6225 -> false
let __proj__TypeContainsLid__item___0: search_term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0
let __proj__Mksearch_term__item__st_negate: search_term -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_negate
let __proj__Mksearch_term__item__st_term: search_term -> search_term' =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_term
let st_cost: search_term' -> Prims.int =
  fun uu___203_6249  ->
    match uu___203_6249 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> Prims.parse_int "1"
type search_candidate =
  {
  sc_lid: FStar_Ident.lid;
  sc_typ:
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref;
  sc_fvars:
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref;}
let __proj__Mksearch_candidate__item__sc_lid:
  search_candidate -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_lid
let __proj__Mksearch_candidate__item__sc_typ:
  search_candidate ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_typ
let __proj__Mksearch_candidate__item__sc_fvars:
  search_candidate ->
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_fvars
let sc_of_lid: FStar_Ident.lid -> search_candidate =
  fun lid  ->
    let uu____6417 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____6424 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____6417; sc_fvars = uu____6424 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____6473 = FStar_ST.op_Bang sc.sc_typ in
      match uu____6473 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____6498 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____6498 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____6519,typ),uu____6521) ->
                typ in
          (FStar_ST.op_Colon_Equals sc.sc_typ
             (FStar_Pervasives_Native.Some typ);
           typ)
let sc_fvars:
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lid FStar_Util.set
  =
  fun tcenv  ->
    fun sc  ->
      let uu____6565 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____6565 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____6608 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____6608 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let json_of_search_result:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json
  =
  fun dsenv  ->
    fun tcenv  ->
      fun sc  ->
        let typ_str =
          let uu____6651 = sc_typ tcenv sc in term_to_string tcenv uu____6651 in
        let uu____6652 =
          let uu____6659 =
            let uu____6664 =
              let uu____6665 =
                let uu____6666 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____6666.FStar_Ident.str in
              FStar_Util.JsonStr uu____6665 in
            ("lid", uu____6664) in
          [uu____6659; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____6652
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____6686 -> true
    | uu____6687 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____6695 -> uu____6695
let run_search:
  'Auu____6702 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6702) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_str  ->
      let uu____6723 = st.repl_env in
      match uu____6723 with
      | (dsenv,tcenv) ->
          let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
          let st_matches candidate term =
            let found =
              match term.st_term with
              | NameContainsStr str ->
                  FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
              | TypeContainsLid lid ->
                  let uu____6751 = sc_fvars tcenv candidate in
                  FStar_Util.set_mem lid uu____6751 in
            found <> term.st_negate in
          let parse1 search_str1 =
            let parse_one term =
              let negate = FStar_Util.starts_with term "-" in
              let term1 =
                if negate
                then FStar_Util.substring_from term (Prims.parse_int "1")
                else term in
              let beg_quote = FStar_Util.starts_with term1 "\"" in
              let end_quote = FStar_Util.ends_with term1 "\"" in
              let strip_quotes str =
                if (FStar_String.length str) < (Prims.parse_int "2")
                then FStar_Exn.raise (InvalidSearch "Empty search term")
                else
                  FStar_Util.substring str (Prims.parse_int "1")
                    ((FStar_String.length term1) - (Prims.parse_int "2")) in
              let parsed =
                if beg_quote <> end_quote
                then
                  let uu____6775 =
                    let uu____6776 =
                      FStar_Util.format1 "Improperly quoted search term: %s"
                        term1 in
                    InvalidSearch uu____6776 in
                  FStar_Exn.raise uu____6775
                else
                  if beg_quote
                  then
                    (let uu____6778 = strip_quotes term1 in
                     NameContainsStr uu____6778)
                  else
                    (let lid = FStar_Ident.lid_of_str term1 in
                     let uu____6781 =
                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                         dsenv lid in
                     match uu____6781 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____6784 =
                           let uu____6785 =
                             FStar_Util.format1 "Unknown identifier: %s"
                               term1 in
                           InvalidSearch uu____6785 in
                         FStar_Exn.raise uu____6784
                     | FStar_Pervasives_Native.Some lid1 ->
                         TypeContainsLid lid1) in
              { st_negate = negate; st_term = parsed } in
            let terms =
              FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
            let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
            FStar_Util.sort_with cmp terms in
          let pprint_one term =
            let uu____6801 =
              match term.st_term with
              | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
              | TypeContainsLid l ->
                  FStar_Util.format1 "%s" l.FStar_Ident.str in
            Prims.strcat (if term.st_negate then "-" else "") uu____6801 in
          let results =
            try
              let terms = parse1 search_str in
              let all_lidents = FStar_TypeChecker_Env.lidents tcenv in
              let all_candidates = FStar_List.map sc_of_lid all_lidents in
              let matches_all candidate =
                FStar_List.for_all (st_matches candidate) terms in
              let cmp r1 r2 =
                FStar_Util.compare (r1.sc_lid).FStar_Ident.str
                  (r2.sc_lid).FStar_Ident.str in
              let results = FStar_List.filter matches_all all_candidates in
              let sorted1 = FStar_Util.sort_with cmp results in
              let js =
                FStar_List.map (json_of_search_result dsenv tcenv) sorted1 in
              match results with
              | [] ->
                  let kwds =
                    let uu____6864 = FStar_List.map pprint_one terms in
                    FStar_Util.concat_l " " uu____6864 in
                  let uu____6867 =
                    let uu____6868 =
                      FStar_Util.format1 "No results found for query [%s]"
                        kwds in
                    InvalidSearch uu____6868 in
                  FStar_Exn.raise uu____6867
              | uu____6873 -> (QueryOK, (FStar_Util.JsonList js))
            with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s)) in
          (results, (FStar_Util.Inl st))
let run_query:
  repl_state ->
    query' ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun uu___204_6924  ->
      match uu___204_6924 with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | DescribeRepl  -> run_describe_repl st
      | Pop  -> run_pop st
      | Push (kind,text1,l,c,peek1) -> run_push st kind text1 l c peek1
      | AutoComplete search_term -> run_completions st search_term
      | Lookup (symbol,pos_opt,rqi) -> run_lookup st symbol pos_opt rqi
      | Compute (term,rules) -> run_compute st term rules
      | Search term -> run_search st term
      | MissingCurrentModule  -> run_missing_current_module st (Obj.magic ())
      | ProtocolViolation query -> run_protocol_violation st query
let validate_query: repl_state -> query -> query =
  fun st  ->
    fun q  ->
      match q.qq with
      | Push (SyntaxCheck ,uu____6986,uu____6987,uu____6988,false ) ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____6989 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = MissingCurrentModule; qid = (q.qid) }
           | uu____6990 -> q)
let rec go: repl_state -> Prims.unit =
  fun st  ->
    let query =
      let uu____6996 = read_interactive_query st.repl_stdin in
      validate_query st uu____6996 in
    let uu____6997 = let uu____7010 = run_query st in uu____7010 query.qq in
    match uu____6997 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____7054 =
      let uu____7057 = FStar_ST.op_Bang issues in e :: uu____7057 in
    FStar_ST.op_Colon_Equals issues uu____7054 in
  let count_errors uu____7127 =
    let uu____7128 =
      let uu____7131 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____7131 in
    FStar_List.length uu____7128 in
  let report1 uu____7173 =
    let uu____7174 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____7174 in
  let clear1 uu____7212 = FStar_ST.op_Colon_Equals issues [] in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report1;
    FStar_Errors.eh_clear = clear1
  }
let interactive_printer: FStar_Util.printer =
  {
    FStar_Util.printer_prinfo =
      (fun s  -> write_message "info" (FStar_Util.JsonStr s));
    FStar_Util.printer_prwarning =
      (fun s  -> write_message "warning" (FStar_Util.JsonStr s));
    FStar_Util.printer_prerror =
      (fun s  -> write_message "error" (FStar_Util.JsonStr s));
    FStar_Util.printer_prgeneric =
      (fun label1  ->
         fun get_string  ->
           fun get_json  ->
             let uu____7267 = get_json () in write_message label1 uu____7267)
  }
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let uu____7273 = deps_of_our_file filename in
     match uu____7273 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____7297 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu____7297 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____7324 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____7325 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____7324 uu____7325 in
              let env2 =
                let uu____7331 =
                  FStar_TypeChecker_Env.set_range
                    (FStar_Pervasives_Native.snd env1) initial_range in
                ((FStar_Pervasives_Native.fst env1), uu____7331) in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2 in
              (FStar_TypeChecker_Env.toggle_id_info
                 (FStar_Pervasives_Native.snd env3) true;
               (let init_st =
                  let uu____7344 = FStar_Util.open_stdin () in
                  {
                    repl_line = (Prims.parse_int "1");
                    repl_column = (Prims.parse_int "0");
                    repl_fname = filename;
                    repl_stack = stack;
                    repl_curmod = FStar_Pervasives_Native.None;
                    repl_env = env3;
                    repl_ts = ts;
                    repl_stdin = uu____7344
                  } in
                let uu____7345 =
                  (FStar_Options.record_hints ()) ||
                    (FStar_Options.use_hints ()) in
                if uu____7345
                then
                  let uu____7346 =
                    let uu____7347 = FStar_Options.file_list () in
                    FStar_List.hd uu____7347 in
                  FStar_SMTEncoding_Solver.with_hints_db uu____7346
                    (fun uu____7351  -> go init_st)
                else go init_st))))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    FStar_Errors.set_handler interactive_error_handler;
    (let uu____7360 =
       let uu____7361 = FStar_Options.codegen () in
       FStar_Option.isSome uu____7361 in
     if uu____7360
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (try interactive_mode' filename
     with
     | e ->
         (FStar_Errors.set_handler FStar_Errors.default_handler;
          FStar_Exn.raise e))