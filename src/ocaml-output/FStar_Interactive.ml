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
                 | (uu____119,dsenv1,env1) ->
                     (((FStar_Pervasives_Native.Some intf), impl), dsenv1,
                       env1, remaining1))
            | intf_or_impl::remaining1 ->
                let uu____148 =
                  FStar_Universal.tc_one_file dsenv env
                    FStar_Pervasives_Native.None intf_or_impl in
                (match uu____148 with
                 | (uu____177,dsenv1,env1) ->
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
  fun uu____276  ->
    let uu____277 = FStar_Universal.tc_prims () in
    match uu____277 with | (uu____292,dsenv,env) -> (dsenv, env)
type env_t =
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t,modul_t) FStar_Pervasives_Native.tuple2 Prims.list
let pop:
  'Auu____321 .
    ('Auu____321,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.string -> Prims.unit
  =
  fun uu____332  ->
    fun msg  ->
      match uu____332 with
      | (uu____338,env) ->
          (FStar_Universal.pop_context env msg; FStar_Options.pop ())
type push_kind =
  | SyntaxCheck
  | LaxCheck
  | FullCheck
let uu___is_SyntaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____345 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____350 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____355 -> false
let push:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    push_kind ->
      Prims.bool ->
        Prims.string ->
          (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2
  =
  fun uu____376  ->
    fun kind  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____376 with
          | (dsenv,tcenv) ->
              let tcenv1 =
                let uu___199_391 = tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___199_391.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___199_391.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___199_391.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___199_391.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___199_391.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___199_391.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___199_391.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___199_391.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___199_391.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___199_391.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___199_391.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___199_391.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___199_391.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___199_391.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___199_391.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___199_391.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___199_391.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___199_391.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = (kind = LaxCheck);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___199_391.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___199_391.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___199_391.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___199_391.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___199_391.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___199_391.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___199_391.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___199_391.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___199_391.FStar_TypeChecker_Env.identifier_info)
                } in
              let dsenv1 =
                FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck) in
              let res = FStar_Universal.push_context (dsenv1, tcenv1) msg in
              (FStar_Options.push ();
               if restore_cmd_line_options1
               then
                 (let uu____400 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____400 FStar_Pervasives.ignore)
               else ();
               res)
let mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____413  ->
    match uu____413 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.mark dsenv in
        let env1 = FStar_TypeChecker_Env.mark env in
        (FStar_Options.push (); (dsenv1, env1))
let reset_mark:
  'Auu____431 .
    ('Auu____431,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____443  ->
    match uu____443 with
    | (uu____448,env) ->
        let dsenv = FStar_ToSyntax_Env.reset_mark () in
        let env1 = FStar_TypeChecker_Env.reset_mark env in
        (FStar_Options.pop (); (dsenv, env1))
let cleanup:
  'Auu____457 .
    ('Auu____457,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.unit
  =
  fun uu____465  ->
    match uu____465 with
    | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
let commit_mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____483  ->
    match uu____483 with
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
  fun uu____529  ->
    fun curmod  ->
      fun frag  ->
        match uu____529 with
        | (dsenv,env) ->
            (try
               let uu____593 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag in
               match uu____593 with
               | FStar_Pervasives_Native.Some (m,dsenv1,env1) ->
                   let uu____633 =
                     let uu____646 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____646) in
                   FStar_Pervasives_Native.Some uu____633
               | uu____665 -> FStar_Pervasives_Native.None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____709 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____709 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____732 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____732 ->
                 ((let uu____734 =
                     let uu____741 =
                       let uu____746 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____746) in
                     [uu____741] in
                   FStar_TypeChecker_Err.add_errors env uu____734);
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
    let uu____782 =
      FStar_List.partition
        (fun x  ->
           let uu____795 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____796 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____795 <> uu____796) deps in
    match uu____782 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____823 =
                  (let uu____826 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____826) ||
                    (let uu____828 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____828) in
                if uu____823
                then
                  let uu____829 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____829
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____832 ->
              ((let uu____836 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____836);
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
            | uu____891 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____910 =
                    let uu____911 = FStar_Options.lax () in
                    if uu____911 then LaxCheck else FullCheck in
                  push env uu____910 true "typecheck_modul" in
                let uu____913 = tc_one_file remaining env1 in
                (match uu____913 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____964 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____977 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____977
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____964 with
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
                 | (uu____1081,uu____1082) ->
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
                     | uu____1177 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1205 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1288::ts3 ->
                    (pop env1 "";
                     (let uu____1329 =
                        let uu____1344 = FStar_List.hd stack in
                        let uu____1353 = FStar_List.tl stack in
                        (uu____1344, uu____1353) in
                      match uu____1329 with
                      | ((env2,uu____1379),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1443 = ts_elt in
                  (match uu____1443 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1474 = match_dep depnames intf impl in
                       (match uu____1474 with
                        | (b,depnames') ->
                            let uu____1493 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1493
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1514 =
                                 let uu____1529 = FStar_List.hd st in
                                 let uu____1538 = FStar_List.tl st in
                                 (uu____1529, uu____1538) in
                               match uu____1514 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1615 = deps_of_our_file filename in
            match uu____1615 with
            | (filenames,uu____1631) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___189_1691  ->
    match uu___189_1691 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1695 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1695
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1697 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1700 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1718 -> true
    | uu____1723 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1739 -> uu____1739
let js_fail: 'Auu____1750 . Prims.string -> FStar_Util.json -> 'Auu____1750 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___190_1762  ->
    match uu___190_1762 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___191_1768  ->
    match uu___191_1768 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list:
  'Auu____1777 .
    (FStar_Util.json -> 'Auu____1777) ->
      FStar_Util.json -> 'Auu____1777 Prims.list
  =
  fun k  ->
    fun uu___192_1790  ->
      match uu___192_1790 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___193_1808  ->
    match uu___193_1808 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1833 = js_str s in
    match uu____1833 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1834 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1839 = js_str s in
    match uu____1839 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | uu____1840 -> js_fail "reduction rule" s
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
  | ProtocolViolation of Prims.string
and query = {
  qq: query';
  qid: Prims.string;}
let uu___is_Exit: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1911 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1916 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1921 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1926 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1942 -> false
let __proj__Push__item___0:
  query' ->
    (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1986 -> false
let __proj__AutoComplete__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2016 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,(Prims.string,Prims.int,Prims.int)
                    FStar_Pervasives_Native.tuple3
                    FStar_Pervasives_Native.option,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2086 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2124 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2138 -> false
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
let interactive_protocol_vernum: Prims.int = Prims.parse_int "1"
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
    | InvalidQuery uu____2168 -> true
    | uu____2169 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2177 -> uu____2177
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2182 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2187 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2192 -> false
let try_assoc:
  'Auu____2201 'Auu____2202 .
    'Auu____2202 ->
      ('Auu____2202,'Auu____2201) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2201 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2225 =
        FStar_Util.try_find
          (fun uu____2239  ->
             match uu____2239 with | (k,uu____2245) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2225
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2262 =
          let uu____2263 =
            let uu____2264 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2264 in
          ProtocolViolation uu____2263 in
        { qq = uu____2262; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2291 = try_assoc key a in
      match uu____2291 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2295 =
            let uu____2296 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____2296 in
          FStar_Exn.raise uu____2295 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____2311 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2311 js_str in
    try
      let query =
        let uu____2320 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____2320 js_str in
      let args =
        let uu____2328 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____2328 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____2345 = try_assoc k args in
        match uu____2345 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____2353 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____2354 =
              let uu____2365 =
                let uu____2366 = arg "kind" in
                FStar_All.pipe_right uu____2366 js_pushkind in
              let uu____2367 =
                let uu____2368 = arg "code" in
                FStar_All.pipe_right uu____2368 js_str in
              let uu____2369 =
                let uu____2370 = arg "line" in
                FStar_All.pipe_right uu____2370 js_int in
              let uu____2371 =
                let uu____2372 = arg "column" in
                FStar_All.pipe_right uu____2372 js_int in
              (uu____2365, uu____2367, uu____2369, uu____2371,
                (query = "peek")) in
            Push uu____2354
        | "push" ->
            let uu____2373 =
              let uu____2384 =
                let uu____2385 = arg "kind" in
                FStar_All.pipe_right uu____2385 js_pushkind in
              let uu____2386 =
                let uu____2387 = arg "code" in
                FStar_All.pipe_right uu____2387 js_str in
              let uu____2388 =
                let uu____2389 = arg "line" in
                FStar_All.pipe_right uu____2389 js_int in
              let uu____2390 =
                let uu____2391 = arg "column" in
                FStar_All.pipe_right uu____2391 js_int in
              (uu____2384, uu____2386, uu____2388, uu____2390,
                (query = "peek")) in
            Push uu____2373
        | "autocomplete" ->
            let uu____2392 =
              let uu____2393 = arg "partial-symbol" in
              FStar_All.pipe_right uu____2393 js_str in
            AutoComplete uu____2392
        | "lookup" ->
            let uu____2394 =
              let uu____2411 =
                let uu____2412 = arg "symbol" in
                FStar_All.pipe_right uu____2412 js_str in
              let uu____2413 =
                let uu____2422 =
                  let uu____2431 = try_arg "location" in
                  FStar_All.pipe_right uu____2431
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____2422
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____2489 =
                          let uu____2490 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____2490 js_str in
                        let uu____2491 =
                          let uu____2492 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____2492 js_int in
                        let uu____2493 =
                          let uu____2494 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____2494 js_int in
                        (uu____2489, uu____2491, uu____2493))) in
              let uu____2495 =
                let uu____2498 = arg "requested-info" in
                FStar_All.pipe_right uu____2498 (js_list js_str) in
              (uu____2411, uu____2413, uu____2495) in
            Lookup uu____2394
        | "compute" ->
            let uu____2511 =
              let uu____2520 =
                let uu____2521 = arg "term" in
                FStar_All.pipe_right uu____2521 js_str in
              let uu____2522 =
                let uu____2527 = try_arg "rules" in
                FStar_All.pipe_right uu____2527
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____2520, uu____2522) in
            Compute uu____2511
        | "search" ->
            let uu____2542 =
              let uu____2543 = arg "terms" in
              FStar_All.pipe_right uu____2543 js_str in
            Search uu____2542
        | uu____2544 ->
            let uu____2545 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____2545 in
      { qq = uu____2353; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let validate_interactive_query: query -> query =
  fun uu___194_2555  ->
    match uu___194_2555 with
    | { qq = Push (SyntaxCheck ,uu____2556,uu____2557,uu____2558,false );
        qid;_} ->
        {
          qq =
            (ProtocolViolation
               "Cannot use 'kind': 'syntax' with 'query': 'push'");
          qid
        }
    | other -> other
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____2568 = FStar_Util.read_line stream in
      match uu____2568 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some line ->
          let uu____2572 = FStar_Util.json_of_string line in
          (match uu____2572 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               let uu____2576 = unpack_interactive_query request in
               validate_interactive_query uu____2576)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let rec json_of_fstar_option: FStar_Options.option_val -> FStar_Util.json =
  fun uu___195_2586  ->
    match uu___195_2586 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____2594 = FStar_List.map json_of_fstar_option vs in
        FStar_Util.JsonList uu____2594
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let json_of_opt:
  'Auu____2603 .
    ('Auu____2603 -> FStar_Util.json) ->
      'Auu____2603 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____2621 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____2621
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____2628 =
      let uu____2631 =
        let uu____2632 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____2632 in
      let uu____2633 =
        let uu____2636 =
          let uu____2637 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____2637 in
        [uu____2636] in
      uu____2631 :: uu____2633 in
    FStar_Util.JsonList uu____2628
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____2650 =
          let uu____2657 =
            let uu____2664 =
              let uu____2669 = json_of_pos b in ("beg", uu____2669) in
            let uu____2670 =
              let uu____2677 =
                let uu____2682 = json_of_pos e in ("end", uu____2682) in
              [uu____2677] in
            uu____2664 :: uu____2670 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____2657 in
        FStar_Util.JsonAssoc uu____2650
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2703 = FStar_Range.file_of_use_range r in
    let uu____2704 = FStar_Range.start_of_use_range r in
    let uu____2705 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____2703 uu____2704 uu____2705
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2710 = FStar_Range.file_of_range r in
    let uu____2711 = FStar_Range.start_of_range r in
    let uu____2712 = FStar_Range.end_of_range r in
    json_of_range_fields uu____2710 uu____2711 uu____2712
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
    let uu____2721 =
      let uu____2728 =
        let uu____2735 =
          let uu____2742 =
            let uu____2747 =
              let uu____2748 =
                let uu____2751 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____2757 = json_of_use_range r in [uu____2757] in
                let uu____2758 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____2764 = json_of_def_range r in [uu____2764]
                  | uu____2765 -> [] in
                FStar_List.append uu____2751 uu____2758 in
              FStar_Util.JsonList uu____2748 in
            ("ranges", uu____2747) in
          [uu____2742] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____2735 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____2728 in
    FStar_Util.JsonAssoc uu____2721
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
    let uu____2917 =
      let uu____2924 =
        let uu____2931 =
          let uu____2936 = json_of_opt json_of_def_range lr.lr_def_range in
          ("defined-at", uu____2936) in
        let uu____2937 =
          let uu____2944 =
            let uu____2949 =
              json_of_opt (fun _0_40  -> FStar_Util.JsonStr _0_40) lr.lr_typ in
            ("type", uu____2949) in
          let uu____2950 =
            let uu____2957 =
              let uu____2962 =
                json_of_opt (fun _0_41  -> FStar_Util.JsonStr _0_41)
                  lr.lr_doc in
              ("documentation", uu____2962) in
            let uu____2963 =
              let uu____2970 =
                let uu____2975 =
                  json_of_opt (fun _0_42  -> FStar_Util.JsonStr _0_42)
                    lr.lr_def in
                ("definition", uu____2975) in
              [uu____2970] in
            uu____2957 :: uu____2963 in
          uu____2944 :: uu____2950 in
        uu____2931 :: uu____2937 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____2924 in
    FStar_Util.JsonAssoc uu____2917
let json_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3008 =
      FStar_List.map (fun _0_43  -> FStar_Util.JsonStr _0_43)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_44  -> FStar_Util.JsonList _0_44) uu____3008 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____3030 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____3030);
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
  fun uu____3092  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____3095 =
        FStar_List.map (fun _0_45  -> FStar_Util.JsonStr _0_45)
          interactive_protocol_features in
      FStar_Util.JsonList uu____3095 in
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
        let uu____3256 = FStar_Options.docs () in
        FStar_Util.smap_of_list uu____3256 in
      let get_doc k = FStar_Util.smap_try_find opt_docs k in
      FStar_List.map
        (fun uu____3288  ->
           match uu____3288 with
           | (k,v1) ->
               let uu____3305 = FStar_Options.get_option k in
               let uu____3306 = get_doc k in (k, uu____3305, uu____3306, v1))
        FStar_Options.defaults in
    let uu____3311 =
      let uu____3316 =
        let uu____3317 =
          FStar_List.map
            (fun uu____3337  ->
               match uu____3337 with
               | (uu____3350,fstname,uu____3352,uu____3353) ->
                   FStar_Util.JsonStr fstname) st.repl_ts in
        FStar_Util.JsonList uu____3317 in
      ("loaded-dependencies", uu____3316) in
    let uu____3362 =
      let uu____3369 =
        let uu____3374 =
          let uu____3375 =
            FStar_List.map
              (fun uu____3394  ->
                 match uu____3394 with
                 | (name,value,doc1,dflt1) ->
                     let uu____3413 =
                       let uu____3420 =
                         let uu____3427 =
                           let uu____3432 = json_of_fstar_option value in
                           ("value", uu____3432) in
                         let uu____3433 =
                           let uu____3440 =
                             let uu____3445 = json_of_fstar_option dflt1 in
                             ("default", uu____3445) in
                           let uu____3446 =
                             let uu____3453 =
                               let uu____3458 =
                                 json_of_opt
                                   (fun _0_46  -> FStar_Util.JsonStr _0_46)
                                   doc1 in
                               ("documentation", uu____3458) in
                             [uu____3453] in
                           uu____3440 :: uu____3446 in
                         uu____3427 :: uu____3433 in
                       ("name", (FStar_Util.JsonStr name)) :: uu____3420 in
                     FStar_Util.JsonAssoc uu____3413) opts_and_defaults in
          FStar_Util.JsonList uu____3375 in
        ("options", uu____3374) in
      [uu____3369] in
    uu____3311 :: uu____3362
let with_printed_effect_args:
  'Auu____3495 . (Prims.unit -> 'Auu____3495) -> 'Auu____3495 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____3507  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____3518  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
let sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____3524  -> FStar_Syntax_Print.sigelt_to_string se)
let run_exit:
  'Auu____3531 'Auu____3532 .
    'Auu____3532 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3531,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol:
  'Auu____3563 'Auu____3564 .
    'Auu____3564 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3564,'Auu____3563) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl:
  'Auu____3593 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____3593) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____3610 =
      let uu____3615 =
        let uu____3616 = json_of_repl_state st in
        FStar_Util.JsonAssoc uu____3616 in
      (QueryOK, uu____3615) in
    (uu____3610, (FStar_Util.Inl st))
let run_protocol_violation:
  'Auu____3639 'Auu____3640 .
    'Auu____3640 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____3640,'Auu____3639) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let nothing_left_to_pop: repl_state -> Prims.bool =
  fun st  ->
    (FStar_List.length st.repl_stack) <= (FStar_List.length st.repl_ts)
let run_pop:
  'Auu____3693 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____3693) FStar_Util.either)
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
               let uu___206_3762 = st in
               {
                 repl_line = (uu___206_3762.repl_line);
                 repl_column = (uu___206_3762.repl_column);
                 repl_fname = (uu___206_3762.repl_fname);
                 repl_stack = stack;
                 repl_curmod = curmod;
                 repl_env = env;
                 repl_ts = (uu___206_3762.repl_ts);
                 repl_stdin = (uu___206_3762.repl_stdin)
               } in
             if nothing_left_to_pop st' then cleanup env else ();
             ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))))
let run_push:
  'Auu____3787 .
    repl_state ->
      push_kind ->
        Prims.string ->
          Prims.int ->
            Prims.int ->
              Prims.bool ->
                ((query_status,FStar_Util.json)
                   FStar_Pervasives_Native.tuple2,(repl_state,'Auu____3787)
                                                    FStar_Util.either)
                  FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun kind  ->
      fun text1  ->
        fun line  ->
          fun column1  ->
            fun peek_only  ->
              let uu____3824 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
              match uu____3824 with
              | (stack,env,ts) ->
                  let uu____3846 =
                    if nothing_left_to_pop st
                    then
                      let uu____3867 =
                        update_deps st.repl_fname st.repl_curmod stack env ts in
                      (true, uu____3867)
                    else (false, (stack, env, ts)) in
                  (match uu____3846 with
                   | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
                       let stack2 = (env1, (st.repl_curmod)) :: stack1 in
                       let env2 =
                         push env1 kind restore_cmd_line_options1 "#push" in
                       let env_mark = mark env2 in
                       let frag =
                         {
                           FStar_Parser_ParseIt.frag_text = text1;
                           FStar_Parser_ParseIt.frag_line = line;
                           FStar_Parser_ParseIt.frag_col = column1
                         } in
                       let res =
                         check_frag env_mark st.repl_curmod (frag, false) in
                       let errors =
                         let uu____3949 = FStar_Errors.report_all () in
                         FStar_All.pipe_right uu____3949
                           (FStar_List.map json_of_issue) in
                       (FStar_Errors.clear ();
                        (let st' =
                           let uu___207_3958 = st in
                           {
                             repl_line = line;
                             repl_column = column1;
                             repl_fname = (uu___207_3958.repl_fname);
                             repl_stack = stack2;
                             repl_curmod = (uu___207_3958.repl_curmod);
                             repl_env = (uu___207_3958.repl_env);
                             repl_ts = ts1;
                             repl_stdin = (uu___207_3958.repl_stdin)
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
                                  (let uu___208_4012 = st' in
                                   {
                                     repl_line = (uu___208_4012.repl_line);
                                     repl_column =
                                       (uu___208_4012.repl_column);
                                     repl_fname = (uu___208_4012.repl_fname);
                                     repl_stack = (uu___208_4012.repl_stack);
                                     repl_curmod = curmod;
                                     repl_env = env4;
                                     repl_ts = (uu___208_4012.repl_ts);
                                     repl_stdin = (uu___208_4012.repl_stdin)
                                   })))
                         | uu____4013 ->
                             let env3 = reset_mark env_mark in
                             let uu____4033 =
                               run_pop
                                 (let uu___209_4047 = st' in
                                  {
                                    repl_line = (uu___209_4047.repl_line);
                                    repl_column = (uu___209_4047.repl_column);
                                    repl_fname = (uu___209_4047.repl_fname);
                                    repl_stack = (uu___209_4047.repl_stack);
                                    repl_curmod = (uu___209_4047.repl_curmod);
                                    repl_env = env3;
                                    repl_ts = (uu___209_4047.repl_ts);
                                    repl_stdin = (uu___209_4047.repl_stdin)
                                  }) in
                             (match uu____4033 with
                              | (uu____4060,st'') ->
                                  let status =
                                    if peek_only then QueryOK else QueryNOK in
                                  ((status, (FStar_Util.JsonList errors)),
                                    st'')))))
let run_lookup:
  'Auu____4098 .
    repl_state ->
      Prims.string ->
        (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option ->
          Prims.string Prims.list ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____4098) FStar_Util.either)
              FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____4147 = st.repl_env in
          match uu____4147 with
          | (dsenv,tcenv) ->
              let info_of_lid_str lid_str =
                let lid =
                  let uu____4179 =
                    FStar_List.map FStar_Ident.id_of_text
                      (FStar_Util.split lid_str ".") in
                  FStar_Ident.lid_of_ids uu____4179 in
                let lid1 =
                  let uu____4183 =
                    FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                      lid in
                  FStar_All.pipe_left (FStar_Util.dflt lid) uu____4183 in
                let uu____4188 =
                  FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
                FStar_All.pipe_right uu____4188
                  (FStar_Util.map_option
                     (fun uu____4243  ->
                        match uu____4243 with
                        | ((uu____4262,typ),r) ->
                            ((FStar_Util.Inr lid1), typ, r))) in
              let docs_of_lid lid =
                let uu____4279 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
                FStar_All.pipe_right uu____4279
                  (FStar_Util.map_option FStar_Pervasives_Native.fst) in
              let def_of_lid lid =
                let uu____4308 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
                FStar_Util.bind_opt uu____4308
                  (fun uu___196_4352  ->
                     match uu___196_4352 with
                     | (FStar_Util.Inr (se,uu____4374),uu____4375) ->
                         let uu____4404 = sigelt_to_string se in
                         FStar_Pervasives_Native.Some uu____4404
                     | uu____4405 -> FStar_Pervasives_Native.None) in
              let info_at_pos_opt =
                FStar_Util.bind_opt pos_opt
                  (fun uu____4457  ->
                     match uu____4457 with
                     | (file,row,col) ->
                         FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
              let info_opt =
                match info_at_pos_opt with
                | FStar_Pervasives_Native.Some uu____4504 -> info_at_pos_opt
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
                        let uu____4606 = term_to_string tcenv typ in
                        FStar_Pervasives_Native.Some uu____4606
                      else FStar_Pervasives_Native.None in
                    let doc_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "documentation" requested_info ->
                          docs_of_lid lid
                      | uu____4614 -> FStar_Pervasives_Native.None in
                    let def_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "definition" requested_info ->
                          def_of_lid lid
                      | uu____4625 -> FStar_Pervasives_Native.None in
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
                    let uu____4637 = json_of_lookup_result result in
                    (QueryOK, uu____4637) in
              (response, (FStar_Util.Inl st))
let run_completions:
  'Auu____4652 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4652) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      let uu____4673 = st.repl_env in
      match uu____4673 with
      | (dsenv,tcenv) ->
          let rec measure_anchored_match search_term1 candidate =
            match (search_term1, candidate) with
            | ([],uu____4723) ->
                FStar_Pervasives_Native.Some ([], (Prims.parse_int "0"))
            | (uu____4738,[]) -> FStar_Pervasives_Native.None
            | (hs::ts,hc::tc) ->
                let hc_text = FStar_Ident.text_of_id hc in
                if FStar_Util.starts_with hc_text hs
                then
                  (match ts with
                   | [] ->
                       FStar_Pervasives_Native.Some
                         (candidate, (FStar_String.length hs))
                   | uu____4788 ->
                       let uu____4791 = measure_anchored_match ts tc in
                       FStar_All.pipe_right uu____4791
                         (FStar_Util.map_option
                            (fun uu____4831  ->
                               match uu____4831 with
                               | (matched,len) ->
                                   ((hc :: matched),
                                     (((FStar_String.length hc_text) +
                                         (Prims.parse_int "1"))
                                        + len)))))
                else FStar_Pervasives_Native.None in
          let rec locate_match needle candidate =
            let uu____4886 = measure_anchored_match needle candidate in
            match uu____4886 with
            | FStar_Pervasives_Native.Some (matched,n1) ->
                FStar_Pervasives_Native.Some ([], matched, n1)
            | FStar_Pervasives_Native.None  ->
                (match candidate with
                 | [] -> FStar_Pervasives_Native.None
                 | hc::tc ->
                     let uu____4965 = locate_match needle tc in
                     FStar_All.pipe_right uu____4965
                       (FStar_Util.map_option
                          (fun uu____5026  ->
                             match uu____5026 with
                             | (prefix1,matched,len) ->
                                 ((hc :: prefix1), matched, len)))) in
          let str_of_ids ids =
            let uu____5070 = FStar_List.map FStar_Ident.text_of_id ids in
            FStar_Util.concat_l "." uu____5070 in
          let match_lident_against needle lident =
            locate_match needle
              (FStar_List.append lident.FStar_Ident.ns
                 [lident.FStar_Ident.ident]) in
          let shorten_namespace uu____5117 =
            match uu____5117 with
            | (prefix1,matched,match_len) ->
                let naked_match =
                  match matched with
                  | uu____5148::[] -> true
                  | uu____5149 -> false in
                let uu____5152 =
                  FStar_ToSyntax_Env.shorten_module_path dsenv prefix1
                    naked_match in
                (match uu____5152 with
                 | (stripped_ns,shortened) ->
                     let uu____5179 = str_of_ids shortened in
                     let uu____5180 = str_of_ids matched in
                     let uu____5181 = str_of_ids stripped_ns in
                     (uu____5179, uu____5180, uu____5181, match_len)) in
          let prepare_candidate uu____5199 =
            match uu____5199 with
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
                        let uu____5327 =
                          FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                            dsenv lid in
                        FStar_Option.map
                          (fun fqn  ->
                             let uu____5343 =
                               let uu____5346 =
                                 FStar_List.map FStar_Ident.id_of_text
                                   orig_ns in
                               FStar_List.append uu____5346
                                 [fqn.FStar_Ident.ident] in
                             ([], uu____5343, matched_length)) uu____5327
                      else FStar_Pervasives_Native.None)) in
            let case_b_find_matches_in_env uu____5379 =
              let matches =
                FStar_List.filter_map (match_lident_against needle)
                  all_lidents_in_env in
              FStar_All.pipe_right matches
                (FStar_List.filter
                   (fun uu____5454  ->
                      match uu____5454 with
                      | (ns,id,uu____5467) ->
                          let uu____5476 =
                            let uu____5479 = FStar_Ident.lid_of_ids id in
                            FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                              dsenv uu____5479 in
                          (match uu____5476 with
                           | FStar_Pervasives_Native.None  -> false
                           | FStar_Pervasives_Native.Some l ->
                               let uu____5481 =
                                 FStar_Ident.lid_of_ids
                                   (FStar_List.append ns id) in
                               FStar_Ident.lid_equals l uu____5481))) in
            let uu____5482 = FStar_Util.prefix needle in
            match uu____5482 with
            | (ns,id) ->
                let matched_ids =
                  match ns with
                  | [] -> case_b_find_matches_in_env ()
                  | uu____5528 ->
                      let l =
                        FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
                      let uu____5532 =
                        FStar_ToSyntax_Env.resolve_module_name dsenv l true in
                      (match uu____5532 with
                       | FStar_Pervasives_Native.None  ->
                           case_b_find_matches_in_env ()
                       | FStar_Pervasives_Native.Some m ->
                           case_a_find_transitive_includes ns m id) in
                FStar_All.pipe_right matched_ids
                  (FStar_List.map
                     (fun x  ->
                        let uu____5597 = shorten_namespace x in
                        prepare_candidate uu____5597)) in
          let json_candidates =
            let uu____5609 =
              FStar_Util.sort_with
                (fun uu____5632  ->
                   fun uu____5633  ->
                     match (uu____5632, uu____5633) with
                     | ((cd1,ns1,uu____5660),(cd2,ns2,uu____5663)) ->
                         (match FStar_String.compare cd1 cd2 with
                          | _0_47 when _0_47 = (Prims.parse_int "0") ->
                              FStar_String.compare ns1 ns2
                          | n1 -> n1)) matches in
            FStar_List.map
              (fun uu____5687  ->
                 match uu____5687 with
                 | (candidate,ns,match_len) ->
                     FStar_Util.JsonList
                       [FStar_Util.JsonInt match_len;
                       FStar_Util.JsonStr ns;
                       FStar_Util.JsonStr candidate]) uu____5609 in
          ((QueryOK, (FStar_Util.JsonList json_candidates)),
            (FStar_Util.Inl st))
let run_compute:
  'Auu____5713 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____5713) FStar_Util.either)
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
            let uu___210_5794 = st1 in
            {
              repl_line = (uu___210_5794.repl_line);
              repl_column = (uu___210_5794.repl_column);
              repl_fname = (uu___210_5794.repl_fname);
              repl_stack = (uu___210_5794.repl_stack);
              repl_curmod = (uu___210_5794.repl_curmod);
              repl_env = env;
              repl_ts = (uu___210_5794.repl_ts);
              repl_stdin = (uu___210_5794.repl_stdin)
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
                ((uu____5834,{ FStar_Syntax_Syntax.lbname = uu____5835;
                               FStar_Syntax_Syntax.lbunivs = uu____5836;
                               FStar_Syntax_Syntax.lbtyp = uu____5837;
                               FStar_Syntax_Syntax.lbeff = uu____5838;
                               FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____5840);
              FStar_Syntax_Syntax.sigrng = uu____5841;
              FStar_Syntax_Syntax.sigquals = uu____5842;
              FStar_Syntax_Syntax.sigmeta = uu____5843;
              FStar_Syntax_Syntax.sigattrs = uu____5844;_}::[] ->
              FStar_Pervasives_Native.Some def
          | uu____5873 -> FStar_Pervasives_Native.None in
        let parse1 frag =
          let uu____5886 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
          match uu____5886 with
          | FStar_Util.Inl (FStar_Util.Inr decls,uu____5910) ->
              FStar_Pervasives_Native.Some decls
          | uu____5955 -> FStar_Pervasives_Native.None in
        let desugar dsenv decls =
          let uu____5987 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
          FStar_Pervasives_Native.snd uu____5987 in
        let typecheck tcenv decls =
          let uu____6005 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
          match uu____6005 with | (ses,uu____6019,uu____6020) -> ses in
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
             let uu____6048 = st1.repl_env in
             match uu____6048 with
             | (dsenv,tcenv) ->
                 let frag = dummy_let_fragment term in
                 (match st1.repl_curmod with
                  | FStar_Pervasives_Native.None  ->
                      (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                  | uu____6060 ->
                      let uu____6061 = parse1 frag in
                      (match uu____6061 with
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
                                  let uu____6105 =
                                    let uu____6106 =
                                      term_to_string tcenv normalized in
                                    FStar_Util.JsonStr uu____6106 in
                                  (QueryOK, uu____6105)
                            with
                            | e ->
                                let uu____6116 =
                                  let uu____6117 =
                                    FStar_Errors.issue_of_exn e in
                                  match uu____6117 with
                                  | FStar_Pervasives_Native.Some issue ->
                                      let uu____6121 =
                                        FStar_Errors.format_issue issue in
                                      FStar_Util.JsonStr uu____6121
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Exn.raise e in
                                (QueryNOK, uu____6116)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____6143 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____6157 -> false
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
  fun uu___197_6181  ->
    match uu___197_6181 with
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
    let uu____6349 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____6356 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____6349; sc_fvars = uu____6356 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____6405 = FStar_ST.op_Bang sc.sc_typ in
      match uu____6405 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____6430 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____6430 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____6451,typ),uu____6453) ->
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
      let uu____6497 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____6497 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____6540 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____6540 in
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
          let uu____6583 = sc_typ tcenv sc in term_to_string tcenv uu____6583 in
        let uu____6584 =
          let uu____6591 =
            let uu____6596 =
              let uu____6597 =
                let uu____6598 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____6598.FStar_Ident.str in
              FStar_Util.JsonStr uu____6597 in
            ("lid", uu____6596) in
          [uu____6591; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____6584
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____6618 -> true
    | uu____6619 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____6627 -> uu____6627
let run_search:
  'Auu____6634 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6634) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_str  ->
      let uu____6655 = st.repl_env in
      match uu____6655 with
      | (dsenv,tcenv) ->
          let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
          let st_matches candidate term =
            let found =
              match term.st_term with
              | NameContainsStr str ->
                  FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
              | TypeContainsLid lid ->
                  let uu____6683 = sc_fvars tcenv candidate in
                  FStar_Util.set_mem lid uu____6683 in
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
                  let uu____6707 =
                    let uu____6708 =
                      FStar_Util.format1 "Improperly quoted search term: %s"
                        term1 in
                    InvalidSearch uu____6708 in
                  FStar_Exn.raise uu____6707
                else
                  if beg_quote
                  then
                    (let uu____6710 = strip_quotes term1 in
                     NameContainsStr uu____6710)
                  else
                    (let lid = FStar_Ident.lid_of_str term1 in
                     let uu____6713 =
                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                         dsenv lid in
                     match uu____6713 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____6716 =
                           let uu____6717 =
                             FStar_Util.format1 "Unknown identifier: %s"
                               term1 in
                           InvalidSearch uu____6717 in
                         FStar_Exn.raise uu____6716
                     | FStar_Pervasives_Native.Some lid1 ->
                         TypeContainsLid lid1) in
              { st_negate = negate; st_term = parsed } in
            let terms =
              FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
            let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
            FStar_Util.sort_with cmp terms in
          let pprint_one term =
            let uu____6733 =
              match term.st_term with
              | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
              | TypeContainsLid l ->
                  FStar_Util.format1 "%s" l.FStar_Ident.str in
            Prims.strcat (if term.st_negate then "-" else "") uu____6733 in
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
                    let uu____6796 = FStar_List.map pprint_one terms in
                    FStar_Util.concat_l " " uu____6796 in
                  let uu____6799 =
                    let uu____6800 =
                      FStar_Util.format1 "No results found for query [%s]"
                        kwds in
                    InvalidSearch uu____6800 in
                  FStar_Exn.raise uu____6799
              | uu____6805 -> (QueryOK, (FStar_Util.JsonList js))
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
    fun uu___198_6856  ->
      match uu___198_6856 with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | DescribeRepl  -> run_describe_repl st
      | Pop  -> run_pop st
      | Push (kind,text1,l,c,peek1) -> run_push st kind text1 l c peek1
      | AutoComplete search_term -> run_completions st search_term
      | Lookup (symbol,pos_opt,rqi) -> run_lookup st symbol pos_opt rqi
      | Compute (term,rules) -> run_compute st term rules
      | Search term -> run_search st term
      | ProtocolViolation query -> run_protocol_violation st query
let rec go: repl_state -> Prims.unit =
  fun st  ->
    let query = read_interactive_query st.repl_stdin in
    let uu____6915 = let uu____6928 = run_query st in uu____6928 query.qq in
    match uu____6915 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____6972 =
      let uu____6975 = FStar_ST.op_Bang issues in e :: uu____6975 in
    FStar_ST.op_Colon_Equals issues uu____6972 in
  let count_errors uu____7045 =
    let uu____7046 =
      let uu____7049 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____7049 in
    FStar_List.length uu____7046 in
  let report1 uu____7091 =
    let uu____7092 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____7092 in
  let clear1 uu____7130 = FStar_ST.op_Colon_Equals issues [] in
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
             let uu____7185 = get_json () in write_message label1 uu____7185)
  }
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let uu____7191 = deps_of_our_file filename in
     match uu____7191 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____7215 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu____7215 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____7242 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____7243 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____7242 uu____7243 in
              let env2 =
                let uu____7249 =
                  FStar_TypeChecker_Env.set_range
                    (FStar_Pervasives_Native.snd env1) initial_range in
                ((FStar_Pervasives_Native.fst env1), uu____7249) in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2 in
              (FStar_TypeChecker_Env.toggle_id_info
                 (FStar_Pervasives_Native.snd env3) true;
               (let init_st =
                  let uu____7262 = FStar_Util.open_stdin () in
                  {
                    repl_line = (Prims.parse_int "1");
                    repl_column = (Prims.parse_int "0");
                    repl_fname = filename;
                    repl_stack = stack;
                    repl_curmod = FStar_Pervasives_Native.None;
                    repl_env = env3;
                    repl_ts = ts;
                    repl_stdin = uu____7262
                  } in
                let uu____7263 =
                  (FStar_Options.record_hints ()) ||
                    (FStar_Options.use_hints ()) in
                if uu____7263
                then
                  let uu____7264 =
                    let uu____7265 = FStar_Options.file_list () in
                    FStar_List.hd uu____7265 in
                  FStar_SMTEncoding_Solver.with_hints_db uu____7264
                    (fun uu____7269  -> go init_st)
                else go init_st))))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    FStar_Errors.set_handler interactive_error_handler;
    (let uu____7278 =
       let uu____7279 = FStar_Options.codegen () in
       FStar_Option.isSome uu____7279 in
     if uu____7278
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (try interactive_mode' filename
     with
     | e ->
         (FStar_Errors.set_handler FStar_Errors.default_handler;
          FStar_Exn.raise e))