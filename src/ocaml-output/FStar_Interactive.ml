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
      let uu____29 = uenv in
      match uu____29 with
      | (dsenv,env) ->
          let uu____50 =
            match remaining with
            | intf::impl::remaining1 when
                FStar_Universal.needs_interleaving intf impl ->
                let uu____88 =
                  FStar_Universal.tc_one_file dsenv env
                    (FStar_Pervasives_Native.Some intf) impl in
                (match uu____88 with
                 | (uu____117,dsenv1,env1) ->
                     (((FStar_Pervasives_Native.Some intf), impl), dsenv1,
                       env1, remaining1))
            | intf_or_impl::remaining1 ->
                let uu____146 =
                  FStar_Universal.tc_one_file dsenv env
                    FStar_Pervasives_Native.None intf_or_impl in
                (match uu____146 with
                 | (uu____175,dsenv1,env1) ->
                     ((FStar_Pervasives_Native.None, intf_or_impl), dsenv1,
                       env1, remaining1))
            | [] -> failwith "Impossible" in
          (match uu____50 with
           | ((intf,impl),dsenv1,env1,remaining1) ->
               ((intf, impl), (dsenv1, env1), remaining1))
let tc_prims:
  Prims.unit ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____273  ->
    let uu____274 = FStar_Universal.tc_prims () in
    match uu____274 with | (uu____289,dsenv,env) -> (dsenv, env)
type env_t =
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t,modul_t) FStar_Pervasives_Native.tuple2 Prims.list
let pop uu____326 msg =
  match uu____326 with
  | (uu____332,env) ->
      (FStar_Universal.pop_context env msg; FStar_Options.pop ())
type push_kind =
  | SyntaxCheck
  | LaxCheck
  | FullCheck
let uu___is_SyntaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____338 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____342 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____346 -> false
let push:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    push_kind ->
      Prims.bool ->
        Prims.string ->
          (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2
  =
  fun uu____363  ->
    fun kind  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____363 with
          | (dsenv,tcenv) ->
              let tcenv1 =
                let uu___208_378 = tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___208_378.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___208_378.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___208_378.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___208_378.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___208_378.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___208_378.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___208_378.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___208_378.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___208_378.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___208_378.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___208_378.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___208_378.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___208_378.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___208_378.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___208_378.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___208_378.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___208_378.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___208_378.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = (kind = LaxCheck);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___208_378.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___208_378.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___208_378.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___208_378.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___208_378.FStar_TypeChecker_Env.qname_and_index)
                } in
              let dsenv1 =
                FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck) in
              let res = FStar_Universal.push_context (dsenv1, tcenv1) msg in
              (FStar_Options.push ();
               if restore_cmd_line_options1
               then
                 (let uu____387 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____387 FStar_Pervasives.ignore)
               else ();
               res)
let mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____399  ->
    match uu____399 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.mark dsenv in
        let env1 = FStar_TypeChecker_Env.mark env in
        (FStar_Options.push (); (dsenv1, env1))
let reset_mark uu____427 =
  match uu____427 with
  | (uu____432,env) ->
      let dsenv = FStar_ToSyntax_Env.reset_mark () in
      let env1 = FStar_TypeChecker_Env.reset_mark env in
      (FStar_Options.pop (); (dsenv, env1))
let cleanup uu____447 =
  match uu____447 with
  | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
let commit_mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____464  ->
    match uu____464 with
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
  fun uu____507  ->
    fun curmod  ->
      fun frag  ->
        match uu____507 with
        | (dsenv,env) ->
            (try
               let uu____565 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag in
               match uu____565 with
               | FStar_Pervasives_Native.Some (m,dsenv1,env1) ->
                   let uu____605 =
                     let uu____618 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____618) in
                   FStar_Pervasives_Native.Some uu____605
               | uu____637 -> FStar_Pervasives_Native.None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____677 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____677 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____700 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____700 ->
                 ((let uu____702 =
                     let uu____709 =
                       let uu____714 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____714) in
                     [uu____709] in
                   FStar_TypeChecker_Err.add_errors env uu____702);
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
    let uu____749 =
      FStar_List.partition
        (fun x  ->
           let uu____759 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____760 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____759 <> uu____760) deps in
    match uu____749 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____787 =
                  (let uu____788 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____788) ||
                    (let uu____789 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____789) in
                if uu____787
                then
                  let uu____790 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____790
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____793 ->
              ((let uu____797 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____797);
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
            | uu____847 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____866 =
                    let uu____867 = FStar_Options.lax () in
                    if uu____867 then LaxCheck else FullCheck in
                  push env uu____866 true "typecheck_modul" in
                let uu____869 = tc_one_file remaining env1 in
                (match uu____869 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____920 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____933 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____933
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____920 with
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
                 | (uu____1029,uu____1030) ->
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
                     | uu____1125 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1153 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1236::ts3 ->
                    (pop env1 "";
                     (let uu____1277 =
                        let uu____1292 = FStar_List.hd stack in
                        let uu____1301 = FStar_List.tl stack in
                        (uu____1292, uu____1301) in
                      match uu____1277 with
                      | ((env2,uu____1327),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1391 = ts_elt in
                  (match uu____1391 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1422 = match_dep depnames intf impl in
                       (match uu____1422 with
                        | (b,depnames') ->
                            let uu____1441 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1441
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1462 =
                                 let uu____1477 = FStar_List.hd st in
                                 let uu____1486 = FStar_List.tl st in
                                 (uu____1477, uu____1486) in
                               match uu____1462 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1563 = deps_of_our_file filename in
            match uu____1563 with
            | (filenames,uu____1579) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___198_1638  ->
    match uu___198_1638 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1642 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1642
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1644 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1647 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1664 -> true
    | uu____1669 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1684 -> uu____1684
let js_fail expected got = raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___199_1703  ->
    match uu___199_1703 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___200_1708  ->
    match uu___200_1708 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list k uu___201_1727 =
  match uu___201_1727 with
  | FStar_Util.JsonList l -> FStar_List.map k l
  | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___202_1744  ->
    match uu___202_1744 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1768 = js_str s in
    match uu____1768 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1769 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1773 = js_str s in
    match uu____1773 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | uu____1774 -> js_fail "reduction rule" s
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
    match projectee with | Exit  -> true | uu____1844 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1848 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1852 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1856 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1871 -> false
let __proj__Push__item___0:
  query' ->
    (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1913 -> false
let __proj__AutoComplete__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____1941 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,(Prims.string,Prims.int,Prims.int)
                    FStar_Pervasives_Native.tuple3
                    FStar_Pervasives_Native.option,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2009 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2045 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2057 -> false
let __proj__ProtocolViolation__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0
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
    | InvalidQuery uu____2081 -> true
    | uu____2082 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2089 -> uu____2089
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2093 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2097 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2101 -> false
let try_assoc key a =
  let uu____2130 =
    FStar_Util.try_find
      (fun uu____2141  -> match uu____2141 with | (k,uu____2147) -> k = key)
      a in
  FStar_Util.map_option FStar_Pervasives_Native.snd uu____2130
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2161 =
          let uu____2162 =
            let uu____2163 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2163 in
          ProtocolViolation uu____2162 in
        { qq = uu____2161; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2189 = try_assoc key a in
      match uu____2189 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2193 =
            let uu____2194 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____2194 in
          raise uu____2193 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____2209 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2209 js_str in
    try
      let query =
        let uu____2212 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____2212 js_str in
      let args =
        let uu____2220 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____2220 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____2237 = try_assoc k args in
        match uu____2237 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____2245 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____2246 =
              let uu____2257 =
                let uu____2258 = arg "kind" in
                FStar_All.pipe_right uu____2258 js_pushkind in
              let uu____2259 =
                let uu____2260 = arg "code" in
                FStar_All.pipe_right uu____2260 js_str in
              let uu____2261 =
                let uu____2262 = arg "line" in
                FStar_All.pipe_right uu____2262 js_int in
              let uu____2263 =
                let uu____2264 = arg "column" in
                FStar_All.pipe_right uu____2264 js_int in
              (uu____2257, uu____2259, uu____2261, uu____2263,
                (query = "peek")) in
            Push uu____2246
        | "push" ->
            let uu____2265 =
              let uu____2276 =
                let uu____2277 = arg "kind" in
                FStar_All.pipe_right uu____2277 js_pushkind in
              let uu____2278 =
                let uu____2279 = arg "code" in
                FStar_All.pipe_right uu____2279 js_str in
              let uu____2280 =
                let uu____2281 = arg "line" in
                FStar_All.pipe_right uu____2281 js_int in
              let uu____2282 =
                let uu____2283 = arg "column" in
                FStar_All.pipe_right uu____2283 js_int in
              (uu____2276, uu____2278, uu____2280, uu____2282,
                (query = "peek")) in
            Push uu____2265
        | "autocomplete" ->
            let uu____2284 =
              let uu____2285 = arg "partial-symbol" in
              FStar_All.pipe_right uu____2285 js_str in
            AutoComplete uu____2284
        | "lookup" ->
            let uu____2286 =
              let uu____2303 =
                let uu____2304 = arg "symbol" in
                FStar_All.pipe_right uu____2304 js_str in
              let uu____2305 =
                let uu____2314 =
                  let uu____2323 = try_arg "location" in
                  FStar_All.pipe_right uu____2323
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____2314
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____2377 =
                          let uu____2378 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____2378 js_str in
                        let uu____2379 =
                          let uu____2380 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____2380 js_int in
                        let uu____2381 =
                          let uu____2382 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____2382 js_int in
                        (uu____2377, uu____2379, uu____2381))) in
              let uu____2383 =
                let uu____2386 = arg "requested-info" in
                FStar_All.pipe_right uu____2386 (js_list js_str) in
              (uu____2303, uu____2305, uu____2383) in
            Lookup uu____2286
        | "compute" ->
            let uu____2399 =
              let uu____2408 =
                let uu____2409 = arg "term" in
                FStar_All.pipe_right uu____2409 js_str in
              let uu____2410 =
                let uu____2415 = try_arg "rules" in
                FStar_All.pipe_right uu____2415
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____2408, uu____2410) in
            Compute uu____2399
        | "search" ->
            let uu____2430 =
              let uu____2431 = arg "terms" in
              FStar_All.pipe_right uu____2431 js_str in
            Search uu____2430
        | uu____2432 ->
            let uu____2433 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____2433 in
      { qq = uu____2245; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let validate_interactive_query: query -> query =
  fun uu___203_2440  ->
    match uu___203_2440 with
    | { qq = Push (SyntaxCheck ,uu____2441,uu____2442,uu____2443,false );
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
      let uu____2450 = FStar_Util.read_line stream in
      match uu____2450 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some line ->
          let uu____2454 = FStar_Util.json_of_string line in
          (match uu____2454 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               let uu____2458 = unpack_interactive_query request in
               validate_interactive_query uu____2458)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let rec json_of_fstar_option: FStar_Options.option_val -> FStar_Util.json =
  fun uu___204_2465  ->
    match uu___204_2465 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____2473 = FStar_List.map json_of_fstar_option vs in
        FStar_Util.JsonList uu____2473
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let json_of_opt json_of_a opt_a =
  let uu____2497 = FStar_Util.map_option json_of_a opt_a in
  FStar_Util.dflt FStar_Util.JsonNull uu____2497
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____2503 =
      let uu____2506 =
        let uu____2507 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____2507 in
      let uu____2508 =
        let uu____2511 =
          let uu____2512 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____2512 in
        [uu____2511] in
      uu____2506 :: uu____2508 in
    FStar_Util.JsonList uu____2503
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____2522 =
          let uu____2529 =
            let uu____2536 =
              let uu____2541 = json_of_pos b in ("beg", uu____2541) in
            let uu____2542 =
              let uu____2549 =
                let uu____2554 = json_of_pos e in ("end", uu____2554) in
              [uu____2549] in
            uu____2536 :: uu____2542 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____2529 in
        FStar_Util.JsonAssoc uu____2522
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2574 = FStar_Range.file_of_use_range r in
    let uu____2575 = FStar_Range.start_of_use_range r in
    let uu____2576 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____2574 uu____2575 uu____2576
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2580 = FStar_Range.file_of_range r in
    let uu____2581 = FStar_Range.start_of_range r in
    let uu____2582 = FStar_Range.end_of_range r in
    json_of_range_fields uu____2580 uu____2581 uu____2582
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
    let uu____2589 =
      let uu____2596 =
        let uu____2603 =
          let uu____2610 =
            let uu____2615 =
              let uu____2616 =
                let uu____2619 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____2625 = json_of_use_range r in [uu____2625] in
                let uu____2626 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____2632 = json_of_def_range r in [uu____2632]
                  | uu____2633 -> [] in
                FStar_List.append uu____2619 uu____2626 in
              FStar_Util.JsonList uu____2616 in
            ("ranges", uu____2615) in
          [uu____2610] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____2603 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____2596 in
    FStar_Util.JsonAssoc uu____2589
type lookup_result =
  {
  lr_name: Prims.string;
  lr_def_range: FStar_Range.range FStar_Pervasives_Native.option;
  lr_typ: Prims.string FStar_Pervasives_Native.option;
  lr_doc: Prims.string FStar_Pervasives_Native.option;
  lr_def: Prims.string FStar_Pervasives_Native.option;}
let json_of_lookup_result: lookup_result -> FStar_Util.json =
  fun lr  ->
    let uu____2719 =
      let uu____2726 =
        let uu____2733 =
          let uu____2738 = json_of_opt json_of_def_range lr.lr_def_range in
          ("defined-at", uu____2738) in
        let uu____2739 =
          let uu____2746 =
            let uu____2751 =
              json_of_opt (fun _0_33  -> FStar_Util.JsonStr _0_33) lr.lr_typ in
            ("type", uu____2751) in
          let uu____2752 =
            let uu____2759 =
              let uu____2764 =
                json_of_opt (fun _0_34  -> FStar_Util.JsonStr _0_34)
                  lr.lr_doc in
              ("documentation", uu____2764) in
            let uu____2765 =
              let uu____2772 =
                let uu____2777 =
                  json_of_opt (fun _0_35  -> FStar_Util.JsonStr _0_35)
                    lr.lr_def in
                ("definition", uu____2777) in
              [uu____2772] in
            uu____2759 :: uu____2765 in
          uu____2746 :: uu____2752 in
        uu____2733 :: uu____2739 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____2726 in
    FStar_Util.JsonAssoc uu____2719
let json_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____2810 =
      FStar_List.map (fun _0_36  -> FStar_Util.JsonStr _0_36)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_37  -> FStar_Util.JsonList _0_37) uu____2810 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____2831 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____2831);
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
let write_message: Prims.string -> Prims.string -> Prims.unit =
  fun level  ->
    fun contents  ->
      write_json
        (FStar_Util.JsonAssoc
           [("kind", (FStar_Util.JsonStr "message"));
           ("level", (FStar_Util.JsonStr level));
           ("contents", (FStar_Util.JsonStr contents))])
let write_hello: Prims.unit -> Prims.unit =
  fun uu____2887  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____2890 =
        FStar_List.map (fun _0_38  -> FStar_Util.JsonStr _0_38)
          interactive_protocol_features in
      FStar_Util.JsonList uu____2890 in
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
let json_of_repl_state:
  repl_state ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun st  ->
    let opts_and_defaults =
      let opt_docs =
        let uu____2986 = FStar_Options.docs () in
        FStar_Util.smap_of_list uu____2986 in
      let get_doc k = FStar_Util.smap_try_find opt_docs k in
      FStar_List.map
        (fun uu____3013  ->
           match uu____3013 with
           | (k,v1) ->
               let uu____3030 = FStar_Options.get_option k in
               let uu____3031 = get_doc k in (k, uu____3030, uu____3031, v1))
        FStar_Options.defaults in
    let uu____3036 =
      let uu____3041 =
        let uu____3042 =
          FStar_List.map
            (fun uu____3057  ->
               match uu____3057 with
               | (uu____3070,fstname,uu____3072,uu____3073) ->
                   FStar_Util.JsonStr fstname) st.repl_ts in
        FStar_Util.JsonList uu____3042 in
      ("loaded-dependencies", uu____3041) in
    let uu____3082 =
      let uu____3089 =
        let uu____3094 =
          let uu____3095 =
            FStar_List.map
              (fun uu____3108  ->
                 match uu____3108 with
                 | (name,value,doc1,dflt1) ->
                     let uu____3127 =
                       let uu____3134 =
                         let uu____3141 =
                           let uu____3146 = json_of_fstar_option value in
                           ("value", uu____3146) in
                         let uu____3147 =
                           let uu____3154 =
                             let uu____3159 = json_of_fstar_option dflt1 in
                             ("default", uu____3159) in
                           let uu____3160 =
                             let uu____3167 =
                               let uu____3172 =
                                 json_of_opt
                                   (fun _0_39  -> FStar_Util.JsonStr _0_39)
                                   doc1 in
                               ("documentation", uu____3172) in
                             [uu____3167] in
                           uu____3154 :: uu____3160 in
                         uu____3141 :: uu____3147 in
                       ("name", (FStar_Util.JsonStr name)) :: uu____3134 in
                     FStar_Util.JsonAssoc uu____3127) opts_and_defaults in
          FStar_Util.JsonList uu____3095 in
        ("options", uu____3094) in
      [uu____3089] in
    uu____3036 :: uu____3082
let run_exit st =
  ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol st =
  ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
    (FStar_Util.Inl st))
let run_describe_repl st =
  let uu____3282 =
    let uu____3287 =
      let uu____3288 = json_of_repl_state st in
      FStar_Util.JsonAssoc uu____3288 in
    (QueryOK, uu____3287) in
  (uu____3282, (FStar_Util.Inl st))
let run_protocol_violation st message =
  ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
    (FStar_Util.Inl st))
let nothing_left_to_pop: repl_state -> Prims.bool =
  fun st  ->
    (FStar_List.length st.repl_stack) <= (FStar_List.length st.repl_ts)
let run_pop st =
  if nothing_left_to_pop st
  then
    ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
  else
    (match st.repl_stack with
     | [] -> failwith "impossible"
     | (env,curmod)::stack ->
         (pop st.repl_env "#pop";
          (let st' =
             let uu___215_3427 = st in
             {
               repl_line = (uu___215_3427.repl_line);
               repl_column = (uu___215_3427.repl_column);
               repl_fname = (uu___215_3427.repl_fname);
               repl_stack = stack;
               repl_curmod = curmod;
               repl_env = env;
               repl_ts = (uu___215_3427.repl_ts);
               repl_stdin = (uu___215_3427.repl_stdin)
             } in
           if nothing_left_to_pop st' then cleanup env else ();
           ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))))
let run_push st kind text1 line column1 peek_only =
  let uu____3482 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
  match uu____3482 with
  | (stack,env,ts) ->
      let uu____3504 =
        if nothing_left_to_pop st
        then
          let uu____3525 =
            update_deps st.repl_fname st.repl_curmod stack env ts in
          (true, uu____3525)
        else (false, (stack, env, ts)) in
      (match uu____3504 with
       | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
           let stack2 = (env1, (st.repl_curmod)) :: stack1 in
           let env2 = push env1 kind restore_cmd_line_options1 "#push" in
           let env_mark = mark env2 in
           let frag =
             {
               FStar_Parser_ParseIt.frag_text = text1;
               FStar_Parser_ParseIt.frag_line = line;
               FStar_Parser_ParseIt.frag_col = column1
             } in
           let res = check_frag env_mark st.repl_curmod (frag, false) in
           let errors =
             let uu____3607 = FStar_Errors.report_all () in
             FStar_All.pipe_right uu____3607 (FStar_List.map json_of_issue) in
           (FStar_Errors.clear ();
            (let st' =
               let uu___216_3616 = st in
               {
                 repl_line = line;
                 repl_column = column1;
                 repl_fname = (uu___216_3616.repl_fname);
                 repl_stack = stack2;
                 repl_curmod = (uu___216_3616.repl_curmod);
                 repl_env = (uu___216_3616.repl_env);
                 repl_ts = ts1;
                 repl_stdin = (uu___216_3616.repl_stdin)
               } in
             match res with
             | FStar_Pervasives_Native.Some (curmod,env3,nerrs) when
                 (nerrs = (Prims.parse_int "0")) && (peek_only = false) ->
                 let env4 = commit_mark env3 in
                 ((QueryOK, (FStar_Util.JsonList errors)),
                   (FStar_Util.Inl
                      (let uu___217_3669 = st' in
                       {
                         repl_line = (uu___217_3669.repl_line);
                         repl_column = (uu___217_3669.repl_column);
                         repl_fname = (uu___217_3669.repl_fname);
                         repl_stack = (uu___217_3669.repl_stack);
                         repl_curmod = curmod;
                         repl_env = env4;
                         repl_ts = (uu___217_3669.repl_ts);
                         repl_stdin = (uu___217_3669.repl_stdin)
                       })))
             | uu____3670 ->
                 let env3 = reset_mark env_mark in
                 let uu____3690 =
                   run_pop
                     (let uu___218_3703 = st' in
                      {
                        repl_line = (uu___218_3703.repl_line);
                        repl_column = (uu___218_3703.repl_column);
                        repl_fname = (uu___218_3703.repl_fname);
                        repl_stack = (uu___218_3703.repl_stack);
                        repl_curmod = (uu___218_3703.repl_curmod);
                        repl_env = env3;
                        repl_ts = (uu___218_3703.repl_ts);
                        repl_stdin = (uu___218_3703.repl_stdin)
                      }) in
                 (match uu____3690 with
                  | (uu____3716,st'') ->
                      let status = if peek_only then QueryOK else QueryNOK in
                      ((status, (FStar_Util.JsonList errors)), st'')))))
let run_lookup st symbol pos_opt requested_info =
  let uu____3798 = st.repl_env in
  match uu____3798 with
  | (dsenv,tcenv) ->
      let info_of_lid_str lid_str =
        let lid =
          let uu____3830 =
            FStar_List.map FStar_Ident.id_of_text
              (FStar_Util.split lid_str ".") in
          FStar_Ident.lid_of_ids uu____3830 in
        let lid1 =
          let uu____3834 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid in
          FStar_All.pipe_left (FStar_Util.dflt lid) uu____3834 in
        let uu____3839 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
        FStar_All.pipe_right uu____3839
          (FStar_Util.map_option
             (fun uu____3890  ->
                match uu____3890 with
                | ((uu____3909,typ),r) -> ((FStar_Util.Inr lid1), typ, r))) in
      let docs_of_lid lid =
        let uu____3926 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
        FStar_All.pipe_right uu____3926
          (FStar_Util.map_option FStar_Pervasives_Native.fst) in
      let def_of_lid lid =
        let uu____3955 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
        FStar_Util.bind_opt uu____3955
          (fun uu___205_3994  ->
             match uu___205_3994 with
             | (FStar_Util.Inr (se,uu____4016),uu____4017) ->
                 let uu____4046 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Pervasives_Native.Some uu____4046
             | uu____4047 -> FStar_Pervasives_Native.None) in
      let info_at_pos_opt =
        FStar_Util.bind_opt pos_opt
          (fun uu____4095  ->
             match uu____4095 with
             | (file,row,col) ->
                 FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
      let info_opt =
        match info_at_pos_opt with
        | FStar_Pervasives_Native.Some uu____4142 -> info_at_pos_opt
        | FStar_Pervasives_Native.None  ->
            if symbol = ""
            then FStar_Pervasives_Native.None
            else info_of_lid_str symbol in
      let response =
        match info_opt with
        | FStar_Pervasives_Native.None  -> (QueryNOK, FStar_Util.JsonNull)
        | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
            let name =
              match name_or_lid with
              | FStar_Util.Inl name -> name
              | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid in
            let typ_str =
              if FStar_List.mem "type" requested_info
              then
                let uu____4244 =
                  FStar_TypeChecker_Normalize.term_to_string tcenv typ in
                FStar_Pervasives_Native.Some uu____4244
              else FStar_Pervasives_Native.None in
            let doc_str =
              match name_or_lid with
              | FStar_Util.Inr lid when
                  FStar_List.mem "documentation" requested_info ->
                  docs_of_lid lid
              | uu____4252 -> FStar_Pervasives_Native.None in
            let def_str =
              match name_or_lid with
              | FStar_Util.Inr lid when
                  FStar_List.mem "definition" requested_info ->
                  def_of_lid lid
              | uu____4263 -> FStar_Pervasives_Native.None in
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
            let uu____4275 = json_of_lookup_result result in
            (QueryOK, uu____4275) in
      (response, (FStar_Util.Inl st))
let run_completions st search_term =
  let uu____4308 = st.repl_env in
  match uu____4308 with
  | (dsenv,tcenv) ->
      let rec measure_anchored_match search_term1 candidate =
        match (search_term1, candidate) with
        | ([],uu____4358) ->
            FStar_Pervasives_Native.Some ([], (Prims.parse_int "0"))
        | (uu____4373,[]) -> FStar_Pervasives_Native.None
        | (hs::ts,hc::tc) ->
            let hc_text = FStar_Ident.text_of_id hc in
            if FStar_Util.starts_with hc_text hs
            then
              (match ts with
               | [] ->
                   FStar_Pervasives_Native.Some
                     (candidate, (FStar_String.length hs))
               | uu____4423 ->
                   let uu____4426 = measure_anchored_match ts tc in
                   FStar_All.pipe_right uu____4426
                     (FStar_Util.map_option
                        (fun uu____4463  ->
                           match uu____4463 with
                           | (matched,len) ->
                               ((hc :: matched),
                                 (((FStar_String.length hc_text) +
                                     (Prims.parse_int "1"))
                                    + len)))))
            else FStar_Pervasives_Native.None in
      let rec locate_match needle candidate =
        let uu____4518 = measure_anchored_match needle candidate in
        match uu____4518 with
        | FStar_Pervasives_Native.Some (matched,n1) ->
            FStar_Pervasives_Native.Some ([], matched, n1)
        | FStar_Pervasives_Native.None  ->
            (match candidate with
             | [] -> FStar_Pervasives_Native.None
             | hc::tc ->
                 let uu____4597 = locate_match needle tc in
                 FStar_All.pipe_right uu____4597
                   (FStar_Util.map_option
                      (fun uu____4654  ->
                         match uu____4654 with
                         | (prefix1,matched,len) ->
                             ((hc :: prefix1), matched, len)))) in
      let str_of_ids ids =
        let uu____4698 = FStar_List.map FStar_Ident.text_of_id ids in
        FStar_Util.concat_l "." uu____4698 in
      let match_lident_against needle lident =
        locate_match needle
          (FStar_List.append lident.FStar_Ident.ns [lident.FStar_Ident.ident]) in
      let shorten_namespace uu____4745 =
        match uu____4745 with
        | (prefix1,matched,match_len) ->
            let naked_match =
              match matched with
              | uu____4776::[] -> true
              | uu____4777 -> false in
            let uu____4780 =
              FStar_ToSyntax_Env.shorten_module_path dsenv prefix1
                naked_match in
            (match uu____4780 with
             | (stripped_ns,shortened) ->
                 let uu____4807 = str_of_ids shortened in
                 let uu____4808 = str_of_ids matched in
                 let uu____4809 = str_of_ids stripped_ns in
                 (uu____4807, uu____4808, uu____4809, match_len)) in
      let prepare_candidate uu____4827 =
        match uu____4827 with
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
                   ((FStar_String.length s) + out) + (Prims.parse_int "1"))
              (FStar_String.length id) orig_ns in
          FStar_All.pipe_right exported_names
            (FStar_List.filter_map
               (fun n1  ->
                  if FStar_Util.starts_with n1 id
                  then
                    let lid =
                      FStar_Ident.lid_of_ns_and_id (FStar_Ident.ids_of_lid m)
                        (FStar_Ident.id_of_text n1) in
                    let uu____4950 =
                      FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                        dsenv lid in
                    FStar_Option.map
                      (fun fqn  ->
                         let uu____4964 =
                           let uu____4967 =
                             FStar_List.map FStar_Ident.id_of_text orig_ns in
                           FStar_List.append uu____4967
                             [fqn.FStar_Ident.ident] in
                         ([], uu____4964, matched_length)) uu____4950
                  else FStar_Pervasives_Native.None)) in
        let case_b_find_matches_in_env uu____5000 =
          let matches =
            FStar_List.filter_map (match_lident_against needle)
              all_lidents_in_env in
          FStar_All.pipe_right matches
            (FStar_List.filter
               (fun uu____5070  ->
                  match uu____5070 with
                  | (ns,id,uu____5083) ->
                      let uu____5092 =
                        let uu____5095 = FStar_Ident.lid_of_ids id in
                        FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                          dsenv uu____5095 in
                      (match uu____5092 with
                       | FStar_Pervasives_Native.None  -> false
                       | FStar_Pervasives_Native.Some l ->
                           let uu____5097 =
                             FStar_Ident.lid_of_ids (FStar_List.append ns id) in
                           FStar_Ident.lid_equals l uu____5097))) in
        let uu____5098 = FStar_Util.prefix needle in
        match uu____5098 with
        | (ns,id) ->
            let matched_ids =
              match ns with
              | [] -> case_b_find_matches_in_env ()
              | uu____5144 ->
                  let l = FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
                  let uu____5148 =
                    FStar_ToSyntax_Env.resolve_module_name dsenv l true in
                  (match uu____5148 with
                   | FStar_Pervasives_Native.None  ->
                       case_b_find_matches_in_env ()
                   | FStar_Pervasives_Native.Some m ->
                       case_a_find_transitive_includes ns m id) in
            FStar_All.pipe_right matched_ids
              (FStar_List.map
                 (fun x  ->
                    let uu____5211 = shorten_namespace x in
                    prepare_candidate uu____5211)) in
      let json_candidates =
        let uu____5223 =
          FStar_Util.sort_with
            (fun uu____5238  ->
               fun uu____5239  ->
                 match (uu____5238, uu____5239) with
                 | ((cd1,ns1,uu____5266),(cd2,ns2,uu____5269)) ->
                     (match FStar_String.compare cd1 cd2 with
                      | _0_40 when _0_40 = (Prims.parse_int "0") ->
                          FStar_String.compare ns1 ns2
                      | n1 -> n1)) matches in
        FStar_List.map
          (fun uu____5289  ->
             match uu____5289 with
             | (candidate,ns,match_len) ->
                 FStar_Util.JsonList
                   [FStar_Util.JsonInt match_len;
                   FStar_Util.JsonStr ns;
                   FStar_Util.JsonStr candidate]) uu____5223 in
      ((QueryOK, (FStar_Util.JsonList json_candidates)), (FStar_Util.Inl st))
let run_compute st term rules =
  let run_and_rewind st1 task =
    let env_mark = mark st1.repl_env in
    let results = task st1 in
    let env = reset_mark env_mark in
    let st' =
      let uu___219_5392 = st1 in
      {
        repl_line = (uu___219_5392.repl_line);
        repl_column = (uu___219_5392.repl_column);
        repl_fname = (uu___219_5392.repl_fname);
        repl_stack = (uu___219_5392.repl_stack);
        repl_curmod = (uu___219_5392.repl_curmod);
        repl_env = env;
        repl_ts = (uu___219_5392.repl_ts);
        repl_stdin = (uu___219_5392.repl_stdin)
      } in
    (results, (FStar_Util.Inl st')) in
  let dummy_let_fragment term1 =
    let dummy_decl = FStar_Util.format1 "let __compute_dummy__ = (%s)" term1 in
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
          ((uu____5436,{ FStar_Syntax_Syntax.lbname = uu____5437;
                         FStar_Syntax_Syntax.lbunivs = uu____5438;
                         FStar_Syntax_Syntax.lbtyp = uu____5439;
                         FStar_Syntax_Syntax.lbeff = uu____5440;
                         FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____5442,uu____5443);
        FStar_Syntax_Syntax.sigrng = uu____5444;
        FStar_Syntax_Syntax.sigquals = uu____5445;
        FStar_Syntax_Syntax.sigmeta = uu____5446;_}::[] ->
        FStar_Pervasives_Native.Some def
    | uu____5483 -> FStar_Pervasives_Native.None in
  let parse1 frag =
    let uu____5498 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
    match uu____5498 with
    | FStar_Util.Inl (FStar_Util.Inr decls,uu____5522) ->
        FStar_Pervasives_Native.Some decls
    | uu____5567 -> FStar_Pervasives_Native.None in
  let desugar dsenv decls =
    let uu____5599 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
    FStar_Pervasives_Native.snd uu____5599 in
  let typecheck tcenv decls =
    let uu____5617 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
    match uu____5617 with | (ses,uu____5631,uu____5632) -> ses in
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
       let uu____5654 = st1.repl_env in
       match uu____5654 with
       | (dsenv,tcenv) ->
           let frag = dummy_let_fragment term in
           (match st1.repl_curmod with
            | FStar_Pervasives_Native.None  ->
                (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
            | uu____5666 ->
                let uu____5667 = parse1 frag in
                (match uu____5667 with
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
                            let normalized = normalize_term1 tcenv rules1 def in
                            let uu____5714 =
                              let uu____5715 =
                                FStar_Syntax_Print.term_to_string normalized in
                              FStar_Util.JsonStr uu____5715 in
                            (QueryOK, uu____5714)
                      with
                      | e ->
                          let uu____5722 =
                            let uu____5723 = FStar_Errors.issue_of_exn e in
                            match uu____5723 with
                            | FStar_Pervasives_Native.Some issue ->
                                let uu____5727 =
                                  FStar_Errors.format_issue issue in
                                FStar_Util.JsonStr uu____5727
                            | FStar_Pervasives_Native.None  -> raise e in
                          (QueryNOK, uu____5722)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____5748 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____5760 -> false
let __proj__TypeContainsLid__item___0: search_term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0
let st_cost: search_term' -> Prims.int =
  fun uu___206_5778  ->
    match uu___206_5778 with
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
let sc_of_lid: FStar_Ident.lid -> search_candidate =
  fun lid  ->
    let uu____5844 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____5851 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____5844; sc_fvars = uu____5851 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____5874 = FStar_ST.read sc.sc_typ in
      match uu____5874 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____5885 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____5885 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____5908,typ),uu____5910) ->
                typ in
          (FStar_ST.write sc.sc_typ (FStar_Pervasives_Native.Some typ); typ)
let sc_fvars:
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lid FStar_Util.set
  =
  fun tcenv  ->
    fun sc  ->
      let uu____5938 = FStar_ST.read sc.sc_fvars in
      match uu____5938 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____5959 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____5959 in
          (FStar_ST.write sc.sc_fvars (FStar_Pervasives_Native.Some fv); fv)
let json_of_search_result:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json
  =
  fun dsenv  ->
    fun tcenv  ->
      fun sc  ->
        let typ_str =
          let uu____5977 = sc_typ tcenv sc in
          FStar_Syntax_Print.term_to_string uu____5977 in
        let uu____5978 =
          let uu____5985 =
            let uu____5990 =
              let uu____5991 =
                let uu____5992 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____5992.FStar_Ident.str in
              FStar_Util.JsonStr uu____5991 in
            ("lid", uu____5990) in
          [uu____5985; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____5978
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____6011 -> true
    | uu____6012 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____6019 -> uu____6019
let run_search st search_str =
  let uu____6044 = st.repl_env in
  match uu____6044 with
  | (dsenv,tcenv) ->
      let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
      let st_matches candidate term =
        let found =
          match term.st_term with
          | NameContainsStr str ->
              FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
          | TypeContainsLid lid ->
              let uu____6072 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____6072 in
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
            then raise (InvalidSearch "Empty search term")
            else
              FStar_Util.substring str (Prims.parse_int "1")
                ((FStar_String.length term1) - (Prims.parse_int "2")) in
          let parsed =
            if beg_quote <> end_quote
            then
              let uu____6096 =
                let uu____6097 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____6097 in
              raise uu____6096
            else
              if beg_quote
              then
                (let uu____6099 = strip_quotes term1 in
                 NameContainsStr uu____6099)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____6102 =
                   FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                     lid in
                 match uu____6102 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____6105 =
                       let uu____6106 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____6106 in
                     raise uu____6105
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____6122 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.strcat (if term.st_negate then "-" else "") uu____6122 in
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
            FStar_Options.with_saved_options
              (fun uu____6171  ->
                 FStar_Options.set_option "print_effect_args"
                   (FStar_Options.Bool true);
                 FStar_List.map (json_of_search_result dsenv tcenv) sorted1) in
          match results with
          | [] ->
              let kwds =
                let uu____6178 = FStar_List.map pprint_one terms in
                FStar_Util.concat_l " " uu____6178 in
              let uu____6181 =
                let uu____6182 =
                  FStar_Util.format1 "No results found for query [%s]" kwds in
                InvalidSearch uu____6182 in
              raise uu____6181
          | uu____6187 -> (QueryOK, (FStar_Util.JsonList js))
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
    fun uu___207_6235  ->
      match uu___207_6235 with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | DescribeRepl  -> run_describe_repl st
      | Pop  -> run_pop st
      | Push (kind,text1,l,c,peek) -> run_push st kind text1 l c peek
      | AutoComplete search_term -> run_completions st search_term
      | Lookup (symbol,pos_opt,rqi) -> run_lookup st symbol pos_opt rqi
      | Compute (term,rules) -> run_compute st term rules
      | Search term -> run_search st term
      | ProtocolViolation query -> run_protocol_violation st query
let rec go: repl_state -> Prims.unit =
  fun st  ->
    let query = read_interactive_query st.repl_stdin in
    let uu____6293 = let uu____6306 = run_query st in uu____6306 query.qq in
    match uu____6293 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____6350 = let uu____6353 = FStar_ST.read issues in e :: uu____6353 in
    FStar_ST.write issues uu____6350 in
  let count_errors uu____6367 =
    let uu____6368 =
      let uu____6371 = FStar_ST.read issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____6371 in
    FStar_List.length uu____6368 in
  let report1 uu____6384 =
    let uu____6385 = FStar_ST.read issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____6385 in
  let clear1 uu____6395 = FStar_ST.write issues [] in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report1;
    FStar_Errors.eh_clear = clear1
  }
let interactive_printer: FStar_Util.printer =
  {
    FStar_Util.printer_prinfo = (write_message "info");
    FStar_Util.printer_prwarning = (write_message "warning");
    FStar_Util.printer_prerror = (write_message "error")
  }
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let uu____6406 = deps_of_our_file filename in
     match uu____6406 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____6430 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu____6430 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____6457 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____6458 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____6457 uu____6458 in
              let env2 =
                let uu____6464 =
                  FStar_TypeChecker_Env.set_range
                    (FStar_Pervasives_Native.snd env1) initial_range in
                ((FStar_Pervasives_Native.fst env1), uu____6464) in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2 in
              let init_st =
                let uu____6476 = FStar_Util.open_stdin () in
                {
                  repl_line = (Prims.parse_int "1");
                  repl_column = (Prims.parse_int "0");
                  repl_fname = filename;
                  repl_stack = stack;
                  repl_curmod = FStar_Pervasives_Native.None;
                  repl_env = env3;
                  repl_ts = ts;
                  repl_stdin = uu____6476
                } in
              let uu____6477 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ()) in
              if uu____6477
              then
                let uu____6478 =
                  let uu____6479 = FStar_Options.file_list () in
                  FStar_List.hd uu____6479 in
                FStar_SMTEncoding_Solver.with_hints_db uu____6478
                  (fun uu____6482  -> go init_st)
              else go init_st))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    FStar_Errors.set_handler interactive_error_handler;
    (let uu____6490 =
       let uu____6491 = FStar_Options.codegen () in
       FStar_Option.isSome uu____6491 in
     if uu____6490
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (try interactive_mode' filename
     with
     | e -> (FStar_Errors.set_handler FStar_Errors.default_handler; raise e))