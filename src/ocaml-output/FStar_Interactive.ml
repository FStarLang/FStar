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
                let uu___195_391 = tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___195_391.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___195_391.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___195_391.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___195_391.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___195_391.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___195_391.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___195_391.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___195_391.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___195_391.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___195_391.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___195_391.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___195_391.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___195_391.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___195_391.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___195_391.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___195_391.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___195_391.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___195_391.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = (kind = LaxCheck);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___195_391.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___195_391.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___195_391.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___195_391.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___195_391.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___195_391.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___195_391.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___195_391.FStar_TypeChecker_Env.is_native_tactic)
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
                 let uu____710 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____710 ->
                 (FStar_TypeChecker_Common.insert_id_info.FStar_TypeChecker_Common.clear
                    ();
                  FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____734 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____734 ->
                 (FStar_TypeChecker_Common.insert_id_info.FStar_TypeChecker_Common.clear
                    ();
                  (let uu____737 =
                     let uu____744 =
                       let uu____749 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____749) in
                     [uu____744] in
                   FStar_TypeChecker_Err.add_errors env uu____737);
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
    let uu____785 =
      FStar_List.partition
        (fun x  ->
           let uu____798 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____799 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____798 <> uu____799) deps in
    match uu____785 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____826 =
                  (let uu____829 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____829) ||
                    (let uu____831 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____831) in
                if uu____826
                then
                  let uu____832 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____832
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____835 ->
              ((let uu____839 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____839);
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
            | uu____894 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____913 =
                    let uu____914 = FStar_Options.lax () in
                    if uu____914 then LaxCheck else FullCheck in
                  push env uu____913 true "typecheck_modul" in
                let uu____916 = tc_one_file remaining env1 in
                (match uu____916 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____967 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____980 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____980
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____967 with
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
                 | (uu____1084,uu____1085) ->
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
                     | uu____1180 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1208 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1291::ts3 ->
                    (pop env1 "";
                     (let uu____1332 =
                        let uu____1347 = FStar_List.hd stack in
                        let uu____1356 = FStar_List.tl stack in
                        (uu____1347, uu____1356) in
                      match uu____1332 with
                      | ((env2,uu____1382),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1446 = ts_elt in
                  (match uu____1446 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1477 = match_dep depnames intf impl in
                       (match uu____1477 with
                        | (b,depnames') ->
                            let uu____1496 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1496
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1517 =
                                 let uu____1532 = FStar_List.hd st in
                                 let uu____1541 = FStar_List.tl st in
                                 (uu____1532, uu____1541) in
                               match uu____1517 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1618 = deps_of_our_file filename in
            match uu____1618 with
            | (filenames,uu____1634) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___185_1694  ->
    match uu___185_1694 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1698 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1698
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1700 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1703 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1721 -> true
    | uu____1726 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1742 -> uu____1742
let js_fail: 'Auu____1753 . Prims.string -> FStar_Util.json -> 'Auu____1753 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___186_1765  ->
    match uu___186_1765 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___187_1771  ->
    match uu___187_1771 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list:
  'Auu____1780 .
    (FStar_Util.json -> 'Auu____1780) ->
      FStar_Util.json -> 'Auu____1780 Prims.list
  =
  fun k  ->
    fun uu___188_1793  ->
      match uu___188_1793 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___189_1811  ->
    match uu___189_1811 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1836 = js_str s in
    match uu____1836 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1837 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1842 = js_str s in
    match uu____1842 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | uu____1843 -> js_fail "reduction rule" s
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
    match projectee with | Exit  -> true | uu____1914 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1919 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1924 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1929 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1945 -> false
let __proj__Push__item___0:
  query' ->
    (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1989 -> false
let __proj__AutoComplete__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2019 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,(Prims.string,Prims.int,Prims.int)
                    FStar_Pervasives_Native.tuple3
                    FStar_Pervasives_Native.option,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2089 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2127 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2141 -> false
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
    | InvalidQuery uu____2171 -> true
    | uu____2172 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2180 -> uu____2180
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2185 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2190 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2195 -> false
let try_assoc:
  'Auu____2204 'Auu____2205 .
    'Auu____2205 ->
      ('Auu____2205,'Auu____2204) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2204 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2228 =
        FStar_Util.try_find
          (fun uu____2242  ->
             match uu____2242 with | (k,uu____2248) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2228
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2265 =
          let uu____2266 =
            let uu____2267 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2267 in
          ProtocolViolation uu____2266 in
        { qq = uu____2265; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2294 = try_assoc key a in
      match uu____2294 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2298 =
            let uu____2299 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____2299 in
          FStar_Exn.raise uu____2298 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____2314 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2314 js_str in
    try
      let query =
        let uu____2323 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____2323 js_str in
      let args =
        let uu____2331 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____2331 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____2348 = try_assoc k args in
        match uu____2348 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____2356 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____2357 =
              let uu____2368 =
                let uu____2369 = arg "kind" in
                FStar_All.pipe_right uu____2369 js_pushkind in
              let uu____2370 =
                let uu____2371 = arg "code" in
                FStar_All.pipe_right uu____2371 js_str in
              let uu____2372 =
                let uu____2373 = arg "line" in
                FStar_All.pipe_right uu____2373 js_int in
              let uu____2374 =
                let uu____2375 = arg "column" in
                FStar_All.pipe_right uu____2375 js_int in
              (uu____2368, uu____2370, uu____2372, uu____2374,
                (query = "peek")) in
            Push uu____2357
        | "push" ->
            let uu____2376 =
              let uu____2387 =
                let uu____2388 = arg "kind" in
                FStar_All.pipe_right uu____2388 js_pushkind in
              let uu____2389 =
                let uu____2390 = arg "code" in
                FStar_All.pipe_right uu____2390 js_str in
              let uu____2391 =
                let uu____2392 = arg "line" in
                FStar_All.pipe_right uu____2392 js_int in
              let uu____2393 =
                let uu____2394 = arg "column" in
                FStar_All.pipe_right uu____2394 js_int in
              (uu____2387, uu____2389, uu____2391, uu____2393,
                (query = "peek")) in
            Push uu____2376
        | "autocomplete" ->
            let uu____2395 =
              let uu____2396 = arg "partial-symbol" in
              FStar_All.pipe_right uu____2396 js_str in
            AutoComplete uu____2395
        | "lookup" ->
            let uu____2397 =
              let uu____2414 =
                let uu____2415 = arg "symbol" in
                FStar_All.pipe_right uu____2415 js_str in
              let uu____2416 =
                let uu____2425 =
                  let uu____2434 = try_arg "location" in
                  FStar_All.pipe_right uu____2434
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____2425
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____2492 =
                          let uu____2493 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____2493 js_str in
                        let uu____2494 =
                          let uu____2495 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____2495 js_int in
                        let uu____2496 =
                          let uu____2497 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____2497 js_int in
                        (uu____2492, uu____2494, uu____2496))) in
              let uu____2498 =
                let uu____2501 = arg "requested-info" in
                FStar_All.pipe_right uu____2501 (js_list js_str) in
              (uu____2414, uu____2416, uu____2498) in
            Lookup uu____2397
        | "compute" ->
            let uu____2514 =
              let uu____2523 =
                let uu____2524 = arg "term" in
                FStar_All.pipe_right uu____2524 js_str in
              let uu____2525 =
                let uu____2530 = try_arg "rules" in
                FStar_All.pipe_right uu____2530
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____2523, uu____2525) in
            Compute uu____2514
        | "search" ->
            let uu____2545 =
              let uu____2546 = arg "terms" in
              FStar_All.pipe_right uu____2546 js_str in
            Search uu____2545
        | uu____2547 ->
            let uu____2548 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____2548 in
      { qq = uu____2356; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let validate_interactive_query: query -> query =
  fun uu___190_2558  ->
    match uu___190_2558 with
    | { qq = Push (SyntaxCheck ,uu____2559,uu____2560,uu____2561,false );
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
      let uu____2571 = FStar_Util.read_line stream in
      match uu____2571 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some line ->
          let uu____2575 = FStar_Util.json_of_string line in
          (match uu____2575 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               let uu____2579 = unpack_interactive_query request in
               validate_interactive_query uu____2579)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let rec json_of_fstar_option: FStar_Options.option_val -> FStar_Util.json =
  fun uu___191_2589  ->
    match uu___191_2589 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____2597 = FStar_List.map json_of_fstar_option vs in
        FStar_Util.JsonList uu____2597
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let json_of_opt:
  'Auu____2606 .
    ('Auu____2606 -> FStar_Util.json) ->
      'Auu____2606 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____2624 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____2624
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____2631 =
      let uu____2634 =
        let uu____2635 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____2635 in
      let uu____2636 =
        let uu____2639 =
          let uu____2640 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____2640 in
        [uu____2639] in
      uu____2634 :: uu____2636 in
    FStar_Util.JsonList uu____2631
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____2653 =
          let uu____2660 =
            let uu____2667 =
              let uu____2672 = json_of_pos b in ("beg", uu____2672) in
            let uu____2673 =
              let uu____2680 =
                let uu____2685 = json_of_pos e in ("end", uu____2685) in
              [uu____2680] in
            uu____2667 :: uu____2673 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____2660 in
        FStar_Util.JsonAssoc uu____2653
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2706 = FStar_Range.file_of_use_range r in
    let uu____2707 = FStar_Range.start_of_use_range r in
    let uu____2708 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____2706 uu____2707 uu____2708
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2713 = FStar_Range.file_of_range r in
    let uu____2714 = FStar_Range.start_of_range r in
    let uu____2715 = FStar_Range.end_of_range r in
    json_of_range_fields uu____2713 uu____2714 uu____2715
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
    let uu____2724 =
      let uu____2731 =
        let uu____2738 =
          let uu____2745 =
            let uu____2750 =
              let uu____2751 =
                let uu____2754 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____2760 = json_of_use_range r in [uu____2760] in
                let uu____2761 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____2767 = json_of_def_range r in [uu____2767]
                  | uu____2768 -> [] in
                FStar_List.append uu____2754 uu____2761 in
              FStar_Util.JsonList uu____2751 in
            ("ranges", uu____2750) in
          [uu____2745] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____2738 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____2731 in
    FStar_Util.JsonAssoc uu____2724
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
    let uu____2920 =
      let uu____2927 =
        let uu____2934 =
          let uu____2939 = json_of_opt json_of_def_range lr.lr_def_range in
          ("defined-at", uu____2939) in
        let uu____2940 =
          let uu____2947 =
            let uu____2952 =
              json_of_opt (fun _0_40  -> FStar_Util.JsonStr _0_40) lr.lr_typ in
            ("type", uu____2952) in
          let uu____2953 =
            let uu____2960 =
              let uu____2965 =
                json_of_opt (fun _0_41  -> FStar_Util.JsonStr _0_41)
                  lr.lr_doc in
              ("documentation", uu____2965) in
            let uu____2966 =
              let uu____2973 =
                let uu____2978 =
                  json_of_opt (fun _0_42  -> FStar_Util.JsonStr _0_42)
                    lr.lr_def in
                ("definition", uu____2978) in
              [uu____2973] in
            uu____2960 :: uu____2966 in
          uu____2947 :: uu____2953 in
        uu____2934 :: uu____2940 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____2927 in
    FStar_Util.JsonAssoc uu____2920
let json_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3011 =
      FStar_List.map (fun _0_43  -> FStar_Util.JsonStr _0_43)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_44  -> FStar_Util.JsonList _0_44) uu____3011 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____3033 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____3033);
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
  fun uu____3095  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____3098 =
        FStar_List.map (fun _0_45  -> FStar_Util.JsonStr _0_45)
          interactive_protocol_features in
      FStar_Util.JsonList uu____3098 in
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
        let uu____3259 = FStar_Options.docs () in
        FStar_Util.smap_of_list uu____3259 in
      let get_doc k = FStar_Util.smap_try_find opt_docs k in
      FStar_List.map
        (fun uu____3291  ->
           match uu____3291 with
           | (k,v1) ->
               let uu____3308 = FStar_Options.get_option k in
               let uu____3309 = get_doc k in (k, uu____3308, uu____3309, v1))
        FStar_Options.defaults in
    let uu____3314 =
      let uu____3319 =
        let uu____3320 =
          FStar_List.map
            (fun uu____3340  ->
               match uu____3340 with
               | (uu____3353,fstname,uu____3355,uu____3356) ->
                   FStar_Util.JsonStr fstname) st.repl_ts in
        FStar_Util.JsonList uu____3320 in
      ("loaded-dependencies", uu____3319) in
    let uu____3365 =
      let uu____3372 =
        let uu____3377 =
          let uu____3378 =
            FStar_List.map
              (fun uu____3397  ->
                 match uu____3397 with
                 | (name,value,doc1,dflt1) ->
                     let uu____3416 =
                       let uu____3423 =
                         let uu____3430 =
                           let uu____3435 = json_of_fstar_option value in
                           ("value", uu____3435) in
                         let uu____3436 =
                           let uu____3443 =
                             let uu____3448 = json_of_fstar_option dflt1 in
                             ("default", uu____3448) in
                           let uu____3449 =
                             let uu____3456 =
                               let uu____3461 =
                                 json_of_opt
                                   (fun _0_46  -> FStar_Util.JsonStr _0_46)
                                   doc1 in
                               ("documentation", uu____3461) in
                             [uu____3456] in
                           uu____3443 :: uu____3449 in
                         uu____3430 :: uu____3436 in
                       ("name", (FStar_Util.JsonStr name)) :: uu____3423 in
                     FStar_Util.JsonAssoc uu____3416) opts_and_defaults in
          FStar_Util.JsonList uu____3378 in
        ("options", uu____3377) in
      [uu____3372] in
    uu____3314 :: uu____3365
let run_exit:
  'Auu____3500 'Auu____3501 .
    'Auu____3501 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3500,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol:
  'Auu____3532 'Auu____3533 .
    'Auu____3533 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3533,'Auu____3532) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl:
  'Auu____3562 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____3562) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____3579 =
      let uu____3584 =
        let uu____3585 = json_of_repl_state st in
        FStar_Util.JsonAssoc uu____3585 in
      (QueryOK, uu____3584) in
    (uu____3579, (FStar_Util.Inl st))
let run_protocol_violation:
  'Auu____3608 'Auu____3609 .
    'Auu____3609 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____3609,'Auu____3608) FStar_Util.either)
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
  'Auu____3662 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____3662) FStar_Util.either)
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
               let uu___202_3731 = st in
               {
                 repl_line = (uu___202_3731.repl_line);
                 repl_column = (uu___202_3731.repl_column);
                 repl_fname = (uu___202_3731.repl_fname);
                 repl_stack = stack;
                 repl_curmod = curmod;
                 repl_env = env;
                 repl_ts = (uu___202_3731.repl_ts);
                 repl_stdin = (uu___202_3731.repl_stdin)
               } in
             if nothing_left_to_pop st' then cleanup env else ();
             ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))))
let run_push:
  'Auu____3756 .
    repl_state ->
      push_kind ->
        Prims.string ->
          Prims.int ->
            Prims.int ->
              Prims.bool ->
                ((query_status,FStar_Util.json)
                   FStar_Pervasives_Native.tuple2,(repl_state,'Auu____3756)
                                                    FStar_Util.either)
                  FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun kind  ->
      fun text1  ->
        fun line  ->
          fun column1  ->
            fun peek_only  ->
              let uu____3793 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
              match uu____3793 with
              | (stack,env,ts) ->
                  let uu____3815 =
                    if nothing_left_to_pop st
                    then
                      let uu____3836 =
                        update_deps st.repl_fname st.repl_curmod stack env ts in
                      (true, uu____3836)
                    else (false, (stack, env, ts)) in
                  (match uu____3815 with
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
                         let uu____3918 = FStar_Errors.report_all () in
                         FStar_All.pipe_right uu____3918
                           (FStar_List.map json_of_issue) in
                       (FStar_Errors.clear ();
                        (let st' =
                           let uu___203_3927 = st in
                           {
                             repl_line = line;
                             repl_column = column1;
                             repl_fname = (uu___203_3927.repl_fname);
                             repl_stack = stack2;
                             repl_curmod = (uu___203_3927.repl_curmod);
                             repl_env = (uu___203_3927.repl_env);
                             repl_ts = ts1;
                             repl_stdin = (uu___203_3927.repl_stdin)
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
                                  (let uu___204_3981 = st' in
                                   {
                                     repl_line = (uu___204_3981.repl_line);
                                     repl_column =
                                       (uu___204_3981.repl_column);
                                     repl_fname = (uu___204_3981.repl_fname);
                                     repl_stack = (uu___204_3981.repl_stack);
                                     repl_curmod = curmod;
                                     repl_env = env4;
                                     repl_ts = (uu___204_3981.repl_ts);
                                     repl_stdin = (uu___204_3981.repl_stdin)
                                   })))
                         | uu____3982 ->
                             let env3 = reset_mark env_mark in
                             let uu____4002 =
                               run_pop
                                 (let uu___205_4016 = st' in
                                  {
                                    repl_line = (uu___205_4016.repl_line);
                                    repl_column = (uu___205_4016.repl_column);
                                    repl_fname = (uu___205_4016.repl_fname);
                                    repl_stack = (uu___205_4016.repl_stack);
                                    repl_curmod = (uu___205_4016.repl_curmod);
                                    repl_env = env3;
                                    repl_ts = (uu___205_4016.repl_ts);
                                    repl_stdin = (uu___205_4016.repl_stdin)
                                  }) in
                             (match uu____4002 with
                              | (uu____4029,st'') ->
                                  let status =
                                    if peek_only then QueryOK else QueryNOK in
                                  ((status, (FStar_Util.JsonList errors)),
                                    st'')))))
let run_lookup:
  'Auu____4067 .
    repl_state ->
      Prims.string ->
        (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option ->
          Prims.string Prims.list ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____4067) FStar_Util.either)
              FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____4116 = st.repl_env in
          match uu____4116 with
          | (dsenv,tcenv) ->
              let info_of_lid_str lid_str =
                let lid =
                  let uu____4148 =
                    FStar_List.map FStar_Ident.id_of_text
                      (FStar_Util.split lid_str ".") in
                  FStar_Ident.lid_of_ids uu____4148 in
                let lid1 =
                  let uu____4152 =
                    FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                      lid in
                  FStar_All.pipe_left (FStar_Util.dflt lid) uu____4152 in
                let uu____4157 =
                  FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
                FStar_All.pipe_right uu____4157
                  (FStar_Util.map_option
                     (fun uu____4212  ->
                        match uu____4212 with
                        | ((uu____4231,typ),r) ->
                            ((FStar_Util.Inr lid1), typ, r))) in
              let docs_of_lid lid =
                let uu____4248 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
                FStar_All.pipe_right uu____4248
                  (FStar_Util.map_option FStar_Pervasives_Native.fst) in
              let def_of_lid lid =
                let uu____4277 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
                FStar_Util.bind_opt uu____4277
                  (fun uu___192_4321  ->
                     match uu___192_4321 with
                     | (FStar_Util.Inr (se,uu____4343),uu____4344) ->
                         let uu____4373 =
                           FStar_Syntax_Print.sigelt_to_string se in
                         FStar_Pervasives_Native.Some uu____4373
                     | uu____4374 -> FStar_Pervasives_Native.None) in
              let info_at_pos_opt =
                FStar_Util.bind_opt pos_opt
                  (fun uu____4426  ->
                     match uu____4426 with
                     | (file,row,col) ->
                         FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
              let info_opt =
                match info_at_pos_opt with
                | FStar_Pervasives_Native.Some uu____4473 -> info_at_pos_opt
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
                        let uu____4575 =
                          FStar_Syntax_Print.term_to_string typ in
                        FStar_Pervasives_Native.Some uu____4575
                      else FStar_Pervasives_Native.None in
                    let doc_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "documentation" requested_info ->
                          docs_of_lid lid
                      | uu____4583 -> FStar_Pervasives_Native.None in
                    let def_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "definition" requested_info ->
                          def_of_lid lid
                      | uu____4594 -> FStar_Pervasives_Native.None in
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
                    let uu____4606 = json_of_lookup_result result in
                    (QueryOK, uu____4606) in
              (response, (FStar_Util.Inl st))
let run_completions:
  'Auu____4621 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4621) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      let uu____4642 = st.repl_env in
      match uu____4642 with
      | (dsenv,tcenv) ->
          let rec measure_anchored_match search_term1 candidate =
            match (search_term1, candidate) with
            | ([],uu____4692) ->
                FStar_Pervasives_Native.Some ([], (Prims.parse_int "0"))
            | (uu____4707,[]) -> FStar_Pervasives_Native.None
            | (hs::ts,hc::tc) ->
                let hc_text = FStar_Ident.text_of_id hc in
                if FStar_Util.starts_with hc_text hs
                then
                  (match ts with
                   | [] ->
                       FStar_Pervasives_Native.Some
                         (candidate, (FStar_String.length hs))
                   | uu____4757 ->
                       let uu____4760 = measure_anchored_match ts tc in
                       FStar_All.pipe_right uu____4760
                         (FStar_Util.map_option
                            (fun uu____4800  ->
                               match uu____4800 with
                               | (matched,len) ->
                                   ((hc :: matched),
                                     (((FStar_String.length hc_text) +
                                         (Prims.parse_int "1"))
                                        + len)))))
                else FStar_Pervasives_Native.None in
          let rec locate_match needle candidate =
            let uu____4855 = measure_anchored_match needle candidate in
            match uu____4855 with
            | FStar_Pervasives_Native.Some (matched,n1) ->
                FStar_Pervasives_Native.Some ([], matched, n1)
            | FStar_Pervasives_Native.None  ->
                (match candidate with
                 | [] -> FStar_Pervasives_Native.None
                 | hc::tc ->
                     let uu____4934 = locate_match needle tc in
                     FStar_All.pipe_right uu____4934
                       (FStar_Util.map_option
                          (fun uu____4995  ->
                             match uu____4995 with
                             | (prefix1,matched,len) ->
                                 ((hc :: prefix1), matched, len)))) in
          let str_of_ids ids =
            let uu____5039 = FStar_List.map FStar_Ident.text_of_id ids in
            FStar_Util.concat_l "." uu____5039 in
          let match_lident_against needle lident =
            locate_match needle
              (FStar_List.append lident.FStar_Ident.ns
                 [lident.FStar_Ident.ident]) in
          let shorten_namespace uu____5086 =
            match uu____5086 with
            | (prefix1,matched,match_len) ->
                let naked_match =
                  match matched with
                  | uu____5117::[] -> true
                  | uu____5118 -> false in
                let uu____5121 =
                  FStar_ToSyntax_Env.shorten_module_path dsenv prefix1
                    naked_match in
                (match uu____5121 with
                 | (stripped_ns,shortened) ->
                     let uu____5148 = str_of_ids shortened in
                     let uu____5149 = str_of_ids matched in
                     let uu____5150 = str_of_ids stripped_ns in
                     (uu____5148, uu____5149, uu____5150, match_len)) in
          let prepare_candidate uu____5168 =
            match uu____5168 with
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
                        let uu____5296 =
                          FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                            dsenv lid in
                        FStar_Option.map
                          (fun fqn  ->
                             let uu____5312 =
                               let uu____5315 =
                                 FStar_List.map FStar_Ident.id_of_text
                                   orig_ns in
                               FStar_List.append uu____5315
                                 [fqn.FStar_Ident.ident] in
                             ([], uu____5312, matched_length)) uu____5296
                      else FStar_Pervasives_Native.None)) in
            let case_b_find_matches_in_env uu____5348 =
              let matches =
                FStar_List.filter_map (match_lident_against needle)
                  all_lidents_in_env in
              FStar_All.pipe_right matches
                (FStar_List.filter
                   (fun uu____5423  ->
                      match uu____5423 with
                      | (ns,id,uu____5436) ->
                          let uu____5445 =
                            let uu____5448 = FStar_Ident.lid_of_ids id in
                            FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                              dsenv uu____5448 in
                          (match uu____5445 with
                           | FStar_Pervasives_Native.None  -> false
                           | FStar_Pervasives_Native.Some l ->
                               let uu____5450 =
                                 FStar_Ident.lid_of_ids
                                   (FStar_List.append ns id) in
                               FStar_Ident.lid_equals l uu____5450))) in
            let uu____5451 = FStar_Util.prefix needle in
            match uu____5451 with
            | (ns,id) ->
                let matched_ids =
                  match ns with
                  | [] -> case_b_find_matches_in_env ()
                  | uu____5497 ->
                      let l =
                        FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
                      let uu____5501 =
                        FStar_ToSyntax_Env.resolve_module_name dsenv l true in
                      (match uu____5501 with
                       | FStar_Pervasives_Native.None  ->
                           case_b_find_matches_in_env ()
                       | FStar_Pervasives_Native.Some m ->
                           case_a_find_transitive_includes ns m id) in
                FStar_All.pipe_right matched_ids
                  (FStar_List.map
                     (fun x  ->
                        let uu____5566 = shorten_namespace x in
                        prepare_candidate uu____5566)) in
          let json_candidates =
            let uu____5578 =
              FStar_Util.sort_with
                (fun uu____5601  ->
                   fun uu____5602  ->
                     match (uu____5601, uu____5602) with
                     | ((cd1,ns1,uu____5629),(cd2,ns2,uu____5632)) ->
                         (match FStar_String.compare cd1 cd2 with
                          | _0_47 when _0_47 = (Prims.parse_int "0") ->
                              FStar_String.compare ns1 ns2
                          | n1 -> n1)) matches in
            FStar_List.map
              (fun uu____5656  ->
                 match uu____5656 with
                 | (candidate,ns,match_len) ->
                     FStar_Util.JsonList
                       [FStar_Util.JsonInt match_len;
                       FStar_Util.JsonStr ns;
                       FStar_Util.JsonStr candidate]) uu____5578 in
          ((QueryOK, (FStar_Util.JsonList json_candidates)),
            (FStar_Util.Inl st))
let run_compute:
  'Auu____5682 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____5682) FStar_Util.either)
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
            let uu___206_5763 = st1 in
            {
              repl_line = (uu___206_5763.repl_line);
              repl_column = (uu___206_5763.repl_column);
              repl_fname = (uu___206_5763.repl_fname);
              repl_stack = (uu___206_5763.repl_stack);
              repl_curmod = (uu___206_5763.repl_curmod);
              repl_env = env;
              repl_ts = (uu___206_5763.repl_ts);
              repl_stdin = (uu___206_5763.repl_stdin)
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
                ((uu____5803,{ FStar_Syntax_Syntax.lbname = uu____5804;
                               FStar_Syntax_Syntax.lbunivs = uu____5805;
                               FStar_Syntax_Syntax.lbtyp = uu____5806;
                               FStar_Syntax_Syntax.lbeff = uu____5807;
                               FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____5809);
              FStar_Syntax_Syntax.sigrng = uu____5810;
              FStar_Syntax_Syntax.sigquals = uu____5811;
              FStar_Syntax_Syntax.sigmeta = uu____5812;
              FStar_Syntax_Syntax.sigattrs = uu____5813;_}::[] ->
              FStar_Pervasives_Native.Some def
          | uu____5842 -> FStar_Pervasives_Native.None in
        let parse1 frag =
          let uu____5855 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
          match uu____5855 with
          | FStar_Util.Inl (FStar_Util.Inr decls,uu____5879) ->
              FStar_Pervasives_Native.Some decls
          | uu____5924 -> FStar_Pervasives_Native.None in
        let desugar dsenv decls =
          let uu____5956 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
          FStar_Pervasives_Native.snd uu____5956 in
        let typecheck tcenv decls =
          let uu____5974 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
          match uu____5974 with | (ses,uu____5988,uu____5989) -> ses in
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
             let uu____6017 = st1.repl_env in
             match uu____6017 with
             | (dsenv,tcenv) ->
                 let frag = dummy_let_fragment term in
                 (match st1.repl_curmod with
                  | FStar_Pervasives_Native.None  ->
                      (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                  | uu____6029 ->
                      let uu____6030 = parse1 frag in
                      (match uu____6030 with
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
                                  let uu____6074 =
                                    let uu____6075 =
                                      FStar_Syntax_Print.term_to_string
                                        normalized in
                                    FStar_Util.JsonStr uu____6075 in
                                  (QueryOK, uu____6074)
                            with
                            | e ->
                                let uu____6085 =
                                  let uu____6086 =
                                    FStar_Errors.issue_of_exn e in
                                  match uu____6086 with
                                  | FStar_Pervasives_Native.Some issue ->
                                      let uu____6090 =
                                        FStar_Errors.format_issue issue in
                                      FStar_Util.JsonStr uu____6090
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Exn.raise e in
                                (QueryNOK, uu____6085)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____6112 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____6126 -> false
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
  fun uu___193_6150  ->
    match uu___193_6150 with
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
    let uu____6318 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____6325 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____6318; sc_fvars = uu____6325 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____6374 = FStar_ST.op_Bang sc.sc_typ in
      match uu____6374 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____6399 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____6399 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____6420,typ),uu____6422) ->
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
      let uu____6466 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____6466 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____6509 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____6509 in
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
          let uu____6552 = sc_typ tcenv sc in
          FStar_Syntax_Print.term_to_string uu____6552 in
        let uu____6553 =
          let uu____6560 =
            let uu____6565 =
              let uu____6566 =
                let uu____6567 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____6567.FStar_Ident.str in
              FStar_Util.JsonStr uu____6566 in
            ("lid", uu____6565) in
          [uu____6560; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____6553
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____6587 -> true
    | uu____6588 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____6596 -> uu____6596
let run_search:
  'Auu____6603 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6603) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_str  ->
      let uu____6624 = st.repl_env in
      match uu____6624 with
      | (dsenv,tcenv) ->
          let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
          let st_matches candidate term =
            let found =
              match term.st_term with
              | NameContainsStr str ->
                  FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
              | TypeContainsLid lid ->
                  let uu____6652 = sc_fvars tcenv candidate in
                  FStar_Util.set_mem lid uu____6652 in
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
                  let uu____6676 =
                    let uu____6677 =
                      FStar_Util.format1 "Improperly quoted search term: %s"
                        term1 in
                    InvalidSearch uu____6677 in
                  FStar_Exn.raise uu____6676
                else
                  if beg_quote
                  then
                    (let uu____6679 = strip_quotes term1 in
                     NameContainsStr uu____6679)
                  else
                    (let lid = FStar_Ident.lid_of_str term1 in
                     let uu____6682 =
                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                         dsenv lid in
                     match uu____6682 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____6685 =
                           let uu____6686 =
                             FStar_Util.format1 "Unknown identifier: %s"
                               term1 in
                           InvalidSearch uu____6686 in
                         FStar_Exn.raise uu____6685
                     | FStar_Pervasives_Native.Some lid1 ->
                         TypeContainsLid lid1) in
              { st_negate = negate; st_term = parsed } in
            let terms =
              FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
            let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
            FStar_Util.sort_with cmp terms in
          let pprint_one term =
            let uu____6702 =
              match term.st_term with
              | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
              | TypeContainsLid l ->
                  FStar_Util.format1 "%s" l.FStar_Ident.str in
            Prims.strcat (if term.st_negate then "-" else "") uu____6702 in
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
                  (fun uu____6764  ->
                     FStar_Options.set_option "print_effect_args"
                       (FStar_Options.Bool true);
                     FStar_List.map (json_of_search_result dsenv tcenv)
                       sorted1) in
              match results with
              | [] ->
                  let kwds =
                    let uu____6771 = FStar_List.map pprint_one terms in
                    FStar_Util.concat_l " " uu____6771 in
                  let uu____6774 =
                    let uu____6775 =
                      FStar_Util.format1 "No results found for query [%s]"
                        kwds in
                    InvalidSearch uu____6775 in
                  FStar_Exn.raise uu____6774
              | uu____6780 -> (QueryOK, (FStar_Util.JsonList js))
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
    fun uu___194_6831  ->
      match uu___194_6831 with
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
    let uu____6890 = let uu____6903 = run_query st in uu____6903 query.qq in
    match uu____6890 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____6947 =
      let uu____6950 = FStar_ST.op_Bang issues in e :: uu____6950 in
    FStar_ST.op_Colon_Equals issues uu____6947 in
  let count_errors uu____7020 =
    let uu____7021 =
      let uu____7024 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____7024 in
    FStar_List.length uu____7021 in
  let report1 uu____7066 =
    let uu____7067 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____7067 in
  let clear1 uu____7105 = FStar_ST.op_Colon_Equals issues [] in
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
    (let uu____7147 = deps_of_our_file filename in
     match uu____7147 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____7171 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu____7171 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____7198 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____7199 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____7198 uu____7199 in
              let env2 =
                let uu____7205 =
                  FStar_TypeChecker_Env.set_range
                    (FStar_Pervasives_Native.snd env1) initial_range in
                ((FStar_Pervasives_Native.fst env1), uu____7205) in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2 in
              let init_st =
                let uu____7217 = FStar_Util.open_stdin () in
                {
                  repl_line = (Prims.parse_int "1");
                  repl_column = (Prims.parse_int "0");
                  repl_fname = filename;
                  repl_stack = stack;
                  repl_curmod = FStar_Pervasives_Native.None;
                  repl_env = env3;
                  repl_ts = ts;
                  repl_stdin = uu____7217
                } in
              (FStar_TypeChecker_Common.insert_id_info.FStar_TypeChecker_Common.enable
                 true;
               (let uu____7219 =
                  (FStar_Options.record_hints ()) ||
                    (FStar_Options.use_hints ()) in
                if uu____7219
                then
                  let uu____7220 =
                    let uu____7221 = FStar_Options.file_list () in
                    FStar_List.hd uu____7221 in
                  FStar_SMTEncoding_Solver.with_hints_db uu____7220
                    (fun uu____7225  -> go init_st)
                else go init_st))))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    FStar_Errors.set_handler interactive_error_handler;
    (let uu____7234 =
       let uu____7235 = FStar_Options.codegen () in
       FStar_Option.isSome uu____7235 in
     if uu____7234
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (try interactive_mode' filename
     with
     | e ->
         (FStar_Errors.set_handler FStar_Errors.default_handler;
          FStar_Exn.raise e))