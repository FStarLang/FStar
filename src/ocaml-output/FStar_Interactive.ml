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
    FStar_Pervasives_Native.tuple2[@@deriving show]
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
[@@deriving show]
type stack_t = (env_t,modul_t) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
let push:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    Prims.string ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun msg  ->
      let res = FStar_Universal.push_context env msg in
      FStar_Options.push (); res
let pop:
  'Auu____335 .
    ('Auu____335,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.string -> Prims.unit
  =
  fun env  ->
    fun msg  ->
      FStar_Universal.pop_context (FStar_Pervasives_Native.snd env) msg;
      FStar_Options.pop ()
type push_kind =
  | SyntaxCheck
  | LaxCheck
  | FullCheck[@@deriving show]
let uu___is_SyntaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____357 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____362 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____367 -> false
let push_with_kind:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    push_kind ->
      Prims.bool ->
        Prims.string ->
          (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2
  =
  fun uu____388  ->
    fun kind  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____388 with
          | (dsenv,tcenv) ->
              let tcenv1 =
                let uu___221_403 = tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___221_403.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___221_403.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___221_403.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___221_403.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___221_403.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___221_403.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___221_403.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___221_403.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___221_403.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___221_403.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___221_403.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___221_403.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___221_403.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___221_403.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___221_403.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___221_403.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___221_403.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___221_403.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = (kind = LaxCheck);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___221_403.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___221_403.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___221_403.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___221_403.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___221_403.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___221_403.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___221_403.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___221_403.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___221_403.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___221_403.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___221_403.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___221_403.FStar_TypeChecker_Env.identifier_info)
                } in
              let dsenv1 =
                FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck) in
              let res = push (dsenv1, tcenv1) msg in
              (if restore_cmd_line_options1
               then
                 (let uu____411 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____411 FStar_Pervasives.ignore)
               else ();
               res)
let cleanup:
  'Auu____417 .
    ('Auu____417,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.unit
  =
  fun uu____425  ->
    match uu____425 with
    | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
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
  fun uu____465  ->
    fun curmod  ->
      fun frag  ->
        match uu____465 with
        | (dsenv,env) ->
            (try
               let uu____529 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag in
               match uu____529 with
               | FStar_Pervasives_Native.Some (m,dsenv1,env1) ->
                   let uu____569 =
                     let uu____582 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____582) in
                   FStar_Pervasives_Native.Some uu____569
               | uu____601 -> FStar_Pervasives_Native.None
             with
             | FStar_All.Failure msg when
                 let uu____645 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____645 ->
                 let msg1 =
                   Prims.strcat "ASSERTION FAILURE: "
                     (Prims.strcat msg
                        (Prims.strcat "\n"
                           (Prims.strcat
                              "F* may be in an inconsistent state.\n"
                              (Prims.strcat
                                 "Please file a bug report, ideally with a "
                                 "minimized version of the program that triggered the error.")))) in
                 ((let uu____648 =
                     let uu____655 =
                       let uu____660 = FStar_TypeChecker_Env.get_range env in
                       (msg1, uu____660) in
                     [uu____655] in
                   FStar_TypeChecker_Err.add_errors env uu____648);
                  FStar_Util.print_error msg1;
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Error (msg,r) when
                 let uu____684 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____684 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____707 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____707 ->
                 ((let uu____709 =
                     let uu____716 =
                       let uu____721 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____721) in
                     [uu____716] in
                   FStar_TypeChecker_Err.add_errors env uu____709);
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
    let uu____757 =
      FStar_List.partition
        (fun x  ->
           let uu____770 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____771 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____770 <> uu____771) deps in
    match uu____757 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____798 =
                  (let uu____801 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____801) ||
                    (let uu____803 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____803) in
                if uu____798
                then
                  let uu____804 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____804
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____807 ->
              ((let uu____811 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____811);
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
            | uu____866 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____885 =
                    let uu____886 = FStar_Options.lax () in
                    if uu____886 then LaxCheck else FullCheck in
                  push_with_kind env uu____885 true "typecheck_modul" in
                let uu____888 = tc_one_file remaining env1 in
                (match uu____888 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____939 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____952 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____952
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____939 with
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
                 | (uu____1056,uu____1057) ->
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
                     | uu____1152 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1180 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1263::ts3 ->
                    (pop env1 "";
                     (let uu____1304 =
                        let uu____1319 = FStar_List.hd stack in
                        let uu____1328 = FStar_List.tl stack in
                        (uu____1319, uu____1328) in
                      match uu____1304 with
                      | ((env2,uu____1354),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1418 = ts_elt in
                  (match uu____1418 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1449 = match_dep depnames intf impl in
                       (match uu____1449 with
                        | (b,depnames') ->
                            let uu____1468 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1468
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1489 =
                                 let uu____1504 = FStar_List.hd st in
                                 let uu____1513 = FStar_List.tl st in
                                 (uu____1504, uu____1513) in
                               match uu____1489 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1590 = deps_of_our_file filename in
            match uu____1590 with
            | (filenames,uu____1606) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___211_1666  ->
    match uu___211_1666 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1670 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1670
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1672 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1675 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1693 -> true
    | uu____1698 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1714 -> uu____1714
let js_fail: 'Auu____1725 . Prims.string -> FStar_Util.json -> 'Auu____1725 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___212_1737  ->
    match uu___212_1737 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___213_1743  ->
    match uu___213_1743 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list:
  'Auu____1752 .
    (FStar_Util.json -> 'Auu____1752) ->
      FStar_Util.json -> 'Auu____1752 Prims.list
  =
  fun k  ->
    fun uu___214_1765  ->
      match uu___214_1765 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___215_1783  ->
    match uu___215_1783 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1808 = js_str s in
    match uu____1808 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1809 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1814 = js_str s in
    match uu____1814 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | "reify" -> FStar_TypeChecker_Normalize.Reify
    | "pure-subterms" ->
        FStar_TypeChecker_Normalize.PureSubtermsWithinComputations
    | uu____1815 -> js_fail "reduction rule" s
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
  | ProtocolViolation of Prims.string[@@deriving show]
and query = {
  qq: query';
  qid: Prims.string;}[@@deriving show]
let uu___is_Exit: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1886 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1891 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1896 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1901 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1917 -> false
let __proj__Push__item___0:
  query' ->
    (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1961 -> false
let __proj__AutoComplete__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____1991 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,(Prims.string,Prims.int,Prims.int)
                    FStar_Pervasives_Native.tuple3
                    FStar_Pervasives_Native.option,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2061 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2099 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_MissingCurrentModule: query' -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MissingCurrentModule  -> true
    | uu____2112 -> false
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2118 -> false
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
  fun uu___216_2142  ->
    match uu___216_2142 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Pop  -> false
    | Push uu____2143 -> false
    | MissingCurrentModule  -> false
    | ProtocolViolation uu____2154 -> false
    | AutoComplete uu____2155 -> true
    | Lookup uu____2156 -> true
    | Compute uu____2173 -> true
    | Search uu____2182 -> true
let interactive_protocol_vernum: Prims.int = Prims.parse_int "2"
let interactive_protocol_features: Prims.string Prims.list =
  ["autocomplete";
  "compute";
  "compute/reify";
  "compute/pure-subterms";
  "describe-protocol";
  "describe-repl";
  "exit";
  "lookup";
  "lookup/documentation";
  "lookup/definition";
  "peek";
  "pop";
  "push";
  "search"]
exception InvalidQuery of Prims.string
let uu___is_InvalidQuery: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____2192 -> true
    | uu____2193 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2201 -> uu____2201
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol[@@deriving show]
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2206 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2211 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2216 -> false
let try_assoc:
  'Auu____2225 'Auu____2226 .
    'Auu____2226 ->
      ('Auu____2226,'Auu____2225) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2225 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2249 =
        FStar_Util.try_find
          (fun uu____2263  ->
             match uu____2263 with | (k,uu____2269) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2249
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2286 =
          let uu____2287 =
            let uu____2288 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2288 in
          ProtocolViolation uu____2287 in
        { qq = uu____2286; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2315 = try_assoc key a in
      match uu____2315 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2319 =
            let uu____2320 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____2320 in
          FStar_Exn.raise uu____2319 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____2335 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2335 js_str in
    try
      let query =
        let uu____2344 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____2344 js_str in
      let args =
        let uu____2352 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____2352 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____2369 = try_assoc k args in
        match uu____2369 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____2377 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____2378 =
              let uu____2389 =
                let uu____2390 = arg "kind" in
                FStar_All.pipe_right uu____2390 js_pushkind in
              let uu____2391 =
                let uu____2392 = arg "code" in
                FStar_All.pipe_right uu____2392 js_str in
              let uu____2393 =
                let uu____2394 = arg "line" in
                FStar_All.pipe_right uu____2394 js_int in
              let uu____2395 =
                let uu____2396 = arg "column" in
                FStar_All.pipe_right uu____2396 js_int in
              (uu____2389, uu____2391, uu____2393, uu____2395,
                (query = "peek")) in
            Push uu____2378
        | "push" ->
            let uu____2397 =
              let uu____2408 =
                let uu____2409 = arg "kind" in
                FStar_All.pipe_right uu____2409 js_pushkind in
              let uu____2410 =
                let uu____2411 = arg "code" in
                FStar_All.pipe_right uu____2411 js_str in
              let uu____2412 =
                let uu____2413 = arg "line" in
                FStar_All.pipe_right uu____2413 js_int in
              let uu____2414 =
                let uu____2415 = arg "column" in
                FStar_All.pipe_right uu____2415 js_int in
              (uu____2408, uu____2410, uu____2412, uu____2414,
                (query = "peek")) in
            Push uu____2397
        | "autocomplete" ->
            let uu____2416 =
              let uu____2417 = arg "partial-symbol" in
              FStar_All.pipe_right uu____2417 js_str in
            AutoComplete uu____2416
        | "lookup" ->
            let uu____2418 =
              let uu____2435 =
                let uu____2436 = arg "symbol" in
                FStar_All.pipe_right uu____2436 js_str in
              let uu____2437 =
                let uu____2446 =
                  let uu____2455 = try_arg "location" in
                  FStar_All.pipe_right uu____2455
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____2446
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____2513 =
                          let uu____2514 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____2514 js_str in
                        let uu____2515 =
                          let uu____2516 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____2516 js_int in
                        let uu____2517 =
                          let uu____2518 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____2518 js_int in
                        (uu____2513, uu____2515, uu____2517))) in
              let uu____2519 =
                let uu____2522 = arg "requested-info" in
                FStar_All.pipe_right uu____2522 (js_list js_str) in
              (uu____2435, uu____2437, uu____2519) in
            Lookup uu____2418
        | "compute" ->
            let uu____2535 =
              let uu____2544 =
                let uu____2545 = arg "term" in
                FStar_All.pipe_right uu____2545 js_str in
              let uu____2546 =
                let uu____2551 = try_arg "rules" in
                FStar_All.pipe_right uu____2551
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____2544, uu____2546) in
            Compute uu____2535
        | "search" ->
            let uu____2566 =
              let uu____2567 = arg "terms" in
              FStar_All.pipe_right uu____2567 js_str in
            Search uu____2566
        | uu____2568 ->
            let uu____2569 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____2569 in
      { qq = uu____2377; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____2583 = FStar_Util.read_line stream in
      match uu____2583 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some line ->
          let uu____2587 = FStar_Util.json_of_string line in
          (match uu____2587 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               unpack_interactive_query request)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let rec json_of_fstar_option: FStar_Options.option_val -> FStar_Util.json =
  fun uu___217_2600  ->
    match uu___217_2600 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____2608 = FStar_List.map json_of_fstar_option vs in
        FStar_Util.JsonList uu____2608
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let json_of_opt:
  'Auu____2617 .
    ('Auu____2617 -> FStar_Util.json) ->
      'Auu____2617 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____2635 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____2635
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____2642 =
      let uu____2645 =
        let uu____2646 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____2646 in
      let uu____2647 =
        let uu____2650 =
          let uu____2651 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____2651 in
        [uu____2650] in
      uu____2645 :: uu____2647 in
    FStar_Util.JsonList uu____2642
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____2664 =
          let uu____2671 =
            let uu____2678 =
              let uu____2683 = json_of_pos b in ("beg", uu____2683) in
            let uu____2684 =
              let uu____2691 =
                let uu____2696 = json_of_pos e in ("end", uu____2696) in
              [uu____2691] in
            uu____2678 :: uu____2684 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____2671 in
        FStar_Util.JsonAssoc uu____2664
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2717 = FStar_Range.file_of_use_range r in
    let uu____2718 = FStar_Range.start_of_use_range r in
    let uu____2719 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____2717 uu____2718 uu____2719
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2724 = FStar_Range.file_of_range r in
    let uu____2725 = FStar_Range.start_of_range r in
    let uu____2726 = FStar_Range.end_of_range r in
    json_of_range_fields uu____2724 uu____2725 uu____2726
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
    let uu____2735 =
      let uu____2742 =
        let uu____2749 =
          let uu____2756 =
            let uu____2761 =
              let uu____2762 =
                let uu____2765 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____2771 = json_of_use_range r in [uu____2771] in
                let uu____2772 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____2778 = json_of_def_range r in [uu____2778]
                  | uu____2779 -> [] in
                FStar_List.append uu____2765 uu____2772 in
              FStar_Util.JsonList uu____2762 in
            ("ranges", uu____2761) in
          [uu____2756] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____2749 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____2742 in
    FStar_Util.JsonAssoc uu____2735
type lookup_result =
  {
  lr_name: Prims.string;
  lr_def_range: FStar_Range.range FStar_Pervasives_Native.option;
  lr_typ: Prims.string FStar_Pervasives_Native.option;
  lr_doc: Prims.string FStar_Pervasives_Native.option;
  lr_def: Prims.string FStar_Pervasives_Native.option;}[@@deriving show]
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
    let uu____2931 =
      let uu____2938 =
        let uu____2945 =
          let uu____2950 = json_of_opt json_of_def_range lr.lr_def_range in
          ("defined-at", uu____2950) in
        let uu____2951 =
          let uu____2958 =
            let uu____2963 =
              json_of_opt (fun _0_42  -> FStar_Util.JsonStr _0_42) lr.lr_typ in
            ("type", uu____2963) in
          let uu____2964 =
            let uu____2971 =
              let uu____2976 =
                json_of_opt (fun _0_43  -> FStar_Util.JsonStr _0_43)
                  lr.lr_doc in
              ("documentation", uu____2976) in
            let uu____2977 =
              let uu____2984 =
                let uu____2989 =
                  json_of_opt (fun _0_44  -> FStar_Util.JsonStr _0_44)
                    lr.lr_def in
                ("definition", uu____2989) in
              [uu____2984] in
            uu____2971 :: uu____2977 in
          uu____2958 :: uu____2964 in
        uu____2945 :: uu____2951 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____2938 in
    FStar_Util.JsonAssoc uu____2931
let json_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3022 =
      FStar_List.map (fun _0_45  -> FStar_Util.JsonStr _0_45)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_46  -> FStar_Util.JsonList _0_46) uu____3022 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____3044 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____3044);
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
  fun uu____3106  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____3109 =
        FStar_List.map (fun _0_47  -> FStar_Util.JsonStr _0_47)
          interactive_protocol_features in
      FStar_Util.JsonList uu____3109 in
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
  repl_stdin: FStar_Util.stream_reader;}[@@deriving show]
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
        let uu____3270 = FStar_Options.docs () in
        FStar_Util.smap_of_list uu____3270 in
      let get_doc k = FStar_Util.smap_try_find opt_docs k in
      FStar_List.map
        (fun uu____3302  ->
           match uu____3302 with
           | (k,v1) ->
               let uu____3319 = FStar_Options.get_option k in
               let uu____3320 = get_doc k in (k, uu____3319, uu____3320, v1))
        FStar_Options.defaults in
    let uu____3325 =
      let uu____3330 =
        let uu____3331 =
          FStar_List.map
            (fun uu____3351  ->
               match uu____3351 with
               | (uu____3364,fstname,uu____3366,uu____3367) ->
                   FStar_Util.JsonStr fstname) st.repl_ts in
        FStar_Util.JsonList uu____3331 in
      ("loaded-dependencies", uu____3330) in
    let uu____3376 =
      let uu____3383 =
        let uu____3388 =
          let uu____3389 =
            FStar_List.map
              (fun uu____3408  ->
                 match uu____3408 with
                 | (name,value,doc1,dflt1) ->
                     let uu____3427 =
                       let uu____3434 =
                         let uu____3441 =
                           let uu____3446 = json_of_fstar_option value in
                           ("value", uu____3446) in
                         let uu____3447 =
                           let uu____3454 =
                             let uu____3459 = json_of_fstar_option dflt1 in
                             ("default", uu____3459) in
                           let uu____3460 =
                             let uu____3467 =
                               let uu____3472 =
                                 json_of_opt
                                   (fun _0_48  -> FStar_Util.JsonStr _0_48)
                                   doc1 in
                               ("documentation", uu____3472) in
                             [uu____3467] in
                           uu____3454 :: uu____3460 in
                         uu____3441 :: uu____3447 in
                       ("name", (FStar_Util.JsonStr name)) :: uu____3434 in
                     FStar_Util.JsonAssoc uu____3427) opts_and_defaults in
          FStar_Util.JsonList uu____3389 in
        ("options", uu____3388) in
      [uu____3383] in
    uu____3325 :: uu____3376
let with_printed_effect_args:
  'Auu____3509 . (Prims.unit -> 'Auu____3509) -> 'Auu____3509 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____3521  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____3532  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
let sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____3538  -> FStar_Syntax_Print.sigelt_to_string se)
let run_exit:
  'Auu____3545 'Auu____3546 .
    'Auu____3546 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3545,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol:
  'Auu____3577 'Auu____3578 .
    'Auu____3578 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3578,'Auu____3577) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl:
  'Auu____3607 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____3607) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____3624 =
      let uu____3629 =
        let uu____3630 = json_of_repl_state st in
        FStar_Util.JsonAssoc uu____3630 in
      (QueryOK, uu____3629) in
    (uu____3624, (FStar_Util.Inl st))
let run_protocol_violation:
  'Auu____3653 'Auu____3654 .
    'Auu____3654 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____3654,'Auu____3653) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_missing_current_module:
  'Auu____3693 'Auu____3694 'Auu____3695 .
    'Auu____3695 ->
      'Auu____3694 ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____3695,'Auu____3693) FStar_Util.either)
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
  'Auu____3748 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____3748) FStar_Util.either)
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
               let uu___228_3817 = st in
               {
                 repl_line = (uu___228_3817.repl_line);
                 repl_column = (uu___228_3817.repl_column);
                 repl_fname = (uu___228_3817.repl_fname);
                 repl_stack = stack;
                 repl_curmod = curmod;
                 repl_env = env;
                 repl_ts = (uu___228_3817.repl_ts);
                 repl_stdin = (uu___228_3817.repl_stdin)
               } in
             if nothing_left_to_pop st' then cleanup env else ();
             ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))))
let run_push:
  'Auu____3842 .
    repl_state ->
      push_kind ->
        Prims.string ->
          Prims.int ->
            Prims.int ->
              Prims.bool ->
                ((query_status,FStar_Util.json)
                   FStar_Pervasives_Native.tuple2,(repl_state,'Auu____3842)
                                                    FStar_Util.either)
                  FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun kind  ->
      fun text1  ->
        fun line  ->
          fun column  ->
            fun peek_only  ->
              let uu____3879 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
              match uu____3879 with
              | (stack,env,ts) ->
                  let uu____3901 =
                    if nothing_left_to_pop st
                    then
                      let uu____3922 =
                        update_deps st.repl_fname st.repl_curmod stack env ts in
                      (true, uu____3922)
                    else (false, (stack, env, ts)) in
                  (match uu____3901 with
                   | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
                       let stack2 = (env1, (st.repl_curmod)) :: stack1 in
                       let env2 =
                         push_with_kind env1 kind restore_cmd_line_options1
                           "#push" in
                       let frag =
                         {
                           FStar_Parser_ParseIt.frag_text = text1;
                           FStar_Parser_ParseIt.frag_line = line;
                           FStar_Parser_ParseIt.frag_col = column
                         } in
                       let res = check_frag env2 st.repl_curmod (frag, false) in
                       let errors =
                         let uu____3999 = FStar_Errors.report_all () in
                         FStar_All.pipe_right uu____3999
                           (FStar_List.map json_of_issue) in
                       (FStar_Errors.clear ();
                        (let st' =
                           let uu___229_4008 = st in
                           {
                             repl_line = line;
                             repl_column = column;
                             repl_fname = (uu___229_4008.repl_fname);
                             repl_stack = stack2;
                             repl_curmod = (uu___229_4008.repl_curmod);
                             repl_env = (uu___229_4008.repl_env);
                             repl_ts = ts1;
                             repl_stdin = (uu___229_4008.repl_stdin)
                           } in
                         match res with
                         | FStar_Pervasives_Native.Some (curmod,env3,nerrs)
                             when
                             (nerrs = (Prims.parse_int "0")) &&
                               (peek_only = false)
                             ->
                             ((QueryOK, (FStar_Util.JsonList errors)),
                               (FStar_Util.Inl
                                  (let uu___230_4057 = st' in
                                   {
                                     repl_line = (uu___230_4057.repl_line);
                                     repl_column =
                                       (uu___230_4057.repl_column);
                                     repl_fname = (uu___230_4057.repl_fname);
                                     repl_stack = (uu___230_4057.repl_stack);
                                     repl_curmod = curmod;
                                     repl_env = env3;
                                     repl_ts = (uu___230_4057.repl_ts);
                                     repl_stdin = (uu___230_4057.repl_stdin)
                                   })))
                         | uu____4058 ->
                             let uu____4073 =
                               run_pop
                                 (let uu___231_4087 = st' in
                                  {
                                    repl_line = (uu___231_4087.repl_line);
                                    repl_column = (uu___231_4087.repl_column);
                                    repl_fname = (uu___231_4087.repl_fname);
                                    repl_stack = (uu___231_4087.repl_stack);
                                    repl_curmod = (uu___231_4087.repl_curmod);
                                    repl_env = env2;
                                    repl_ts = (uu___231_4087.repl_ts);
                                    repl_stdin = (uu___231_4087.repl_stdin)
                                  }) in
                             (match uu____4073 with
                              | (uu____4100,st'') ->
                                  let status =
                                    if peek_only then QueryOK else QueryNOK in
                                  ((status, (FStar_Util.JsonList errors)),
                                    st'')))))
let run_lookup:
  'Auu____4138 .
    repl_state ->
      Prims.string ->
        (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option ->
          Prims.string Prims.list ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____4138) FStar_Util.either)
              FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____4187 = st.repl_env in
          match uu____4187 with
          | (dsenv,tcenv) ->
              let info_of_lid_str lid_str =
                let lid =
                  let uu____4219 =
                    FStar_List.map FStar_Ident.id_of_text
                      (FStar_Util.split lid_str ".") in
                  FStar_Ident.lid_of_ids uu____4219 in
                let lid1 =
                  let uu____4223 =
                    FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                      lid in
                  FStar_All.pipe_left (FStar_Util.dflt lid) uu____4223 in
                let uu____4228 =
                  FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
                FStar_All.pipe_right uu____4228
                  (FStar_Util.map_option
                     (fun uu____4283  ->
                        match uu____4283 with
                        | ((uu____4302,typ),r) ->
                            ((FStar_Util.Inr lid1), typ, r))) in
              let docs_of_lid lid =
                let uu____4319 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
                FStar_All.pipe_right uu____4319
                  (FStar_Util.map_option FStar_Pervasives_Native.fst) in
              let def_of_lid lid =
                let uu____4348 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
                FStar_Util.bind_opt uu____4348
                  (fun uu___218_4392  ->
                     match uu___218_4392 with
                     | (FStar_Util.Inr (se,uu____4414),uu____4415) ->
                         let uu____4444 = sigelt_to_string se in
                         FStar_Pervasives_Native.Some uu____4444
                     | uu____4445 -> FStar_Pervasives_Native.None) in
              let info_at_pos_opt =
                FStar_Util.bind_opt pos_opt
                  (fun uu____4497  ->
                     match uu____4497 with
                     | (file,row,col) ->
                         FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
              let info_opt =
                match info_at_pos_opt with
                | FStar_Pervasives_Native.Some uu____4544 -> info_at_pos_opt
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
                        let uu____4646 = term_to_string tcenv typ in
                        FStar_Pervasives_Native.Some uu____4646
                      else FStar_Pervasives_Native.None in
                    let doc_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "documentation" requested_info ->
                          docs_of_lid lid
                      | uu____4654 -> FStar_Pervasives_Native.None in
                    let def_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "definition" requested_info ->
                          def_of_lid lid
                      | uu____4665 -> FStar_Pervasives_Native.None in
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
                    let uu____4677 = json_of_lookup_result result in
                    (QueryOK, uu____4677) in
              (response, (FStar_Util.Inl st))
let run_completions:
  'Auu____4692 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4692) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      let uu____4713 = st.repl_env in
      match uu____4713 with
      | (dsenv,tcenv) ->
          let rec measure_anchored_match search_term1 candidate =
            match (search_term1, candidate) with
            | ([],uu____4763) ->
                FStar_Pervasives_Native.Some ([], (Prims.parse_int "0"))
            | (uu____4778,[]) -> FStar_Pervasives_Native.None
            | (hs::ts,hc::tc) ->
                let hc_text = FStar_Ident.text_of_id hc in
                if FStar_Util.starts_with hc_text hs
                then
                  (match ts with
                   | [] ->
                       FStar_Pervasives_Native.Some
                         (candidate, (FStar_String.length hs))
                   | uu____4828 ->
                       let uu____4831 = measure_anchored_match ts tc in
                       FStar_All.pipe_right uu____4831
                         (FStar_Util.map_option
                            (fun uu____4871  ->
                               match uu____4871 with
                               | (matched,len) ->
                                   ((hc :: matched),
                                     (((FStar_String.length hc_text) +
                                         (Prims.parse_int "1"))
                                        + len)))))
                else FStar_Pervasives_Native.None in
          let rec locate_match needle candidate =
            let uu____4926 = measure_anchored_match needle candidate in
            match uu____4926 with
            | FStar_Pervasives_Native.Some (matched,n1) ->
                FStar_Pervasives_Native.Some ([], matched, n1)
            | FStar_Pervasives_Native.None  ->
                (match candidate with
                 | [] -> FStar_Pervasives_Native.None
                 | hc::tc ->
                     let uu____5005 = locate_match needle tc in
                     FStar_All.pipe_right uu____5005
                       (FStar_Util.map_option
                          (fun uu____5066  ->
                             match uu____5066 with
                             | (prefix1,matched,len) ->
                                 ((hc :: prefix1), matched, len)))) in
          let str_of_ids ids =
            let uu____5110 = FStar_List.map FStar_Ident.text_of_id ids in
            FStar_Util.concat_l "." uu____5110 in
          let match_lident_against needle lident =
            locate_match needle
              (FStar_List.append lident.FStar_Ident.ns
                 [lident.FStar_Ident.ident]) in
          let shorten_namespace uu____5157 =
            match uu____5157 with
            | (prefix1,matched,match_len) ->
                let naked_match =
                  match matched with
                  | uu____5188::[] -> true
                  | uu____5189 -> false in
                let uu____5192 =
                  FStar_ToSyntax_Env.shorten_module_path dsenv prefix1
                    naked_match in
                (match uu____5192 with
                 | (stripped_ns,shortened) ->
                     let uu____5219 = str_of_ids shortened in
                     let uu____5220 = str_of_ids matched in
                     let uu____5221 = str_of_ids stripped_ns in
                     (uu____5219, uu____5220, uu____5221, match_len)) in
          let prepare_candidate uu____5239 =
            match uu____5239 with
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
                        let uu____5367 =
                          FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                            dsenv lid in
                        FStar_Option.map
                          (fun fqn  ->
                             let uu____5383 =
                               let uu____5386 =
                                 FStar_List.map FStar_Ident.id_of_text
                                   orig_ns in
                               FStar_List.append uu____5386
                                 [fqn.FStar_Ident.ident] in
                             ([], uu____5383, matched_length)) uu____5367
                      else FStar_Pervasives_Native.None)) in
            let case_b_find_matches_in_env uu____5419 =
              let matches =
                FStar_List.filter_map (match_lident_against needle)
                  all_lidents_in_env in
              FStar_All.pipe_right matches
                (FStar_List.filter
                   (fun uu____5494  ->
                      match uu____5494 with
                      | (ns,id,uu____5507) ->
                          let uu____5516 =
                            let uu____5519 = FStar_Ident.lid_of_ids id in
                            FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                              dsenv uu____5519 in
                          (match uu____5516 with
                           | FStar_Pervasives_Native.None  -> false
                           | FStar_Pervasives_Native.Some l ->
                               let uu____5521 =
                                 FStar_Ident.lid_of_ids
                                   (FStar_List.append ns id) in
                               FStar_Ident.lid_equals l uu____5521))) in
            let uu____5522 = FStar_Util.prefix needle in
            match uu____5522 with
            | (ns,id) ->
                let matched_ids =
                  match ns with
                  | [] -> case_b_find_matches_in_env ()
                  | uu____5568 ->
                      let l =
                        FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
                      let uu____5572 =
                        FStar_ToSyntax_Env.resolve_module_name dsenv l true in
                      (match uu____5572 with
                       | FStar_Pervasives_Native.None  ->
                           case_b_find_matches_in_env ()
                       | FStar_Pervasives_Native.Some m ->
                           case_a_find_transitive_includes ns m id) in
                FStar_All.pipe_right matched_ids
                  (FStar_List.map
                     (fun x  ->
                        let uu____5637 = shorten_namespace x in
                        prepare_candidate uu____5637)) in
          let json_candidates =
            let uu____5649 =
              FStar_Util.sort_with
                (fun uu____5672  ->
                   fun uu____5673  ->
                     match (uu____5672, uu____5673) with
                     | ((cd1,ns1,uu____5700),(cd2,ns2,uu____5703)) ->
                         (match FStar_String.compare cd1 cd2 with
                          | _0_49 when _0_49 = (Prims.parse_int "0") ->
                              FStar_String.compare ns1 ns2
                          | n1 -> n1)) matches in
            FStar_List.map
              (fun uu____5727  ->
                 match uu____5727 with
                 | (candidate,ns,match_len) ->
                     FStar_Util.JsonList
                       [FStar_Util.JsonInt match_len;
                       FStar_Util.JsonStr ns;
                       FStar_Util.JsonStr candidate]) uu____5649 in
          ((QueryOK, (FStar_Util.JsonList json_candidates)),
            (FStar_Util.Inl st))
let run_compute:
  'Auu____5753 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____5753) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun term  ->
      fun rules  ->
        let run_and_rewind st1 task =
          let env' = push st1.repl_env "#compute" in
          let results = task st1 in
          pop env' "#compute"; (results, (FStar_Util.Inl st1)) in
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
                ((uu____5880,{ FStar_Syntax_Syntax.lbname = uu____5881;
                               FStar_Syntax_Syntax.lbunivs = univs1;
                               FStar_Syntax_Syntax.lbtyp = uu____5883;
                               FStar_Syntax_Syntax.lbeff = uu____5884;
                               FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____5886);
              FStar_Syntax_Syntax.sigrng = uu____5887;
              FStar_Syntax_Syntax.sigquals = uu____5888;
              FStar_Syntax_Syntax.sigmeta = uu____5889;
              FStar_Syntax_Syntax.sigattrs = uu____5890;_}::[] ->
              FStar_Pervasives_Native.Some (univs1, def)
          | uu____5929 -> FStar_Pervasives_Native.None in
        let parse1 frag =
          let uu____5948 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
          match uu____5948 with
          | FStar_Util.Inl (FStar_Util.Inr decls,uu____5972) ->
              FStar_Pervasives_Native.Some decls
          | uu____6017 -> FStar_Pervasives_Native.None in
        let desugar dsenv decls =
          let uu____6049 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
          FStar_Pervasives_Native.snd uu____6049 in
        let typecheck tcenv decls =
          let uu____6067 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
          match uu____6067 with | (ses,uu____6081,uu____6082) -> ses in
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
             let uu____6110 = st1.repl_env in
             match uu____6110 with
             | (dsenv,tcenv) ->
                 let frag = dummy_let_fragment term in
                 (match st1.repl_curmod with
                  | FStar_Pervasives_Native.None  ->
                      (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                  | uu____6122 ->
                      let uu____6123 = parse1 frag in
                      (match uu____6123 with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr "Could not parse this term"))
                       | FStar_Pervasives_Native.Some decls ->
                           let aux uu____6146 =
                             let decls1 = desugar dsenv decls in
                             let ses = typecheck tcenv decls1 in
                             match find_let_body ses with
                             | FStar_Pervasives_Native.None  ->
                                 (QueryNOK,
                                   (FStar_Util.JsonStr
                                      "Typechecking yielded an unexpected term"))
                             | FStar_Pervasives_Native.Some (univs1,def) ->
                                 let uu____6181 =
                                   FStar_Syntax_Subst.open_univ_vars univs1
                                     def in
                                 (match uu____6181 with
                                  | (univs2,def1) ->
                                      let tcenv1 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          tcenv univs2 in
                                      let normalized =
                                        normalize_term1 tcenv1 rules1 def1 in
                                      let uu____6194 =
                                        let uu____6195 =
                                          term_to_string tcenv1 normalized in
                                        FStar_Util.JsonStr uu____6195 in
                                      (QueryOK, uu____6194)) in
                           let uu____6196 = FStar_Options.trace_error () in
                           if uu____6196
                           then aux ()
                           else
                             (try aux ()
                              with
                              | e ->
                                  let uu____6221 =
                                    let uu____6222 =
                                      FStar_Errors.issue_of_exn e in
                                    match uu____6222 with
                                    | FStar_Pervasives_Native.Some issue ->
                                        let uu____6226 =
                                          FStar_Errors.format_issue issue in
                                        FStar_Util.JsonStr uu____6226
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Exn.raise e in
                                  (QueryNOK, uu____6221)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid[@@deriving show]
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}[@@deriving show]
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____6248 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____6262 -> false
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
  fun uu___219_6286  ->
    match uu___219_6286 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> Prims.parse_int "1"
type search_candidate =
  {
  sc_lid: FStar_Ident.lid;
  sc_typ:
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref;
  sc_fvars:
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref;}[@@deriving show]
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
    let uu____6454 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____6461 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____6454; sc_fvars = uu____6461 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____6510 = FStar_ST.op_Bang sc.sc_typ in
      match uu____6510 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____6567 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____6567 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____6588,typ),uu____6590) ->
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
      let uu____6666 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____6666 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____6737 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____6737 in
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
          let uu____6808 = sc_typ tcenv sc in term_to_string tcenv uu____6808 in
        let uu____6809 =
          let uu____6816 =
            let uu____6821 =
              let uu____6822 =
                let uu____6823 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____6823.FStar_Ident.str in
              FStar_Util.JsonStr uu____6822 in
            ("lid", uu____6821) in
          [uu____6816; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____6809
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____6843 -> true
    | uu____6844 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____6852 -> uu____6852
let run_search:
  'Auu____6859 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6859) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_str  ->
      let uu____6880 = st.repl_env in
      match uu____6880 with
      | (dsenv,tcenv) ->
          let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
          let st_matches candidate term =
            let found =
              match term.st_term with
              | NameContainsStr str ->
                  FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
              | TypeContainsLid lid ->
                  let uu____6908 = sc_fvars tcenv candidate in
                  FStar_Util.set_mem lid uu____6908 in
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
                  let uu____6932 =
                    let uu____6933 =
                      FStar_Util.format1 "Improperly quoted search term: %s"
                        term1 in
                    InvalidSearch uu____6933 in
                  FStar_Exn.raise uu____6932
                else
                  if beg_quote
                  then
                    (let uu____6935 = strip_quotes term1 in
                     NameContainsStr uu____6935)
                  else
                    (let lid = FStar_Ident.lid_of_str term1 in
                     let uu____6938 =
                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                         dsenv lid in
                     match uu____6938 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____6941 =
                           let uu____6942 =
                             FStar_Util.format1 "Unknown identifier: %s"
                               term1 in
                           InvalidSearch uu____6942 in
                         FStar_Exn.raise uu____6941
                     | FStar_Pervasives_Native.Some lid1 ->
                         TypeContainsLid lid1) in
              { st_negate = negate; st_term = parsed } in
            let terms =
              FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
            let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
            FStar_Util.sort_with cmp terms in
          let pprint_one term =
            let uu____6958 =
              match term.st_term with
              | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
              | TypeContainsLid l ->
                  FStar_Util.format1 "%s" l.FStar_Ident.str in
            Prims.strcat (if term.st_negate then "-" else "") uu____6958 in
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
                    let uu____7021 = FStar_List.map pprint_one terms in
                    FStar_Util.concat_l " " uu____7021 in
                  let uu____7024 =
                    let uu____7025 =
                      FStar_Util.format1 "No results found for query [%s]"
                        kwds in
                    InvalidSearch uu____7025 in
                  FStar_Exn.raise uu____7024
              | uu____7030 -> (QueryOK, (FStar_Util.JsonList js))
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
    fun uu___220_7081  ->
      match uu___220_7081 with
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
      | Push (SyntaxCheck ,uu____7143,uu____7144,uu____7145,false ) ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____7146 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = MissingCurrentModule; qid = (q.qid) }
           | uu____7147 -> q)
let rec go: repl_state -> Prims.unit =
  fun st  ->
    let query =
      let uu____7153 = read_interactive_query st.repl_stdin in
      validate_query st uu____7153 in
    let uu____7154 = let uu____7167 = run_query st in uu____7167 query.qq in
    match uu____7154 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____7211 =
      let uu____7214 = FStar_ST.op_Bang issues in e :: uu____7214 in
    FStar_ST.op_Colon_Equals issues uu____7211 in
  let count_errors uu____7348 =
    let uu____7349 =
      let uu____7352 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____7352 in
    FStar_List.length uu____7349 in
  let report1 uu____7426 =
    let uu____7427 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____7427 in
  let clear1 uu____7497 = FStar_ST.op_Colon_Equals issues [] in
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
             let uu____7584 = get_json () in write_message label1 uu____7584)
  }
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let uu____7590 = deps_of_our_file filename in
     match uu____7590 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____7614 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu____7614 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____7641 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____7642 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____7641 uu____7642 in
              let env2 =
                let uu____7648 =
                  FStar_TypeChecker_Env.set_range
                    (FStar_Pervasives_Native.snd env1) initial_range in
                ((FStar_Pervasives_Native.fst env1), uu____7648) in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2 in
              (FStar_TypeChecker_Env.toggle_id_info
                 (FStar_Pervasives_Native.snd env3) true;
               (let init_st =
                  let uu____7661 = FStar_Util.open_stdin () in
                  {
                    repl_line = (Prims.parse_int "1");
                    repl_column = (Prims.parse_int "0");
                    repl_fname = filename;
                    repl_stack = stack;
                    repl_curmod = FStar_Pervasives_Native.None;
                    repl_env = env3;
                    repl_ts = ts;
                    repl_stdin = uu____7661
                  } in
                let uu____7662 =
                  (FStar_Options.record_hints ()) ||
                    (FStar_Options.use_hints ()) in
                if uu____7662
                then
                  let uu____7663 =
                    let uu____7664 = FStar_Options.file_list () in
                    FStar_List.hd uu____7664 in
                  FStar_SMTEncoding_Solver.with_hints_db uu____7663
                    (fun uu____7668  -> go init_st)
                else go init_st))))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    (let uu____7676 =
       let uu____7677 = FStar_Options.codegen () in
       FStar_Option.isSome uu____7677 in
     if uu____7676
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____7681 = FStar_Options.trace_error () in
     if uu____7681
     then interactive_mode' filename
     else
       (try
          FStar_Errors.set_handler interactive_error_handler;
          interactive_mode' filename
        with
        | e ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise e)))