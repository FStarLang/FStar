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
                let uu___219_379 = tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___219_379.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___219_379.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___219_379.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___219_379.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___219_379.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___219_379.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___219_379.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___219_379.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___219_379.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___219_379.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___219_379.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___219_379.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___219_379.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___219_379.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___219_379.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___219_379.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___219_379.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___219_379.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = (kind = LaxCheck);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___219_379.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___219_379.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___219_379.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.type_of =
                    (uu___219_379.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___219_379.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___219_379.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___219_379.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___219_379.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___219_379.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___219_379.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___219_379.FStar_TypeChecker_Env.identifier_info)
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
             | FStar_All.Failure msg when
                 let uu____697 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____697 ->
                 let msg1 =
                   Prims.strcat "ASSERTION FAILURE: "
                     (Prims.strcat msg
                        (Prims.strcat "\n"
                           (Prims.strcat
                              "F* may be in an inconsistent state.\n"
                              (Prims.strcat
                                 "Please file a bug report, ideally with a "
                                 "minimized version of the program that triggered the error.")))) in
                 ((let uu____700 =
                     let uu____707 =
                       let uu____712 = FStar_TypeChecker_Env.get_range env in
                       (msg1, uu____712) in
                     [uu____707] in
                   FStar_TypeChecker_Err.add_errors env uu____700);
                  FStar_Util.print_error msg1;
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Error (msg,r) when
                 let uu____736 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____736 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____759 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____759 ->
                 ((let uu____761 =
                     let uu____768 =
                       let uu____773 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____773) in
                     [uu____768] in
                   FStar_TypeChecker_Err.add_errors env uu____761);
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
    let uu____809 =
      FStar_List.partition
        (fun x  ->
           let uu____822 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____823 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____822 <> uu____823) deps in
    match uu____809 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____850 =
                  (let uu____853 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____853) ||
                    (let uu____855 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____855) in
                if uu____850
                then
                  let uu____856 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____856
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____859 ->
              ((let uu____863 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____863);
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
            | uu____918 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____937 =
                    let uu____938 = FStar_Options.lax () in
                    if uu____938 then LaxCheck else FullCheck in
                  push env uu____937 true "typecheck_modul" in
                let uu____940 = tc_one_file remaining env1 in
                (match uu____940 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____991 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____1004 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____1004
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____991 with
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
                 | (uu____1108,uu____1109) ->
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
                     | uu____1204 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1232 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1315::ts3 ->
                    (pop env1 "";
                     (let uu____1356 =
                        let uu____1371 = FStar_List.hd stack in
                        let uu____1380 = FStar_List.tl stack in
                        (uu____1371, uu____1380) in
                      match uu____1356 with
                      | ((env2,uu____1406),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1470 = ts_elt in
                  (match uu____1470 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1501 = match_dep depnames intf impl in
                       (match uu____1501 with
                        | (b,depnames') ->
                            let uu____1520 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1520
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1541 =
                                 let uu____1556 = FStar_List.hd st in
                                 let uu____1565 = FStar_List.tl st in
                                 (uu____1556, uu____1565) in
                               match uu____1541 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1642 = deps_of_our_file filename in
            match uu____1642 with
            | (filenames,uu____1658) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___209_1718  ->
    match uu___209_1718 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1722 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1722
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1724 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1727 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1745 -> true
    | uu____1750 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1766 -> uu____1766
let js_fail: 'Auu____1777 . Prims.string -> FStar_Util.json -> 'Auu____1777 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___210_1789  ->
    match uu___210_1789 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___211_1795  ->
    match uu___211_1795 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list:
  'Auu____1804 .
    (FStar_Util.json -> 'Auu____1804) ->
      FStar_Util.json -> 'Auu____1804 Prims.list
  =
  fun k  ->
    fun uu___212_1817  ->
      match uu___212_1817 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___213_1835  ->
    match uu___213_1835 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1860 = js_str s in
    match uu____1860 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1861 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1866 = js_str s in
    match uu____1866 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | "reify" -> FStar_TypeChecker_Normalize.Reify
    | "pure-subterms" ->
        FStar_TypeChecker_Normalize.PureSubtermsWithinComputations
    | uu____1867 -> js_fail "reduction rule" s
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
    match projectee with | Exit  -> true | uu____1938 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1943 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1948 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1953 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1969 -> false
let __proj__Push__item___0:
  query' ->
    (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____2013 -> false
let __proj__AutoComplete__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2043 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,(Prims.string,Prims.int,Prims.int)
                    FStar_Pervasives_Native.tuple3
                    FStar_Pervasives_Native.option,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2113 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2151 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_MissingCurrentModule: query' -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MissingCurrentModule  -> true
    | uu____2164 -> false
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2170 -> false
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
  fun uu___214_2194  ->
    match uu___214_2194 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Pop  -> false
    | Push uu____2195 -> false
    | MissingCurrentModule  -> false
    | ProtocolViolation uu____2206 -> false
    | AutoComplete uu____2207 -> true
    | Lookup uu____2208 -> true
    | Compute uu____2225 -> true
    | Search uu____2234 -> true
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
    | InvalidQuery uu____2244 -> true
    | uu____2245 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2253 -> uu____2253
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2258 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2263 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2268 -> false
let try_assoc:
  'Auu____2277 'Auu____2278 .
    'Auu____2278 ->
      ('Auu____2278,'Auu____2277) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2277 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2301 =
        FStar_Util.try_find
          (fun uu____2315  ->
             match uu____2315 with | (k,uu____2321) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2301
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2338 =
          let uu____2339 =
            let uu____2340 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2340 in
          ProtocolViolation uu____2339 in
        { qq = uu____2338; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2367 = try_assoc key a in
      match uu____2367 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2371 =
            let uu____2372 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____2372 in
          FStar_Exn.raise uu____2371 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____2387 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2387 js_str in
    try
      let query =
        let uu____2396 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____2396 js_str in
      let args =
        let uu____2404 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____2404 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____2421 = try_assoc k args in
        match uu____2421 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____2429 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____2430 =
              let uu____2441 =
                let uu____2442 = arg "kind" in
                FStar_All.pipe_right uu____2442 js_pushkind in
              let uu____2443 =
                let uu____2444 = arg "code" in
                FStar_All.pipe_right uu____2444 js_str in
              let uu____2445 =
                let uu____2446 = arg "line" in
                FStar_All.pipe_right uu____2446 js_int in
              let uu____2447 =
                let uu____2448 = arg "column" in
                FStar_All.pipe_right uu____2448 js_int in
              (uu____2441, uu____2443, uu____2445, uu____2447,
                (query = "peek")) in
            Push uu____2430
        | "push" ->
            let uu____2449 =
              let uu____2460 =
                let uu____2461 = arg "kind" in
                FStar_All.pipe_right uu____2461 js_pushkind in
              let uu____2462 =
                let uu____2463 = arg "code" in
                FStar_All.pipe_right uu____2463 js_str in
              let uu____2464 =
                let uu____2465 = arg "line" in
                FStar_All.pipe_right uu____2465 js_int in
              let uu____2466 =
                let uu____2467 = arg "column" in
                FStar_All.pipe_right uu____2467 js_int in
              (uu____2460, uu____2462, uu____2464, uu____2466,
                (query = "peek")) in
            Push uu____2449
        | "autocomplete" ->
            let uu____2468 =
              let uu____2469 = arg "partial-symbol" in
              FStar_All.pipe_right uu____2469 js_str in
            AutoComplete uu____2468
        | "lookup" ->
            let uu____2470 =
              let uu____2487 =
                let uu____2488 = arg "symbol" in
                FStar_All.pipe_right uu____2488 js_str in
              let uu____2489 =
                let uu____2498 =
                  let uu____2507 = try_arg "location" in
                  FStar_All.pipe_right uu____2507
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____2498
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____2565 =
                          let uu____2566 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____2566 js_str in
                        let uu____2567 =
                          let uu____2568 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____2568 js_int in
                        let uu____2569 =
                          let uu____2570 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____2570 js_int in
                        (uu____2565, uu____2567, uu____2569))) in
              let uu____2571 =
                let uu____2574 = arg "requested-info" in
                FStar_All.pipe_right uu____2574 (js_list js_str) in
              (uu____2487, uu____2489, uu____2571) in
            Lookup uu____2470
        | "compute" ->
            let uu____2587 =
              let uu____2596 =
                let uu____2597 = arg "term" in
                FStar_All.pipe_right uu____2597 js_str in
              let uu____2598 =
                let uu____2603 = try_arg "rules" in
                FStar_All.pipe_right uu____2603
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____2596, uu____2598) in
            Compute uu____2587
        | "search" ->
            let uu____2618 =
              let uu____2619 = arg "terms" in
              FStar_All.pipe_right uu____2619 js_str in
            Search uu____2618
        | uu____2620 ->
            let uu____2621 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____2621 in
      { qq = uu____2429; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____2635 = FStar_Util.read_line stream in
      match uu____2635 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some line ->
          let uu____2639 = FStar_Util.json_of_string line in
          (match uu____2639 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               unpack_interactive_query request)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let rec json_of_fstar_option: FStar_Options.option_val -> FStar_Util.json =
  fun uu___215_2652  ->
    match uu___215_2652 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____2660 = FStar_List.map json_of_fstar_option vs in
        FStar_Util.JsonList uu____2660
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let json_of_opt:
  'Auu____2669 .
    ('Auu____2669 -> FStar_Util.json) ->
      'Auu____2669 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____2687 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____2687
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____2694 =
      let uu____2697 =
        let uu____2698 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____2698 in
      let uu____2699 =
        let uu____2702 =
          let uu____2703 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____2703 in
        [uu____2702] in
      uu____2697 :: uu____2699 in
    FStar_Util.JsonList uu____2694
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____2716 =
          let uu____2723 =
            let uu____2730 =
              let uu____2735 = json_of_pos b in ("beg", uu____2735) in
            let uu____2736 =
              let uu____2743 =
                let uu____2748 = json_of_pos e in ("end", uu____2748) in
              [uu____2743] in
            uu____2730 :: uu____2736 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____2723 in
        FStar_Util.JsonAssoc uu____2716
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2769 = FStar_Range.file_of_use_range r in
    let uu____2770 = FStar_Range.start_of_use_range r in
    let uu____2771 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____2769 uu____2770 uu____2771
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2776 = FStar_Range.file_of_range r in
    let uu____2777 = FStar_Range.start_of_range r in
    let uu____2778 = FStar_Range.end_of_range r in
    json_of_range_fields uu____2776 uu____2777 uu____2778
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
    let uu____2787 =
      let uu____2794 =
        let uu____2801 =
          let uu____2808 =
            let uu____2813 =
              let uu____2814 =
                let uu____2817 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____2823 = json_of_use_range r in [uu____2823] in
                let uu____2824 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____2830 = json_of_def_range r in [uu____2830]
                  | uu____2831 -> [] in
                FStar_List.append uu____2817 uu____2824 in
              FStar_Util.JsonList uu____2814 in
            ("ranges", uu____2813) in
          [uu____2808] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____2801 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____2794 in
    FStar_Util.JsonAssoc uu____2787
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
    let uu____2983 =
      let uu____2990 =
        let uu____2997 =
          let uu____3002 = json_of_opt json_of_def_range lr.lr_def_range in
          ("defined-at", uu____3002) in
        let uu____3003 =
          let uu____3010 =
            let uu____3015 =
              json_of_opt (fun _0_42  -> FStar_Util.JsonStr _0_42) lr.lr_typ in
            ("type", uu____3015) in
          let uu____3016 =
            let uu____3023 =
              let uu____3028 =
                json_of_opt (fun _0_43  -> FStar_Util.JsonStr _0_43)
                  lr.lr_doc in
              ("documentation", uu____3028) in
            let uu____3029 =
              let uu____3036 =
                let uu____3041 =
                  json_of_opt (fun _0_44  -> FStar_Util.JsonStr _0_44)
                    lr.lr_def in
                ("definition", uu____3041) in
              [uu____3036] in
            uu____3023 :: uu____3029 in
          uu____3010 :: uu____3016 in
        uu____2997 :: uu____3003 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____2990 in
    FStar_Util.JsonAssoc uu____2983
let json_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3074 =
      FStar_List.map (fun _0_45  -> FStar_Util.JsonStr _0_45)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_46  -> FStar_Util.JsonList _0_46) uu____3074 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____3096 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____3096);
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
  fun uu____3158  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____3161 =
        FStar_List.map (fun _0_47  -> FStar_Util.JsonStr _0_47)
          interactive_protocol_features in
      FStar_Util.JsonList uu____3161 in
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
        let uu____3322 = FStar_Options.docs () in
        FStar_Util.smap_of_list uu____3322 in
      let get_doc k = FStar_Util.smap_try_find opt_docs k in
      FStar_List.map
        (fun uu____3354  ->
           match uu____3354 with
           | (k,v1) ->
               let uu____3371 = FStar_Options.get_option k in
               let uu____3372 = get_doc k in (k, uu____3371, uu____3372, v1))
        FStar_Options.defaults in
    let uu____3377 =
      let uu____3382 =
        let uu____3383 =
          FStar_List.map
            (fun uu____3403  ->
               match uu____3403 with
               | (uu____3416,fstname,uu____3418,uu____3419) ->
                   FStar_Util.JsonStr fstname) st.repl_ts in
        FStar_Util.JsonList uu____3383 in
      ("loaded-dependencies", uu____3382) in
    let uu____3428 =
      let uu____3435 =
        let uu____3440 =
          let uu____3441 =
            FStar_List.map
              (fun uu____3460  ->
                 match uu____3460 with
                 | (name,value,doc1,dflt1) ->
                     let uu____3479 =
                       let uu____3486 =
                         let uu____3493 =
                           let uu____3498 = json_of_fstar_option value in
                           ("value", uu____3498) in
                         let uu____3499 =
                           let uu____3506 =
                             let uu____3511 = json_of_fstar_option dflt1 in
                             ("default", uu____3511) in
                           let uu____3512 =
                             let uu____3519 =
                               let uu____3524 =
                                 json_of_opt
                                   (fun _0_48  -> FStar_Util.JsonStr _0_48)
                                   doc1 in
                               ("documentation", uu____3524) in
                             [uu____3519] in
                           uu____3506 :: uu____3512 in
                         uu____3493 :: uu____3499 in
                       ("name", (FStar_Util.JsonStr name)) :: uu____3486 in
                     FStar_Util.JsonAssoc uu____3479) opts_and_defaults in
          FStar_Util.JsonList uu____3441 in
        ("options", uu____3440) in
      [uu____3435] in
    uu____3377 :: uu____3428
let with_printed_effect_args:
  'Auu____3561 . (Prims.unit -> 'Auu____3561) -> 'Auu____3561 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____3573  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____3584  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
let sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____3590  -> FStar_Syntax_Print.sigelt_to_string se)
let run_exit:
  'Auu____3597 'Auu____3598 .
    'Auu____3598 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3597,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol:
  'Auu____3629 'Auu____3630 .
    'Auu____3630 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____3630,'Auu____3629) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl:
  'Auu____3659 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____3659) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____3676 =
      let uu____3681 =
        let uu____3682 = json_of_repl_state st in
        FStar_Util.JsonAssoc uu____3682 in
      (QueryOK, uu____3681) in
    (uu____3676, (FStar_Util.Inl st))
let run_protocol_violation:
  'Auu____3705 'Auu____3706 .
    'Auu____3706 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____3706,'Auu____3705) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_missing_current_module:
  'Auu____3745 'Auu____3746 'Auu____3747 .
    'Auu____3747 ->
      'Auu____3746 ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____3747,'Auu____3745) FStar_Util.either)
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
  'Auu____3800 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____3800) FStar_Util.either)
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
               let uu___226_3869 = st in
               {
                 repl_line = (uu___226_3869.repl_line);
                 repl_column = (uu___226_3869.repl_column);
                 repl_fname = (uu___226_3869.repl_fname);
                 repl_stack = stack;
                 repl_curmod = curmod;
                 repl_env = env;
                 repl_ts = (uu___226_3869.repl_ts);
                 repl_stdin = (uu___226_3869.repl_stdin)
               } in
             if nothing_left_to_pop st' then cleanup env else ();
             ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))))
let run_push:
  'Auu____3894 .
    repl_state ->
      push_kind ->
        Prims.string ->
          Prims.int ->
            Prims.int ->
              Prims.bool ->
                ((query_status,FStar_Util.json)
                   FStar_Pervasives_Native.tuple2,(repl_state,'Auu____3894)
                                                    FStar_Util.either)
                  FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun kind  ->
      fun text1  ->
        fun line  ->
          fun column  ->
            fun peek_only  ->
              let uu____3931 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
              match uu____3931 with
              | (stack,env,ts) ->
                  let uu____3953 =
                    if nothing_left_to_pop st
                    then
                      let uu____3974 =
                        update_deps st.repl_fname st.repl_curmod stack env ts in
                      (true, uu____3974)
                    else (false, (stack, env, ts)) in
                  (match uu____3953 with
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
                         let uu____4056 = FStar_Errors.report_all () in
                         FStar_All.pipe_right uu____4056
                           (FStar_List.map json_of_issue) in
                       (FStar_Errors.clear ();
                        (let st' =
                           let uu___227_4065 = st in
                           {
                             repl_line = line;
                             repl_column = column;
                             repl_fname = (uu___227_4065.repl_fname);
                             repl_stack = stack2;
                             repl_curmod = (uu___227_4065.repl_curmod);
                             repl_env = (uu___227_4065.repl_env);
                             repl_ts = ts1;
                             repl_stdin = (uu___227_4065.repl_stdin)
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
                                  (let uu___228_4119 = st' in
                                   {
                                     repl_line = (uu___228_4119.repl_line);
                                     repl_column =
                                       (uu___228_4119.repl_column);
                                     repl_fname = (uu___228_4119.repl_fname);
                                     repl_stack = (uu___228_4119.repl_stack);
                                     repl_curmod = curmod;
                                     repl_env = env4;
                                     repl_ts = (uu___228_4119.repl_ts);
                                     repl_stdin = (uu___228_4119.repl_stdin)
                                   })))
                         | uu____4120 ->
                             let env3 = reset_mark env_mark in
                             let uu____4140 =
                               run_pop
                                 (let uu___229_4154 = st' in
                                  {
                                    repl_line = (uu___229_4154.repl_line);
                                    repl_column = (uu___229_4154.repl_column);
                                    repl_fname = (uu___229_4154.repl_fname);
                                    repl_stack = (uu___229_4154.repl_stack);
                                    repl_curmod = (uu___229_4154.repl_curmod);
                                    repl_env = env3;
                                    repl_ts = (uu___229_4154.repl_ts);
                                    repl_stdin = (uu___229_4154.repl_stdin)
                                  }) in
                             (match uu____4140 with
                              | (uu____4167,st'') ->
                                  let status =
                                    if peek_only then QueryOK else QueryNOK in
                                  ((status, (FStar_Util.JsonList errors)),
                                    st'')))))
let run_lookup:
  'Auu____4205 .
    repl_state ->
      Prims.string ->
        (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option ->
          Prims.string Prims.list ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____4205) FStar_Util.either)
              FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____4254 = st.repl_env in
          match uu____4254 with
          | (dsenv,tcenv) ->
              let info_of_lid_str lid_str =
                let lid =
                  let uu____4286 =
                    FStar_List.map FStar_Ident.id_of_text
                      (FStar_Util.split lid_str ".") in
                  FStar_Ident.lid_of_ids uu____4286 in
                let lid1 =
                  let uu____4290 =
                    FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                      lid in
                  FStar_All.pipe_left (FStar_Util.dflt lid) uu____4290 in
                let uu____4295 =
                  FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
                FStar_All.pipe_right uu____4295
                  (FStar_Util.map_option
                     (fun uu____4350  ->
                        match uu____4350 with
                        | ((uu____4369,typ),r) ->
                            ((FStar_Util.Inr lid1), typ, r))) in
              let docs_of_lid lid =
                let uu____4386 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
                FStar_All.pipe_right uu____4386
                  (FStar_Util.map_option FStar_Pervasives_Native.fst) in
              let def_of_lid lid =
                let uu____4415 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
                FStar_Util.bind_opt uu____4415
                  (fun uu___216_4459  ->
                     match uu___216_4459 with
                     | (FStar_Util.Inr (se,uu____4481),uu____4482) ->
                         let uu____4511 = sigelt_to_string se in
                         FStar_Pervasives_Native.Some uu____4511
                     | uu____4512 -> FStar_Pervasives_Native.None) in
              let info_at_pos_opt =
                FStar_Util.bind_opt pos_opt
                  (fun uu____4564  ->
                     match uu____4564 with
                     | (file,row,col) ->
                         FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
              let info_opt =
                match info_at_pos_opt with
                | FStar_Pervasives_Native.Some uu____4611 -> info_at_pos_opt
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
                        let uu____4713 = term_to_string tcenv typ in
                        FStar_Pervasives_Native.Some uu____4713
                      else FStar_Pervasives_Native.None in
                    let doc_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "documentation" requested_info ->
                          docs_of_lid lid
                      | uu____4721 -> FStar_Pervasives_Native.None in
                    let def_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "definition" requested_info ->
                          def_of_lid lid
                      | uu____4732 -> FStar_Pervasives_Native.None in
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
                    let uu____4744 = json_of_lookup_result result in
                    (QueryOK, uu____4744) in
              (response, (FStar_Util.Inl st))
let run_completions:
  'Auu____4759 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4759) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      let uu____4780 = st.repl_env in
      match uu____4780 with
      | (dsenv,tcenv) ->
          let rec measure_anchored_match search_term1 candidate =
            match (search_term1, candidate) with
            | ([],uu____4830) ->
                FStar_Pervasives_Native.Some ([], (Prims.parse_int "0"))
            | (uu____4845,[]) -> FStar_Pervasives_Native.None
            | (hs::ts,hc::tc) ->
                let hc_text = FStar_Ident.text_of_id hc in
                if FStar_Util.starts_with hc_text hs
                then
                  (match ts with
                   | [] ->
                       FStar_Pervasives_Native.Some
                         (candidate, (FStar_String.length hs))
                   | uu____4895 ->
                       let uu____4898 = measure_anchored_match ts tc in
                       FStar_All.pipe_right uu____4898
                         (FStar_Util.map_option
                            (fun uu____4938  ->
                               match uu____4938 with
                               | (matched,len) ->
                                   ((hc :: matched),
                                     (((FStar_String.length hc_text) +
                                         (Prims.parse_int "1"))
                                        + len)))))
                else FStar_Pervasives_Native.None in
          let rec locate_match needle candidate =
            let uu____4993 = measure_anchored_match needle candidate in
            match uu____4993 with
            | FStar_Pervasives_Native.Some (matched,n1) ->
                FStar_Pervasives_Native.Some ([], matched, n1)
            | FStar_Pervasives_Native.None  ->
                (match candidate with
                 | [] -> FStar_Pervasives_Native.None
                 | hc::tc ->
                     let uu____5072 = locate_match needle tc in
                     FStar_All.pipe_right uu____5072
                       (FStar_Util.map_option
                          (fun uu____5133  ->
                             match uu____5133 with
                             | (prefix1,matched,len) ->
                                 ((hc :: prefix1), matched, len)))) in
          let str_of_ids ids =
            let uu____5177 = FStar_List.map FStar_Ident.text_of_id ids in
            FStar_Util.concat_l "." uu____5177 in
          let match_lident_against needle lident =
            locate_match needle
              (FStar_List.append lident.FStar_Ident.ns
                 [lident.FStar_Ident.ident]) in
          let shorten_namespace uu____5224 =
            match uu____5224 with
            | (prefix1,matched,match_len) ->
                let naked_match =
                  match matched with
                  | uu____5255::[] -> true
                  | uu____5256 -> false in
                let uu____5259 =
                  FStar_ToSyntax_Env.shorten_module_path dsenv prefix1
                    naked_match in
                (match uu____5259 with
                 | (stripped_ns,shortened) ->
                     let uu____5286 = str_of_ids shortened in
                     let uu____5287 = str_of_ids matched in
                     let uu____5288 = str_of_ids stripped_ns in
                     (uu____5286, uu____5287, uu____5288, match_len)) in
          let prepare_candidate uu____5306 =
            match uu____5306 with
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
                        let uu____5434 =
                          FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                            dsenv lid in
                        FStar_Option.map
                          (fun fqn  ->
                             let uu____5450 =
                               let uu____5453 =
                                 FStar_List.map FStar_Ident.id_of_text
                                   orig_ns in
                               FStar_List.append uu____5453
                                 [fqn.FStar_Ident.ident] in
                             ([], uu____5450, matched_length)) uu____5434
                      else FStar_Pervasives_Native.None)) in
            let case_b_find_matches_in_env uu____5486 =
              let matches =
                FStar_List.filter_map (match_lident_against needle)
                  all_lidents_in_env in
              FStar_All.pipe_right matches
                (FStar_List.filter
                   (fun uu____5561  ->
                      match uu____5561 with
                      | (ns,id,uu____5574) ->
                          let uu____5583 =
                            let uu____5586 = FStar_Ident.lid_of_ids id in
                            FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                              dsenv uu____5586 in
                          (match uu____5583 with
                           | FStar_Pervasives_Native.None  -> false
                           | FStar_Pervasives_Native.Some l ->
                               let uu____5588 =
                                 FStar_Ident.lid_of_ids
                                   (FStar_List.append ns id) in
                               FStar_Ident.lid_equals l uu____5588))) in
            let uu____5589 = FStar_Util.prefix needle in
            match uu____5589 with
            | (ns,id) ->
                let matched_ids =
                  match ns with
                  | [] -> case_b_find_matches_in_env ()
                  | uu____5635 ->
                      let l =
                        FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
                      let uu____5639 =
                        FStar_ToSyntax_Env.resolve_module_name dsenv l true in
                      (match uu____5639 with
                       | FStar_Pervasives_Native.None  ->
                           case_b_find_matches_in_env ()
                       | FStar_Pervasives_Native.Some m ->
                           case_a_find_transitive_includes ns m id) in
                FStar_All.pipe_right matched_ids
                  (FStar_List.map
                     (fun x  ->
                        let uu____5704 = shorten_namespace x in
                        prepare_candidate uu____5704)) in
          let json_candidates =
            let uu____5716 =
              FStar_Util.sort_with
                (fun uu____5739  ->
                   fun uu____5740  ->
                     match (uu____5739, uu____5740) with
                     | ((cd1,ns1,uu____5767),(cd2,ns2,uu____5770)) ->
                         (match FStar_String.compare cd1 cd2 with
                          | _0_49 when _0_49 = (Prims.parse_int "0") ->
                              FStar_String.compare ns1 ns2
                          | n1 -> n1)) matches in
            FStar_List.map
              (fun uu____5794  ->
                 match uu____5794 with
                 | (candidate,ns,match_len) ->
                     FStar_Util.JsonList
                       [FStar_Util.JsonInt match_len;
                       FStar_Util.JsonStr ns;
                       FStar_Util.JsonStr candidate]) uu____5716 in
          ((QueryOK, (FStar_Util.JsonList json_candidates)),
            (FStar_Util.Inl st))
let run_compute:
  'Auu____5820 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____5820) FStar_Util.either)
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
            let uu___230_5901 = st1 in
            {
              repl_line = (uu___230_5901.repl_line);
              repl_column = (uu___230_5901.repl_column);
              repl_fname = (uu___230_5901.repl_fname);
              repl_stack = (uu___230_5901.repl_stack);
              repl_curmod = (uu___230_5901.repl_curmod);
              repl_env = env;
              repl_ts = (uu___230_5901.repl_ts);
              repl_stdin = (uu___230_5901.repl_stdin)
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
                ((uu____5953,{ FStar_Syntax_Syntax.lbname = uu____5954;
                               FStar_Syntax_Syntax.lbunivs = univs1;
                               FStar_Syntax_Syntax.lbtyp = uu____5956;
                               FStar_Syntax_Syntax.lbeff = uu____5957;
                               FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____5959);
              FStar_Syntax_Syntax.sigrng = uu____5960;
              FStar_Syntax_Syntax.sigquals = uu____5961;
              FStar_Syntax_Syntax.sigmeta = uu____5962;
              FStar_Syntax_Syntax.sigattrs = uu____5963;_}::[] ->
              FStar_Pervasives_Native.Some (univs1, def)
          | uu____6002 -> FStar_Pervasives_Native.None in
        let parse1 frag =
          let uu____6021 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
          match uu____6021 with
          | FStar_Util.Inl (FStar_Util.Inr decls,uu____6045) ->
              FStar_Pervasives_Native.Some decls
          | uu____6090 -> FStar_Pervasives_Native.None in
        let desugar dsenv decls =
          let uu____6122 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
          FStar_Pervasives_Native.snd uu____6122 in
        let typecheck tcenv decls =
          let uu____6140 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
          match uu____6140 with | (ses,uu____6154,uu____6155) -> ses in
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
             let uu____6183 = st1.repl_env in
             match uu____6183 with
             | (dsenv,tcenv) ->
                 let frag = dummy_let_fragment term in
                 (match st1.repl_curmod with
                  | FStar_Pervasives_Native.None  ->
                      (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                  | uu____6195 ->
                      let uu____6196 = parse1 frag in
                      (match uu____6196 with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr "Could not parse this term"))
                       | FStar_Pervasives_Native.Some decls ->
                           let aux uu____6219 =
                             let decls1 = desugar dsenv decls in
                             let ses = typecheck tcenv decls1 in
                             match find_let_body ses with
                             | FStar_Pervasives_Native.None  ->
                                 (QueryNOK,
                                   (FStar_Util.JsonStr
                                      "Typechecking yielded an unexpected term"))
                             | FStar_Pervasives_Native.Some (univs1,def) ->
                                 let uu____6254 =
                                   FStar_Syntax_Subst.open_univ_vars univs1
                                     def in
                                 (match uu____6254 with
                                  | (univs2,def1) ->
                                      let tcenv1 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          tcenv univs2 in
                                      let normalized =
                                        normalize_term1 tcenv1 rules1 def1 in
                                      let uu____6267 =
                                        let uu____6268 =
                                          term_to_string tcenv1 normalized in
                                        FStar_Util.JsonStr uu____6268 in
                                      (QueryOK, uu____6267)) in
                           let uu____6269 = FStar_Options.trace_error () in
                           if uu____6269
                           then aux ()
                           else
                             (try aux ()
                              with
                              | e ->
                                  let uu____6294 =
                                    let uu____6295 =
                                      FStar_Errors.issue_of_exn e in
                                    match uu____6295 with
                                    | FStar_Pervasives_Native.Some issue ->
                                        let uu____6299 =
                                          FStar_Errors.format_issue issue in
                                        FStar_Util.JsonStr uu____6299
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Exn.raise e in
                                  (QueryNOK, uu____6294)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____6321 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____6335 -> false
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
  fun uu___217_6359  ->
    match uu___217_6359 with
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
    let uu____6527 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____6534 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____6527; sc_fvars = uu____6534 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____6583 = FStar_ST.op_Bang sc.sc_typ in
      match uu____6583 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____6608 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____6608 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____6629,typ),uu____6631) ->
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
      let uu____6675 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____6675 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____6718 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____6718 in
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
          let uu____6761 = sc_typ tcenv sc in term_to_string tcenv uu____6761 in
        let uu____6762 =
          let uu____6769 =
            let uu____6774 =
              let uu____6775 =
                let uu____6776 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____6776.FStar_Ident.str in
              FStar_Util.JsonStr uu____6775 in
            ("lid", uu____6774) in
          [uu____6769; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____6762
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____6796 -> true
    | uu____6797 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____6805 -> uu____6805
let run_search:
  'Auu____6812 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6812) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_str  ->
      let uu____6833 = st.repl_env in
      match uu____6833 with
      | (dsenv,tcenv) ->
          let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
          let st_matches candidate term =
            let found =
              match term.st_term with
              | NameContainsStr str ->
                  FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
              | TypeContainsLid lid ->
                  let uu____6861 = sc_fvars tcenv candidate in
                  FStar_Util.set_mem lid uu____6861 in
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
                  let uu____6885 =
                    let uu____6886 =
                      FStar_Util.format1 "Improperly quoted search term: %s"
                        term1 in
                    InvalidSearch uu____6886 in
                  FStar_Exn.raise uu____6885
                else
                  if beg_quote
                  then
                    (let uu____6888 = strip_quotes term1 in
                     NameContainsStr uu____6888)
                  else
                    (let lid = FStar_Ident.lid_of_str term1 in
                     let uu____6891 =
                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                         dsenv lid in
                     match uu____6891 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____6894 =
                           let uu____6895 =
                             FStar_Util.format1 "Unknown identifier: %s"
                               term1 in
                           InvalidSearch uu____6895 in
                         FStar_Exn.raise uu____6894
                     | FStar_Pervasives_Native.Some lid1 ->
                         TypeContainsLid lid1) in
              { st_negate = negate; st_term = parsed } in
            let terms =
              FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
            let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
            FStar_Util.sort_with cmp terms in
          let pprint_one term =
            let uu____6911 =
              match term.st_term with
              | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
              | TypeContainsLid l ->
                  FStar_Util.format1 "%s" l.FStar_Ident.str in
            Prims.strcat (if term.st_negate then "-" else "") uu____6911 in
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
                    let uu____6974 = FStar_List.map pprint_one terms in
                    FStar_Util.concat_l " " uu____6974 in
                  let uu____6977 =
                    let uu____6978 =
                      FStar_Util.format1 "No results found for query [%s]"
                        kwds in
                    InvalidSearch uu____6978 in
                  FStar_Exn.raise uu____6977
              | uu____6983 -> (QueryOK, (FStar_Util.JsonList js))
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
    fun uu___218_7034  ->
      match uu___218_7034 with
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
      | Push (SyntaxCheck ,uu____7096,uu____7097,uu____7098,false ) ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____7099 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = MissingCurrentModule; qid = (q.qid) }
           | uu____7100 -> q)
let rec go: repl_state -> Prims.unit =
  fun st  ->
    let query =
      let uu____7106 = read_interactive_query st.repl_stdin in
      validate_query st uu____7106 in
    let uu____7107 = let uu____7120 = run_query st in uu____7120 query.qq in
    match uu____7107 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____7164 =
      let uu____7167 = FStar_ST.op_Bang issues in e :: uu____7167 in
    FStar_ST.op_Colon_Equals issues uu____7164 in
  let count_errors uu____7237 =
    let uu____7238 =
      let uu____7241 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____7241 in
    FStar_List.length uu____7238 in
  let report1 uu____7283 =
    let uu____7284 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____7284 in
  let clear1 uu____7322 = FStar_ST.op_Colon_Equals issues [] in
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
             let uu____7377 = get_json () in write_message label1 uu____7377)
  }
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let uu____7383 = deps_of_our_file filename in
     match uu____7383 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____7407 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu____7407 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____7434 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____7435 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____7434 uu____7435 in
              let env2 =
                let uu____7441 =
                  FStar_TypeChecker_Env.set_range
                    (FStar_Pervasives_Native.snd env1) initial_range in
                ((FStar_Pervasives_Native.fst env1), uu____7441) in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2 in
              (FStar_TypeChecker_Env.toggle_id_info
                 (FStar_Pervasives_Native.snd env3) true;
               (let init_st =
                  let uu____7454 = FStar_Util.open_stdin () in
                  {
                    repl_line = (Prims.parse_int "1");
                    repl_column = (Prims.parse_int "0");
                    repl_fname = filename;
                    repl_stack = stack;
                    repl_curmod = FStar_Pervasives_Native.None;
                    repl_env = env3;
                    repl_ts = ts;
                    repl_stdin = uu____7454
                  } in
                let uu____7455 =
                  (FStar_Options.record_hints ()) ||
                    (FStar_Options.use_hints ()) in
                if uu____7455
                then
                  let uu____7456 =
                    let uu____7457 = FStar_Options.file_list () in
                    FStar_List.hd uu____7457 in
                  FStar_SMTEncoding_Solver.with_hints_db uu____7456
                    (fun uu____7461  -> go init_st)
                else go init_st))))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    (let uu____7469 =
       let uu____7470 = FStar_Options.codegen () in
       FStar_Option.isSome uu____7470 in
     if uu____7469
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____7474 = FStar_Options.trace_error () in
     if uu____7474
     then interactive_mode' filename
     else
       (try
          FStar_Errors.set_handler interactive_error_handler;
          interactive_mode' filename
        with
        | e ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise e)))