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
      let uu____18 = uenv in
      match uu____18 with
      | (dsenv,env) ->
          let uu____30 =
            match remaining with
            | intf::impl::remaining1 when
                FStar_Universal.needs_interleaving intf impl ->
                let uu____51 =
                  FStar_Universal.tc_one_file dsenv env
                    (FStar_Pervasives_Native.Some intf) impl in
                (match uu____51 with
                 | (uu____66,dsenv1,env1) ->
                     (((FStar_Pervasives_Native.Some intf), impl), dsenv1,
                       env1, remaining1))
            | intf_or_impl::remaining1 ->
                let uu____83 =
                  FStar_Universal.tc_one_file dsenv env
                    FStar_Pervasives_Native.None intf_or_impl in
                (match uu____83 with
                 | (uu____98,dsenv1,env1) ->
                     ((FStar_Pervasives_Native.None, intf_or_impl), dsenv1,
                       env1, remaining1))
            | [] -> failwith "Impossible" in
          (match uu____30 with
           | ((intf,impl),dsenv1,env1,remaining1) ->
               ((intf, impl), (dsenv1, env1), remaining1))
let tc_prims:
  Prims.unit ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____152  ->
    let uu____153 = FStar_Universal.tc_prims () in
    match uu____153 with | (uu____161,dsenv,env) -> (dsenv, env)
type env_t =
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t,modul_t) FStar_Pervasives_Native.tuple2 Prims.list
let pop uu____186 msg =
  match uu____186 with
  | (uu____190,env) ->
      (FStar_Universal.pop_context env msg; FStar_Options.pop ())
type push_kind =
  | SyntaxCheck
  | LaxCheck
  | FullCheck
let uu___is_SyntaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____196 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____200 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____204 -> false
let push:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    push_kind ->
      Prims.bool ->
        Prims.string ->
          (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2
  =
  fun uu____217  ->
    fun kind  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____217 with
          | (dsenv,tcenv) ->
              let tcenv1 =
                let uu___207_228 = tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___207_228.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___207_228.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___207_228.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___207_228.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___207_228.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___207_228.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___207_228.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___207_228.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___207_228.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___207_228.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___207_228.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___207_228.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___207_228.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___207_228.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___207_228.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___207_228.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___207_228.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___207_228.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = (kind = LaxCheck);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___207_228.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___207_228.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___207_228.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___207_228.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___207_228.FStar_TypeChecker_Env.qname_and_index)
                } in
              let dsenv1 =
                FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck) in
              let res = FStar_Universal.push_context (dsenv1, tcenv1) msg in
              (FStar_Options.push ();
               if restore_cmd_line_options1
               then
                 (let uu____235 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____235 FStar_Pervasives.ignore)
               else ();
               res)
let mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____243  ->
    match uu____243 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.mark dsenv in
        let env1 = FStar_TypeChecker_Env.mark env in
        (FStar_Options.push (); (dsenv1, env1))
let reset_mark uu____263 =
  match uu____263 with
  | (uu____266,env) ->
      let dsenv = FStar_ToSyntax_Env.reset_mark () in
      let env1 = FStar_TypeChecker_Env.reset_mark env in
      (FStar_Options.pop (); (dsenv, env1))
let cleanup uu____279 =
  match uu____279 with
  | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
let commit_mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____290  ->
    match uu____290 with
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
  fun uu____317  ->
    fun curmod  ->
      fun frag  ->
        match uu____317 with
        | (dsenv,env) ->
            (try
               let uu____349 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag in
               match uu____349 with
               | FStar_Pervasives_Native.Some (m,dsenv1,env1) ->
                   let uu____371 =
                     let uu____378 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____378) in
                   FStar_Pervasives_Native.Some uu____371
               | uu____388 -> FStar_Pervasives_Native.None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____410 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____410 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____423 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____423 ->
                 ((let uu____425 =
                     let uu____429 =
                       let uu____432 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____432) in
                     [uu____429] in
                   FStar_TypeChecker_Err.add_errors env uu____425);
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
    let uu____452 =
      FStar_List.partition
        (fun x  ->
           let uu____458 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____459 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____458 <> uu____459) deps in
    match uu____452 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____476 =
                  (let uu____477 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____477) ||
                    (let uu____478 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____478) in
                if uu____476
                then
                  let uu____479 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____479
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____482 ->
              ((let uu____485 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____485);
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
            | uu____518 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____529 =
                    let uu____530 = FStar_Options.lax () in
                    if uu____530 then LaxCheck else FullCheck in
                  push env uu____529 true "typecheck_modul" in
                let uu____532 = tc_one_file remaining env1 in
                (match uu____532 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____560 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____568 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____568
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____560 with
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
                 | (uu____634,uu____635) ->
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
                     | uu____699 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____716 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____763::ts3 ->
                    (pop env1 "";
                     (let uu____785 =
                        let uu____793 = FStar_List.hd stack in
                        let uu____798 = FStar_List.tl stack in
                        (uu____793, uu____798) in
                      match uu____785 with
                      | ((env2,uu____812),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____846 = ts_elt in
                  (match uu____846 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____864 = match_dep depnames intf impl in
                       (match uu____864 with
                        | (b,depnames') ->
                            let uu____875 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____875
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____887 =
                                 let uu____895 = FStar_List.hd st in
                                 let uu____900 = FStar_List.tl st in
                                 (uu____895, uu____900) in
                               match uu____887 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____940 = deps_of_our_file filename in
            match uu____940 with
            | (filenames,uu____949) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___197_980  ->
    match uu___197_980 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____984 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____984
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____986 -> "list (...)"
    | FStar_Util.JsonAssoc uu____988 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____999 -> true
    | uu____1002 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1013 -> uu____1013
let js_fail expected got = raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___198_1030  ->
    match uu___198_1030 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___199_1035  ->
    match uu___199_1035 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list k uu___200_1053 =
  match uu___200_1053 with
  | FStar_Util.JsonList l -> FStar_List.map k l
  | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___201_1065  ->
    match uu___201_1065 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1080 = js_str s in
    match uu____1080 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1081 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1085 = js_str s in
    match uu____1085 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | uu____1086 -> js_fail "reduction rule" s
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
    match projectee with | Exit  -> true | uu____1131 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1135 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1139 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1143 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1153 -> false
let __proj__Push__item___0:
  query' ->
    (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1180 -> false
let __proj__AutoComplete__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____1200 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,(Prims.string,Prims.int,Prims.int)
                    FStar_Pervasives_Native.tuple3
                    FStar_Pervasives_Native.option,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____1240 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____1264 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____1276 -> false
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
    | InvalidQuery uu____1298 -> true
    | uu____1299 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____1306 -> uu____1306
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____1310 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____1314 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____1318 -> false
let try_assoc key a =
  let uu____1340 =
    FStar_Util.try_find
      (fun uu____1346  -> match uu____1346 with | (k,uu____1350) -> k = key)
      a in
  FStar_Util.map_option FStar_Pervasives_Native.snd uu____1340
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____1362 =
          let uu____1363 =
            let uu____1364 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____1364 in
          ProtocolViolation uu____1363 in
        { qq = uu____1362; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____1384 = try_assoc key a in
      match uu____1384 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____1387 =
            let uu____1388 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____1388 in
          raise uu____1387 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____1397 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____1397 js_str in
    try
      let query =
        let uu____1400 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____1400 js_str in
      let args =
        let uu____1405 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____1405 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____1418 = try_assoc k args in
        match uu____1418 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____1423 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____1424 =
              let uu____1430 =
                let uu____1431 = arg "kind" in
                FStar_All.pipe_right uu____1431 js_pushkind in
              let uu____1432 =
                let uu____1433 = arg "code" in
                FStar_All.pipe_right uu____1433 js_str in
              let uu____1434 =
                let uu____1435 = arg "line" in
                FStar_All.pipe_right uu____1435 js_int in
              let uu____1436 =
                let uu____1437 = arg "column" in
                FStar_All.pipe_right uu____1437 js_int in
              (uu____1430, uu____1432, uu____1434, uu____1436,
                (query = "peek")) in
            Push uu____1424
        | "push" ->
            let uu____1438 =
              let uu____1444 =
                let uu____1445 = arg "kind" in
                FStar_All.pipe_right uu____1445 js_pushkind in
              let uu____1446 =
                let uu____1447 = arg "code" in
                FStar_All.pipe_right uu____1447 js_str in
              let uu____1448 =
                let uu____1449 = arg "line" in
                FStar_All.pipe_right uu____1449 js_int in
              let uu____1450 =
                let uu____1451 = arg "column" in
                FStar_All.pipe_right uu____1451 js_int in
              (uu____1444, uu____1446, uu____1448, uu____1450,
                (query = "peek")) in
            Push uu____1438
        | "autocomplete" ->
            let uu____1452 =
              let uu____1453 = arg "partial-symbol" in
              FStar_All.pipe_right uu____1453 js_str in
            AutoComplete uu____1452
        | "lookup" ->
            let uu____1454 =
              let uu____1463 =
                let uu____1464 = arg "symbol" in
                FStar_All.pipe_right uu____1464 js_str in
              let uu____1465 =
                let uu____1470 =
                  let uu____1475 = try_arg "location" in
                  FStar_All.pipe_right uu____1475
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____1470
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____1503 =
                          let uu____1504 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____1504 js_str in
                        let uu____1505 =
                          let uu____1506 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____1506 js_int in
                        let uu____1507 =
                          let uu____1508 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____1508 js_int in
                        (uu____1503, uu____1505, uu____1507))) in
              let uu____1509 =
                let uu____1511 = arg "requested-info" in
                FStar_All.pipe_right uu____1511 (js_list js_str) in
              (uu____1463, uu____1465, uu____1509) in
            Lookup uu____1454
        | "compute" ->
            let uu____1518 =
              let uu____1523 =
                let uu____1524 = arg "term" in
                FStar_All.pipe_right uu____1524 js_str in
              let uu____1525 =
                let uu____1528 = try_arg "rules" in
                FStar_All.pipe_right uu____1528
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____1523, uu____1525) in
            Compute uu____1518
        | "search" ->
            let uu____1536 =
              let uu____1537 = arg "terms" in
              FStar_All.pipe_right uu____1537 js_str in
            Search uu____1536
        | uu____1538 ->
            let uu____1539 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____1539 in
      { qq = uu____1423; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let validate_interactive_query: query -> query =
  fun uu___202_1546  ->
    match uu___202_1546 with
    | { qq = Push (SyntaxCheck ,uu____1547,uu____1548,uu____1549,false );
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
      let uu____1556 = FStar_Util.read_line stream in
      match uu____1556 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some line ->
          let uu____1559 = FStar_Util.json_of_string line in
          (match uu____1559 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               let uu____1562 = unpack_interactive_query request in
               validate_interactive_query uu____1562)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let rec json_of_fstar_option: FStar_Options.option_val -> FStar_Util.json =
  fun uu___203_1569  ->
    match uu___203_1569 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____1576 = FStar_List.map json_of_fstar_option vs in
        FStar_Util.JsonList uu____1576
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let json_of_opt json_of_a opt_a =
  let uu____1597 = FStar_Util.map_option json_of_a opt_a in
  FStar_Util.dflt FStar_Util.JsonNull uu____1597
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____1602 =
      let uu____1604 =
        let uu____1605 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____1605 in
      let uu____1606 =
        let uu____1608 =
          let uu____1609 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____1609 in
        [uu____1608] in
      uu____1604 :: uu____1606 in
    FStar_Util.JsonList uu____1602
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____1619 =
          let uu____1623 =
            let uu____1627 =
              let uu____1630 = json_of_pos b in ("beg", uu____1630) in
            let uu____1631 =
              let uu____1635 =
                let uu____1638 = json_of_pos e in ("end", uu____1638) in
              [uu____1635] in
            uu____1627 :: uu____1631 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____1623 in
        FStar_Util.JsonAssoc uu____1619
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____1650 = FStar_Range.file_of_use_range r in
    let uu____1651 = FStar_Range.start_of_use_range r in
    let uu____1652 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____1650 uu____1651 uu____1652
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____1656 = FStar_Range.file_of_range r in
    let uu____1657 = FStar_Range.start_of_range r in
    let uu____1658 = FStar_Range.end_of_range r in
    json_of_range_fields uu____1656 uu____1657 uu____1658
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
    let uu____1665 =
      let uu____1669 =
        let uu____1673 =
          let uu____1677 =
            let uu____1680 =
              let uu____1681 =
                let uu____1683 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____1687 = json_of_use_range r in [uu____1687] in
                let uu____1688 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____1692 = json_of_def_range r in [uu____1692]
                  | uu____1693 -> [] in
                FStar_List.append uu____1683 uu____1688 in
              FStar_Util.JsonList uu____1681 in
            ("ranges", uu____1680) in
          [uu____1677] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____1673 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____1669 in
    FStar_Util.JsonAssoc uu____1665
type lookup_result =
  {
  lr_name: Prims.string;
  lr_def_range: FStar_Range.range FStar_Pervasives_Native.option;
  lr_typ: Prims.string FStar_Pervasives_Native.option;
  lr_doc: Prims.string FStar_Pervasives_Native.option;
  lr_def: Prims.string FStar_Pervasives_Native.option;}
let json_of_lookup_result: lookup_result -> FStar_Util.json =
  fun lr  ->
    let uu____1753 =
      let uu____1757 =
        let uu____1761 =
          let uu____1764 = json_of_opt json_of_def_range lr.lr_def_range in
          ("defined-at", uu____1764) in
        let uu____1765 =
          let uu____1769 =
            let uu____1772 =
              json_of_opt (fun _0_33  -> FStar_Util.JsonStr _0_33) lr.lr_typ in
            ("type", uu____1772) in
          let uu____1773 =
            let uu____1777 =
              let uu____1780 =
                json_of_opt (fun _0_34  -> FStar_Util.JsonStr _0_34)
                  lr.lr_doc in
              ("documentation", uu____1780) in
            let uu____1781 =
              let uu____1785 =
                let uu____1788 =
                  json_of_opt (fun _0_35  -> FStar_Util.JsonStr _0_35)
                    lr.lr_def in
                ("definition", uu____1788) in
              [uu____1785] in
            uu____1777 :: uu____1781 in
          uu____1769 :: uu____1773 in
        uu____1761 :: uu____1765 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____1757 in
    FStar_Util.JsonAssoc uu____1753
let json_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____1806 =
      FStar_List.map (fun _0_36  -> FStar_Util.JsonStr _0_36)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_37  -> FStar_Util.JsonList _0_37) uu____1806 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____1819 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____1819);
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
  fun uu____1857  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____1860 =
        FStar_List.map (fun _0_38  -> FStar_Util.JsonStr _0_38)
          interactive_protocol_features in
      FStar_Util.JsonList uu____1860 in
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
        let uu____1935 = FStar_Options.docs () in
        FStar_Util.smap_of_list uu____1935 in
      let get_doc k = FStar_Util.smap_try_find opt_docs k in
      FStar_List.map
        (fun uu____1951  ->
           match uu____1951 with
           | (k,v1) ->
               let uu____1961 = FStar_Options.get_option k in
               let uu____1962 = get_doc k in (k, uu____1961, uu____1962, v1))
        FStar_Options.defaults in
    let uu____1965 =
      let uu____1968 =
        let uu____1969 =
          FStar_List.map
            (fun uu____1977  ->
               match uu____1977 with
               | (uu____1984,fstname,uu____1986,uu____1987) ->
                   FStar_Util.JsonStr fstname) st.repl_ts in
        FStar_Util.JsonList uu____1969 in
      ("loaded-dependencies", uu____1968) in
    let uu____1992 =
      let uu____1996 =
        let uu____1999 =
          let uu____2000 =
            FStar_List.map
              (fun uu____2007  ->
                 match uu____2007 with
                 | (name,value,doc1,dflt1) ->
                     let uu____2019 =
                       let uu____2023 =
                         let uu____2027 =
                           let uu____2030 = json_of_fstar_option value in
                           ("value", uu____2030) in
                         let uu____2031 =
                           let uu____2035 =
                             let uu____2038 = json_of_fstar_option dflt1 in
                             ("default", uu____2038) in
                           let uu____2039 =
                             let uu____2043 =
                               let uu____2046 =
                                 json_of_opt
                                   (fun _0_39  -> FStar_Util.JsonStr _0_39)
                                   doc1 in
                               ("documentation", uu____2046) in
                             [uu____2043] in
                           uu____2035 :: uu____2039 in
                         uu____2027 :: uu____2031 in
                       ("name", (FStar_Util.JsonStr name)) :: uu____2023 in
                     FStar_Util.JsonAssoc uu____2019) opts_and_defaults in
          FStar_Util.JsonList uu____2000 in
        ("options", uu____1999) in
      [uu____1996] in
    uu____1965 :: uu____1992
let run_exit st =
  ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol st =
  ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
    (FStar_Util.Inl st))
let run_describe_repl st =
  let uu____2114 =
    let uu____2117 =
      let uu____2118 = json_of_repl_state st in
      FStar_Util.JsonAssoc uu____2118 in
    (QueryOK, uu____2117) in
  (uu____2114, (FStar_Util.Inl st))
let run_protocol_violation st message =
  ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
    (FStar_Util.Inl st))
let run_pop st =
  match st.repl_stack with
  | [] ->
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
  | (env,curmod)::stack ->
      (pop st.repl_env "#pop";
       if (FStar_List.length stack) = (FStar_List.length st.repl_ts)
       then cleanup env
       else ();
       ((QueryOK, FStar_Util.JsonNull),
         (FStar_Util.Inl
            ((let uu___214_2196 = st in
              {
                repl_line = (uu___214_2196.repl_line);
                repl_column = (uu___214_2196.repl_column);
                repl_fname = (uu___214_2196.repl_fname);
                repl_stack = stack;
                repl_curmod = curmod;
                repl_env = env;
                repl_ts = (uu___214_2196.repl_ts);
                repl_stdin = (uu___214_2196.repl_stdin)
              })))))
let run_push st kind text1 line column1 peek_only =
  let uu____2235 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
  match uu____2235 with
  | (stack,env,ts) ->
      let uu____2248 =
        if (FStar_List.length stack) = (FStar_List.length ts)
        then
          let uu____2271 =
            update_deps st.repl_fname st.repl_curmod stack env ts in
          (true, uu____2271)
        else (false, (stack, env, ts)) in
      (match uu____2248 with
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
             let uu____2318 = FStar_Errors.report_all () in
             FStar_All.pipe_right uu____2318 (FStar_List.map json_of_issue) in
           (FStar_Errors.clear ();
            (let st' =
               let uu___215_2324 = st in
               {
                 repl_line = line;
                 repl_column = column1;
                 repl_fname = (uu___215_2324.repl_fname);
                 repl_stack = stack2;
                 repl_curmod = (uu___215_2324.repl_curmod);
                 repl_env = (uu___215_2324.repl_env);
                 repl_ts = ts1;
                 repl_stdin = (uu___215_2324.repl_stdin)
               } in
             match res with
             | FStar_Pervasives_Native.Some (curmod,env3,nerrs) when
                 (nerrs = (Prims.parse_int "0")) && (peek_only = false) ->
                 let env4 = commit_mark env3 in
                 ((QueryOK, (FStar_Util.JsonList errors)),
                   (FStar_Util.Inl
                      (let uu___216_2353 = st' in
                       {
                         repl_line = (uu___216_2353.repl_line);
                         repl_column = (uu___216_2353.repl_column);
                         repl_fname = (uu___216_2353.repl_fname);
                         repl_stack = (uu___216_2353.repl_stack);
                         repl_curmod = curmod;
                         repl_env = env4;
                         repl_ts = (uu___216_2353.repl_ts);
                         repl_stdin = (uu___216_2353.repl_stdin)
                       })))
             | uu____2354 ->
                 let env3 = reset_mark env_mark in
                 let uu____2365 =
                   run_pop
                     (let uu___217_2372 = st' in
                      {
                        repl_line = (uu___217_2372.repl_line);
                        repl_column = (uu___217_2372.repl_column);
                        repl_fname = (uu___217_2372.repl_fname);
                        repl_stack = (uu___217_2372.repl_stack);
                        repl_curmod = (uu___217_2372.repl_curmod);
                        repl_env = env3;
                        repl_ts = (uu___217_2372.repl_ts);
                        repl_stdin = (uu___217_2372.repl_stdin)
                      }) in
                 (match uu____2365 with
                  | (uu____2379,st'') ->
                      let status = if peek_only then QueryOK else QueryNOK in
                      ((status, (FStar_Util.JsonList errors)), st'')))))
let run_lookup st symbol pos_opt requested_info =
  let uu____2433 = st.repl_env in
  match uu____2433 with
  | (dsenv,tcenv) ->
      let info_of_lid_str lid_str =
        let lid =
          let uu____2453 =
            FStar_List.map FStar_Ident.id_of_text
              (FStar_Util.split lid_str ".") in
          FStar_Ident.lid_of_ids uu____2453 in
        let lid1 =
          let uu____2456 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid in
          FStar_All.pipe_left (FStar_Util.dflt lid) uu____2456 in
        let uu____2459 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
        FStar_All.pipe_right uu____2459
          (FStar_Util.map_option
             (fun uu____2485  ->
                match uu____2485 with
                | ((uu____2495,typ),r) -> ((FStar_Util.Inr lid1), typ, r))) in
      let docs_of_lid lid =
        let uu____2507 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
        FStar_All.pipe_right uu____2507
          (FStar_Util.map_option FStar_Pervasives_Native.fst) in
      let def_of_lid lid =
        let uu____2524 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
        FStar_Util.bind_opt uu____2524
          (fun uu___204_2544  ->
             match uu___204_2544 with
             | (FStar_Util.Inr (se,uu____2556),uu____2557) ->
                 let uu____2572 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Pervasives_Native.Some uu____2572
             | uu____2573 -> FStar_Pervasives_Native.None) in
      let info_at_pos_opt =
        FStar_Util.bind_opt pos_opt
          (fun uu____2598  ->
             match uu____2598 with
             | (file,row,col) ->
                 FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
      let info_opt =
        match info_at_pos_opt with
        | FStar_Pervasives_Native.Some uu____2624 -> info_at_pos_opt
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
                let uu____2680 =
                  FStar_TypeChecker_Normalize.term_to_string tcenv typ in
                FStar_Pervasives_Native.Some uu____2680
              else FStar_Pervasives_Native.None in
            let doc_str =
              match name_or_lid with
              | FStar_Util.Inr lid when
                  FStar_List.mem "documentation" requested_info ->
                  docs_of_lid lid
              | uu____2686 -> FStar_Pervasives_Native.None in
            let def_str =
              match name_or_lid with
              | FStar_Util.Inr lid when
                  FStar_List.mem "definition" requested_info ->
                  def_of_lid lid
              | uu____2693 -> FStar_Pervasives_Native.None in
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
            let uu____2701 = json_of_lookup_result result in
            (QueryOK, uu____2701) in
      (response, (FStar_Util.Inl st))
let run_completions st search_term =
  let uu____2724 = st.repl_env in
  match uu____2724 with
  | (dsenv,tcenv) ->
      let rec measure_anchored_match search_term1 candidate =
        match (search_term1, candidate) with
        | ([],uu____2754) ->
            FStar_Pervasives_Native.Some ([], (Prims.parse_int "0"))
        | (uu____2762,[]) -> FStar_Pervasives_Native.None
        | (hs::ts,hc::tc) ->
            let hc_text = FStar_Ident.text_of_id hc in
            if FStar_Util.starts_with hc_text hs
            then
              (match ts with
               | [] ->
                   FStar_Pervasives_Native.Some
                     (candidate, (FStar_String.length hs))
               | uu____2792 ->
                   let uu____2794 = measure_anchored_match ts tc in
                   FStar_All.pipe_right uu____2794
                     (FStar_Util.map_option
                        (fun uu____2813  ->
                           match uu____2813 with
                           | (matched,len) ->
                               ((hc :: matched),
                                 (((FStar_String.length hc_text) +
                                     (Prims.parse_int "1"))
                                    + len)))))
            else FStar_Pervasives_Native.None in
      let rec locate_match needle candidate =
        let uu____2849 = measure_anchored_match needle candidate in
        match uu____2849 with
        | FStar_Pervasives_Native.Some (matched,n1) ->
            FStar_Pervasives_Native.Some ([], matched, n1)
        | FStar_Pervasives_Native.None  ->
            (match candidate with
             | [] -> FStar_Pervasives_Native.None
             | hc::tc ->
                 let uu____2891 = locate_match needle tc in
                 FStar_All.pipe_right uu____2891
                   (FStar_Util.map_option
                      (fun uu____2920  ->
                         match uu____2920 with
                         | (prefix1,matched,len) ->
                             ((hc :: prefix1), matched, len)))) in
      let str_of_ids ids =
        let uu____2946 = FStar_List.map FStar_Ident.text_of_id ids in
        FStar_Util.concat_l "." uu____2946 in
      let match_lident_against needle lident =
        locate_match needle
          (FStar_List.append lident.FStar_Ident.ns [lident.FStar_Ident.ident]) in
      let shorten_namespace uu____2975 =
        match uu____2975 with
        | (prefix1,matched,match_len) ->
            let naked_match =
              match matched with
              | uu____2993::[] -> true
              | uu____2994 -> false in
            let uu____2996 =
              FStar_ToSyntax_Env.shorten_module_path dsenv prefix1
                naked_match in
            (match uu____2996 with
             | (stripped_ns,shortened) ->
                 let uu____3011 = str_of_ids shortened in
                 let uu____3012 = str_of_ids matched in
                 let uu____3013 = str_of_ids stripped_ns in
                 (uu____3011, uu____3012, uu____3013, match_len)) in
      let prepare_candidate uu____3024 =
        match uu____3024 with
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
                    let uu____3106 =
                      FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                        dsenv lid in
                    FStar_Option.map
                      (fun fqn  ->
                         let uu____3114 =
                           let uu____3116 =
                             FStar_List.map FStar_Ident.id_of_text orig_ns in
                           FStar_List.append uu____3116
                             [fqn.FStar_Ident.ident] in
                         ([], uu____3114, matched_length)) uu____3106
                  else FStar_Pervasives_Native.None)) in
        let case_b_find_matches_in_env uu____3135 =
          let matches =
            FStar_List.filter_map (match_lident_against needle)
              all_lidents_in_env in
          FStar_All.pipe_right matches
            (FStar_List.filter
               (fun uu____3171  ->
                  match uu____3171 with
                  | (ns,id,uu____3179) ->
                      let uu____3184 =
                        let uu____3186 = FStar_Ident.lid_of_ids id in
                        FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                          dsenv uu____3186 in
                      (match uu____3184 with
                       | FStar_Pervasives_Native.None  -> false
                       | FStar_Pervasives_Native.Some l ->
                           let uu____3188 =
                             FStar_Ident.lid_of_ids (FStar_List.append ns id) in
                           FStar_Ident.lid_equals l uu____3188))) in
        let uu____3189 = FStar_Util.prefix needle in
        match uu____3189 with
        | (ns,id) ->
            let matched_ids =
              match ns with
              | [] -> case_b_find_matches_in_env ()
              | uu____3214 ->
                  let l = FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
                  let uu____3217 =
                    FStar_ToSyntax_Env.resolve_module_name dsenv l true in
                  (match uu____3217 with
                   | FStar_Pervasives_Native.None  ->
                       case_b_find_matches_in_env ()
                   | FStar_Pervasives_Native.Some m ->
                       case_a_find_transitive_includes ns m id) in
            FStar_All.pipe_right matched_ids
              (FStar_List.map
                 (fun x  ->
                    let uu____3250 = shorten_namespace x in
                    prepare_candidate uu____3250)) in
      let json_candidates =
        let uu____3257 =
          FStar_Util.sort_with
            (fun uu____3265  ->
               fun uu____3266  ->
                 match (uu____3265, uu____3266) with
                 | ((cd1,ns1,uu____3281),(cd2,ns2,uu____3284)) ->
                     (match FStar_String.compare cd1 cd2 with
                      | _0_40 when _0_40 = (Prims.parse_int "0") ->
                          FStar_String.compare ns1 ns2
                      | n1 -> n1)) matches in
        FStar_List.map
          (fun uu____3295  ->
             match uu____3295 with
             | (candidate,ns,match_len) ->
                 FStar_Util.JsonList
                   [FStar_Util.JsonInt match_len;
                   FStar_Util.JsonStr ns;
                   FStar_Util.JsonStr candidate]) uu____3257 in
      ((QueryOK, (FStar_Util.JsonList json_candidates)), (FStar_Util.Inl st))
let run_compute st term rules =
  let run_and_rewind st1 task =
    let env_mark = mark st1.repl_env in
    let results = task st1 in
    let env = reset_mark env_mark in
    let st' =
      let uu___218_3365 = st1 in
      {
        repl_line = (uu___218_3365.repl_line);
        repl_column = (uu___218_3365.repl_column);
        repl_fname = (uu___218_3365.repl_fname);
        repl_stack = (uu___218_3365.repl_stack);
        repl_curmod = (uu___218_3365.repl_curmod);
        repl_env = env;
        repl_ts = (uu___218_3365.repl_ts);
        repl_stdin = (uu___218_3365.repl_stdin)
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
          ((uu____3397,{ FStar_Syntax_Syntax.lbname = uu____3398;
                         FStar_Syntax_Syntax.lbunivs = uu____3399;
                         FStar_Syntax_Syntax.lbtyp = uu____3400;
                         FStar_Syntax_Syntax.lbeff = uu____3401;
                         FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____3403,uu____3404);
        FStar_Syntax_Syntax.sigrng = uu____3405;
        FStar_Syntax_Syntax.sigquals = uu____3406;
        FStar_Syntax_Syntax.sigmeta = uu____3407;_}::[] ->
        FStar_Pervasives_Native.Some def
    | uu____3426 -> FStar_Pervasives_Native.None in
  let parse1 frag =
    let uu____3436 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
    match uu____3436 with
    | FStar_Util.Inl (FStar_Util.Inr decls,uu____3449) ->
        FStar_Pervasives_Native.Some decls
    | uu____3472 -> FStar_Pervasives_Native.None in
  let desugar dsenv decls =
    let uu____3492 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
    FStar_Pervasives_Native.snd uu____3492 in
  let typecheck tcenv decls =
    let uu____3505 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
    match uu____3505 with | (ses,uu____3513,uu____3514) -> ses in
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
       let uu____3527 = st1.repl_env in
       match uu____3527 with
       | (dsenv,tcenv) ->
           let frag = dummy_let_fragment term in
           (match st1.repl_curmod with
            | FStar_Pervasives_Native.None  ->
                (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
            | uu____3535 ->
                let uu____3536 = parse1 frag in
                (match uu____3536 with
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
                            let uu____3563 =
                              let uu____3564 =
                                FStar_Syntax_Print.term_to_string normalized in
                              FStar_Util.JsonStr uu____3564 in
                            (QueryOK, uu____3563)
                      with
                      | e ->
                          let uu____3569 =
                            let uu____3570 = FStar_Errors.issue_of_exn e in
                            match uu____3570 with
                            | FStar_Pervasives_Native.Some issue ->
                                let uu____3573 =
                                  FStar_Errors.format_issue issue in
                                FStar_Util.JsonStr uu____3573
                            | FStar_Pervasives_Native.None  -> raise e in
                          (QueryNOK, uu____3569)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____3590 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____3602 -> false
let __proj__TypeContainsLid__item___0: search_term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0
let st_cost: search_term' -> Prims.int =
  fun uu___205_3620  ->
    match uu___205_3620 with
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
    let uu____3671 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____3676 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____3671; sc_fvars = uu____3676 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____3694 = FStar_ST.read sc.sc_typ in
      match uu____3694 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____3703 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____3703 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____3719,typ),uu____3721) ->
                typ in
          (FStar_ST.write sc.sc_typ (FStar_Pervasives_Native.Some typ); typ)
let sc_fvars:
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lid FStar_Util.set
  =
  fun tcenv  ->
    fun sc  ->
      let uu____3741 = FStar_ST.read sc.sc_fvars in
      match uu____3741 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____3755 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____3755 in
          (FStar_ST.write sc.sc_fvars (FStar_Pervasives_Native.Some fv); fv)
let json_of_search_result:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json
  =
  fun dsenv  ->
    fun tcenv  ->
      fun sc  ->
        let typ_str =
          let uu____3772 = sc_typ tcenv sc in
          FStar_Syntax_Print.term_to_string uu____3772 in
        let uu____3773 =
          let uu____3777 =
            let uu____3780 =
              let uu____3781 =
                let uu____3782 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____3782.FStar_Ident.str in
              FStar_Util.JsonStr uu____3781 in
            ("lid", uu____3780) in
          [uu____3777; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____3773
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____3794 -> true
    | uu____3795 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____3802 -> uu____3802
let run_search st search_str =
  let uu____3821 = st.repl_env in
  match uu____3821 with
  | (dsenv,tcenv) ->
      let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
      let st_matches candidate term =
        let found =
          match term.st_term with
          | NameContainsStr str ->
              FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
          | TypeContainsLid lid ->
              let uu____3842 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____3842 in
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
              let uu____3870 =
                let uu____3871 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____3871 in
              raise uu____3870
            else
              if beg_quote
              then
                (let uu____3873 = strip_quotes term1 in
                 NameContainsStr uu____3873)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____3876 =
                   FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                     lid in
                 match uu____3876 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____3878 =
                       let uu____3879 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____3879 in
                     raise uu____3878
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____3894 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.strcat (if term.st_negate then "-" else "") uu____3894 in
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
              (fun uu____3930  ->
                 FStar_Options.set_option "print_effect_args"
                   (FStar_Options.Bool true);
                 FStar_List.map (json_of_search_result dsenv tcenv) sorted1) in
          match results with
          | [] ->
              let kwds =
                let uu____3935 = FStar_List.map pprint_one terms in
                FStar_Util.concat_l " " uu____3935 in
              let uu____3937 =
                let uu____3938 =
                  FStar_Util.format1 "No results found for query [%s]" kwds in
                InvalidSearch uu____3938 in
              raise uu____3937
          | uu____3941 -> (QueryOK, (FStar_Util.JsonList js))
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
    fun uu___206_3970  ->
      match uu___206_3970 with
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
    let uu____4008 = let uu____4015 = run_query st in uu____4015 query.qq in
    match uu____4008 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____4045 = let uu____4047 = FStar_ST.read issues in e :: uu____4047 in
    FStar_ST.write issues uu____4045 in
  let count_errors uu____4058 =
    let uu____4059 =
      let uu____4061 = FStar_ST.read issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____4061 in
    FStar_List.length uu____4059 in
  let report1 uu____4072 =
    let uu____4073 = FStar_ST.read issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____4073 in
  let clear1 uu____4081 = FStar_ST.write issues [] in
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
    (let uu____4091 = deps_of_our_file filename in
     match uu____4091 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____4105 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu____4105 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____4121 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____4122 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____4121 uu____4122 in
              let env2 =
                let uu____4126 =
                  FStar_TypeChecker_Env.set_range
                    (FStar_Pervasives_Native.snd env1) initial_range in
                ((FStar_Pervasives_Native.fst env1), uu____4126) in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2 in
              let init_st =
                let uu____4134 = FStar_Util.open_stdin () in
                {
                  repl_line = (Prims.parse_int "1");
                  repl_column = (Prims.parse_int "0");
                  repl_fname = filename;
                  repl_stack = stack;
                  repl_curmod = FStar_Pervasives_Native.None;
                  repl_env = env3;
                  repl_ts = ts;
                  repl_stdin = uu____4134
                } in
              let uu____4135 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ()) in
              if uu____4135
              then
                let uu____4136 =
                  let uu____4137 = FStar_Options.file_list () in
                  FStar_List.hd uu____4137 in
                FStar_SMTEncoding_Solver.with_hints_db uu____4136
                  (fun uu____4139  -> go init_st)
              else go init_st))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    FStar_Errors.set_handler interactive_error_handler;
    (let uu____4147 =
       let uu____4148 = FStar_Options.codegen () in
       FStar_Option.isSome uu____4148 in
     if uu____4147
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (try interactive_mode' filename
     with
     | e -> (FStar_Errors.set_handler FStar_Errors.default_handler; raise e))