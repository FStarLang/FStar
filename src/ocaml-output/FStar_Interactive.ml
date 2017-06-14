open Prims
let tc_one_file:
  Prims.string Prims.list ->
    FStar_Universal.uenv ->
      ((Prims.string option* Prims.string)* (FStar_ToSyntax_Env.env*
        FStar_TypeChecker_Env.env)* Prims.string Prims.list)
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
                  FStar_Universal.tc_one_file dsenv env (Some intf) impl in
                (match uu____51 with
                 | (uu____66,dsenv1,env1) ->
                     (((Some intf), impl), dsenv1, env1, remaining1))
            | intf_or_impl::remaining1 ->
                let uu____83 =
                  FStar_Universal.tc_one_file dsenv env None intf_or_impl in
                (match uu____83 with
                 | (uu____98,dsenv1,env1) ->
                     ((None, intf_or_impl), dsenv1, env1, remaining1))
            | [] -> failwith "Impossible" in
          (match uu____30 with
           | ((intf,impl),dsenv1,env1,remaining1) ->
               ((intf, impl), (dsenv1, env1), remaining1))
let tc_prims:
  Prims.unit -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) =
  fun uu____152  ->
    let uu____153 = FStar_Universal.tc_prims () in
    match uu____153 with | (uu____161,dsenv,env) -> (dsenv, env)
type env_t = (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
type modul_t = FStar_Syntax_Syntax.modul option
type stack_t = (env_t* modul_t) Prims.list
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
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    push_kind ->
      Prims.bool ->
        Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____217  ->
    fun kind  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____217 with
          | (dsenv,tcenv) ->
              let tcenv1 =
                let uu___209_228 = tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___209_228.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___209_228.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___209_228.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___209_228.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___209_228.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___209_228.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___209_228.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___209_228.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___209_228.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___209_228.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___209_228.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___209_228.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___209_228.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___209_228.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___209_228.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___209_228.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___209_228.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___209_228.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = (kind = LaxCheck);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___209_228.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___209_228.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___209_228.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___209_228.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___209_228.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___209_228.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___209_228.FStar_TypeChecker_Env.synth)
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
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
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
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____290  ->
    match uu____290 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.commit_mark dsenv in
        let env1 = FStar_TypeChecker_Env.commit_mark env in (dsenv1, env1)
let check_frag:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    FStar_Syntax_Syntax.modul option ->
      (FStar_Parser_ParseIt.input_frag* Prims.bool) ->
        (FStar_Syntax_Syntax.modul option* (FStar_ToSyntax_Env.env*
          FStar_TypeChecker_Env.env)* Prims.int) option
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
               | Some (m,dsenv1,env1) ->
                   let uu____371 =
                     let uu____378 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____378) in
                   Some uu____371
               | uu____388 -> None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____410 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____410 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
             | FStar_Errors.Err msg when
                 let uu____423 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____423 ->
                 ((let uu____425 =
                     let uu____429 =
                       let uu____432 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____432) in
                     [uu____429] in
                   FStar_TypeChecker_Err.add_errors env uu____425);
                  None))
let deps_of_our_file:
  Prims.string -> (Prims.string Prims.list* Prims.string option) =
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
               Some intf)
          | impl::[] -> None
          | uu____482 ->
              ((let uu____485 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____485);
               None) in
        (deps1, maybe_intf)
type m_timestamps =
  (Prims.string option* Prims.string* FStar_Util.time option*
    FStar_Util.time) Prims.list
let rec tc_deps:
  modul_t ->
    stack_t ->
      env_t ->
        Prims.string Prims.list ->
          m_timestamps -> (stack_t* env_t* m_timestamps)
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
                         | Some intf1 ->
                             let uu____568 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             Some uu____568
                         | None  -> None in
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
      stack_t -> env_t -> m_timestamps -> (stack_t* env_t* m_timestamps)
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
                 | (Some intf1,Some intf_t1) ->
                     let intf_mt =
                       FStar_Util.get_file_last_modification_time intf1 in
                     FStar_Util.is_before intf_t1 intf_mt
                 | (None ,None ) -> false
                 | (uu____634,uu____635) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None") in
            let rec iterate depnames st env' ts1 good_stack good_ts =
              let match_dep depnames1 intf impl =
                match intf with
                | None  ->
                    (match depnames1 with
                     | dep1::depnames' ->
                         if dep1 = impl
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____699 -> (false, depnames1))
                | Some intf1 ->
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
  fun uu___199_980  ->
    match uu___199_980 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____984 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____984
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____986 -> "list (...)"
    | FStar_Util.JsonAssoc uu____988 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string* FStar_Util.json)
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1000 -> true
    | uu____1003 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string* FStar_Util.json) =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1014 -> uu____1014
let js_fail expected got = raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___200_1031  ->
    match uu___200_1031 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___201_1036  ->
    match uu___201_1036 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list k uu___202_1054 =
  match uu___202_1054 with
  | FStar_Util.JsonList l -> FStar_List.map k l
  | other -> js_fail "list" other
let js_assoc: FStar_Util.json -> (Prims.string* FStar_Util.json) Prims.list =
  fun uu___203_1066  ->
    match uu___203_1066 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1081 = js_str s in
    match uu____1081 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1082 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1086 = js_str s in
    match uu____1086 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | uu____1087 -> js_fail "reduction rule" s
type query' =
  | Exit
  | DescribeProtocol
  | DescribeRepl
  | Pop
  | Push of (push_kind* Prims.string* Prims.int* Prims.int* Prims.bool)
  | AutoComplete of Prims.string
  | Lookup of (Prims.string* (Prims.string* Prims.int* Prims.int) option*
  Prims.string Prims.list)
  | Compute of (Prims.string* FStar_TypeChecker_Normalize.step Prims.list
  option)
  | Search of Prims.string
  | ProtocolViolation of Prims.string
and query = {
  qq: query';
  qid: Prims.string;}
let uu___is_Exit: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1140 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1144 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1148 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1152 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1162 -> false
let __proj__Push__item___0:
  query' -> (push_kind* Prims.string* Prims.int* Prims.int* Prims.bool) =
  fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1189 -> false
let __proj__AutoComplete__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____1209 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string* (Prims.string* Prims.int* Prims.int) option* Prims.string
      Prims.list)
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____1249 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string* FStar_TypeChecker_Normalize.step Prims.list option)
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____1273 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____1285 -> false
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
    | InvalidQuery uu____1310 -> true
    | uu____1311 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____1318 -> uu____1318
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____1322 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____1326 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____1330 -> false
let try_assoc key a =
  let uu____1352 =
    FStar_Util.try_find
      (fun uu____1358  -> match uu____1358 with | (k,uu____1362) -> k = key)
      a in
  FStar_Util.map_option FStar_Pervasives.snd uu____1352
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____1374 =
          let uu____1375 =
            let uu____1376 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____1376 in
          ProtocolViolation uu____1375 in
        { qq = uu____1374; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____1396 = try_assoc key a in
      match uu____1396 with
      | Some v1 -> v1
      | None  ->
          let uu____1399 =
            let uu____1400 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____1400 in
          raise uu____1399 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____1409 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____1409 js_str in
    try
      let query =
        let uu____1412 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____1412 js_str in
      let args =
        let uu____1417 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____1417 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____1430 = try_assoc k args in
        match uu____1430 with
        | Some (FStar_Util.JsonNull ) -> None
        | other -> other in
      let uu____1435 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____1436 =
              let uu____1442 =
                let uu____1443 = arg "kind" in
                FStar_All.pipe_right uu____1443 js_pushkind in
              let uu____1444 =
                let uu____1445 = arg "code" in
                FStar_All.pipe_right uu____1445 js_str in
              let uu____1446 =
                let uu____1447 = arg "line" in
                FStar_All.pipe_right uu____1447 js_int in
              let uu____1448 =
                let uu____1449 = arg "column" in
                FStar_All.pipe_right uu____1449 js_int in
              (uu____1442, uu____1444, uu____1446, uu____1448,
                (query = "peek")) in
            Push uu____1436
        | "push" ->
            let uu____1450 =
              let uu____1456 =
                let uu____1457 = arg "kind" in
                FStar_All.pipe_right uu____1457 js_pushkind in
              let uu____1458 =
                let uu____1459 = arg "code" in
                FStar_All.pipe_right uu____1459 js_str in
              let uu____1460 =
                let uu____1461 = arg "line" in
                FStar_All.pipe_right uu____1461 js_int in
              let uu____1462 =
                let uu____1463 = arg "column" in
                FStar_All.pipe_right uu____1463 js_int in
              (uu____1456, uu____1458, uu____1460, uu____1462,
                (query = "peek")) in
            Push uu____1450
        | "autocomplete" ->
            let uu____1464 =
              let uu____1465 = arg "partial-symbol" in
              FStar_All.pipe_right uu____1465 js_str in
            AutoComplete uu____1464
        | "lookup" ->
            let uu____1466 =
              let uu____1475 =
                let uu____1476 = arg "symbol" in
                FStar_All.pipe_right uu____1476 js_str in
              let uu____1477 =
                let uu____1482 =
                  let uu____1487 = try_arg "location" in
                  FStar_All.pipe_right uu____1487
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____1482
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____1515 =
                          let uu____1516 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____1516 js_str in
                        let uu____1517 =
                          let uu____1518 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____1518 js_int in
                        let uu____1519 =
                          let uu____1520 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____1520 js_int in
                        (uu____1515, uu____1517, uu____1519))) in
              let uu____1521 =
                let uu____1523 = arg "requested-info" in
                FStar_All.pipe_right uu____1523 (js_list js_str) in
              (uu____1475, uu____1477, uu____1521) in
            Lookup uu____1466
        | "compute" ->
            let uu____1530 =
              let uu____1535 =
                let uu____1536 = arg "term" in
                FStar_All.pipe_right uu____1536 js_str in
              let uu____1537 =
                let uu____1540 = try_arg "rules" in
                FStar_All.pipe_right uu____1540
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____1535, uu____1537) in
            Compute uu____1530
        | "search" ->
            let uu____1548 =
              let uu____1549 = arg "terms" in
              FStar_All.pipe_right uu____1549 js_str in
            Search uu____1548
        | uu____1550 ->
            let uu____1551 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____1551 in
      { qq = uu____1435; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let validate_interactive_query: query -> query =
  fun uu___204_1558  ->
    match uu___204_1558 with
    | { qq = Push (SyntaxCheck ,uu____1559,uu____1560,uu____1561,false );
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
      let uu____1568 = FStar_Util.read_line stream in
      match uu____1568 with
      | None  -> FStar_All.exit (Prims.parse_int "0")
      | Some line ->
          let uu____1571 = FStar_Util.json_of_string line in
          (match uu____1571 with
           | None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | Some request ->
               let uu____1574 = unpack_interactive_query request in
               validate_interactive_query uu____1574)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let rec json_of_fstar_option: FStar_Options.option_val -> FStar_Util.json =
  fun uu___205_1581  ->
    match uu___205_1581 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____1588 = FStar_List.map json_of_fstar_option vs in
        FStar_Util.JsonList uu____1588
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let json_of_opt json_of_a opt_a =
  let uu____1609 = FStar_Util.map_option json_of_a opt_a in
  FStar_Util.dflt FStar_Util.JsonNull uu____1609
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____1614 =
      let uu____1616 =
        let uu____1617 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____1617 in
      let uu____1618 =
        let uu____1620 =
          let uu____1621 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____1621 in
        [uu____1620] in
      uu____1616 :: uu____1618 in
    FStar_Util.JsonList uu____1614
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____1631 =
          let uu____1635 =
            let uu____1639 =
              let uu____1642 = json_of_pos b in ("beg", uu____1642) in
            let uu____1643 =
              let uu____1647 =
                let uu____1650 = json_of_pos e in ("end", uu____1650) in
              [uu____1647] in
            uu____1639 :: uu____1643 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____1635 in
        FStar_Util.JsonAssoc uu____1631
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____1662 = FStar_Range.file_of_use_range r in
    let uu____1663 = FStar_Range.start_of_use_range r in
    let uu____1664 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____1662 uu____1663 uu____1664
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____1668 = FStar_Range.file_of_range r in
    let uu____1669 = FStar_Range.start_of_range r in
    let uu____1670 = FStar_Range.end_of_range r in
    json_of_range_fields uu____1668 uu____1669 uu____1670
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
    let uu____1677 =
      let uu____1681 =
        let uu____1685 =
          let uu____1689 =
            let uu____1692 =
              let uu____1693 =
                let uu____1695 =
                  match issue.FStar_Errors.issue_range with
                  | None  -> []
                  | Some r ->
                      let uu____1699 = json_of_use_range r in [uu____1699] in
                let uu____1700 =
                  match issue.FStar_Errors.issue_range with
                  | Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____1704 = json_of_def_range r in [uu____1704]
                  | uu____1705 -> [] in
                FStar_List.append uu____1695 uu____1700 in
              FStar_Util.JsonList uu____1693 in
            ("ranges", uu____1692) in
          [uu____1689] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____1685 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____1681 in
    FStar_Util.JsonAssoc uu____1677
type lookup_result =
  {
  lr_name: Prims.string;
  lr_def_range: FStar_Range.range option;
  lr_typ: Prims.string option;
  lr_doc: Prims.string option;
  lr_def: Prims.string option;}
let __proj__Mklookup_result__item__lr_name: lookup_result -> Prims.string =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_name
let __proj__Mklookup_result__item__lr_def_range:
  lookup_result -> FStar_Range.range option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_def_range
let __proj__Mklookup_result__item__lr_typ:
  lookup_result -> Prims.string option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_typ
let __proj__Mklookup_result__item__lr_doc:
  lookup_result -> Prims.string option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_doc
let __proj__Mklookup_result__item__lr_def:
  lookup_result -> Prims.string option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_def
let json_of_lookup_result: lookup_result -> FStar_Util.json =
  fun lr  ->
    let uu____1810 =
      let uu____1814 =
        let uu____1818 =
          let uu____1821 = json_of_opt json_of_def_range lr.lr_def_range in
          ("defined-at", uu____1821) in
        let uu____1822 =
          let uu____1826 =
            let uu____1829 =
              json_of_opt (fun _0_43  -> FStar_Util.JsonStr _0_43) lr.lr_typ in
            ("type", uu____1829) in
          let uu____1830 =
            let uu____1834 =
              let uu____1837 =
                json_of_opt (fun _0_44  -> FStar_Util.JsonStr _0_44)
                  lr.lr_doc in
              ("documentation", uu____1837) in
            let uu____1838 =
              let uu____1842 =
                let uu____1845 =
                  json_of_opt (fun _0_45  -> FStar_Util.JsonStr _0_45)
                    lr.lr_def in
                ("definition", uu____1845) in
              [uu____1842] in
            uu____1834 :: uu____1838 in
          uu____1826 :: uu____1830 in
        uu____1818 :: uu____1822 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____1814 in
    FStar_Util.JsonAssoc uu____1810
let json_of_protocol_info: (Prims.string* FStar_Util.json) Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____1863 =
      FStar_List.map (fun _0_46  -> FStar_Util.JsonStr _0_46)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_47  -> FStar_Util.JsonList _0_47) uu____1863 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____1876 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____1876);
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
  fun uu____1914  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____1917 =
        FStar_List.map (fun _0_48  -> FStar_Util.JsonStr _0_48)
          interactive_protocol_features in
      FStar_Util.JsonList uu____1917 in
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
  repl_state -> (Prims.string* FStar_Util.json) Prims.list =
  fun st  ->
    let opts_and_defaults =
      let opt_docs =
        let uu____2056 = FStar_Options.docs () in
        FStar_Util.smap_of_list uu____2056 in
      let get_doc k = FStar_Util.smap_try_find opt_docs k in
      FStar_List.map
        (fun uu____2072  ->
           match uu____2072 with
           | (k,v1) ->
               let uu____2082 = FStar_Options.get_option k in
               let uu____2083 = get_doc k in (k, uu____2082, uu____2083, v1))
        FStar_Options.defaults in
    let uu____2086 =
      let uu____2089 =
        let uu____2090 =
          FStar_List.map
            (fun uu____2098  ->
               match uu____2098 with
               | (uu____2105,fstname,uu____2107,uu____2108) ->
                   FStar_Util.JsonStr fstname) st.repl_ts in
        FStar_Util.JsonList uu____2090 in
      ("loaded-dependencies", uu____2089) in
    let uu____2113 =
      let uu____2117 =
        let uu____2120 =
          let uu____2121 =
            FStar_List.map
              (fun uu____2128  ->
                 match uu____2128 with
                 | (name,value,doc1,dflt1) ->
                     let uu____2140 =
                       let uu____2144 =
                         let uu____2148 =
                           let uu____2151 = json_of_fstar_option value in
                           ("value", uu____2151) in
                         let uu____2152 =
                           let uu____2156 =
                             let uu____2159 = json_of_fstar_option dflt1 in
                             ("default", uu____2159) in
                           let uu____2160 =
                             let uu____2164 =
                               let uu____2167 =
                                 json_of_opt
                                   (fun _0_49  -> FStar_Util.JsonStr _0_49)
                                   doc1 in
                               ("documentation", uu____2167) in
                             [uu____2164] in
                           uu____2156 :: uu____2160 in
                         uu____2148 :: uu____2152 in
                       ("name", (FStar_Util.JsonStr name)) :: uu____2144 in
                     FStar_Util.JsonAssoc uu____2140) opts_and_defaults in
          FStar_Util.JsonList uu____2121 in
        ("options", uu____2120) in
      [uu____2117] in
    uu____2086 :: uu____2113
let run_exit st =
  ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol st =
  ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
    (FStar_Util.Inl st))
let run_describe_repl st =
  let uu____2235 =
    let uu____2238 =
      let uu____2239 = json_of_repl_state st in
      FStar_Util.JsonAssoc uu____2239 in
    (QueryOK, uu____2238) in
  (uu____2235, (FStar_Util.Inl st))
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
            ((let uu___216_2321 = st in
              {
                repl_line = (uu___216_2321.repl_line);
                repl_column = (uu___216_2321.repl_column);
                repl_fname = (uu___216_2321.repl_fname);
                repl_stack = stack;
                repl_curmod = curmod;
                repl_env = env;
                repl_ts = (uu___216_2321.repl_ts);
                repl_stdin = (uu___216_2321.repl_stdin)
              })))))
let run_push st kind text1 line column1 peek_only =
  let uu____2360 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
  match uu____2360 with
  | (stack,env,ts) ->
      let uu____2373 =
        if (FStar_List.length stack) = (FStar_List.length ts)
        then
          let uu____2400 =
            update_deps st.repl_fname st.repl_curmod stack env ts in
          (true, uu____2400)
        else (false, (stack, env, ts)) in
      (match uu____2373 with
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
             let uu____2447 = FStar_Errors.report_all () in
             FStar_All.pipe_right uu____2447 (FStar_List.map json_of_issue) in
           (FStar_Errors.clear ();
            (let st' =
               let uu___217_2453 = st in
               {
                 repl_line = line;
                 repl_column = column1;
                 repl_fname = (uu___217_2453.repl_fname);
                 repl_stack = stack2;
                 repl_curmod = (uu___217_2453.repl_curmod);
                 repl_env = (uu___217_2453.repl_env);
                 repl_ts = ts1;
                 repl_stdin = (uu___217_2453.repl_stdin)
               } in
             match res with
             | Some (curmod,env3,nerrs) when
                 (nerrs = (Prims.parse_int "0")) && (peek_only = false) ->
                 let env4 = commit_mark env3 in
                 ((QueryOK, (FStar_Util.JsonList errors)),
                   (FStar_Util.Inl
                      (let uu___218_2482 = st' in
                       {
                         repl_line = (uu___218_2482.repl_line);
                         repl_column = (uu___218_2482.repl_column);
                         repl_fname = (uu___218_2482.repl_fname);
                         repl_stack = (uu___218_2482.repl_stack);
                         repl_curmod = curmod;
                         repl_env = env4;
                         repl_ts = (uu___218_2482.repl_ts);
                         repl_stdin = (uu___218_2482.repl_stdin)
                       })))
             | uu____2483 ->
                 let env3 = reset_mark env_mark in
                 let uu____2494 =
                   run_pop
                     (let uu___219_2501 = st' in
                      {
                        repl_line = (uu___219_2501.repl_line);
                        repl_column = (uu___219_2501.repl_column);
                        repl_fname = (uu___219_2501.repl_fname);
                        repl_stack = (uu___219_2501.repl_stack);
                        repl_curmod = (uu___219_2501.repl_curmod);
                        repl_env = env3;
                        repl_ts = (uu___219_2501.repl_ts);
                        repl_stdin = (uu___219_2501.repl_stdin)
                      }) in
                 (match uu____2494 with
                  | (uu____2508,st'') ->
                      let status = if peek_only then QueryOK else QueryNOK in
                      ((status, (FStar_Util.JsonList errors)), st'')))))
let run_lookup st symbol pos_opt requested_info =
  let uu____2562 = st.repl_env in
  match uu____2562 with
  | (dsenv,tcenv) ->
      let info_of_lid_str lid_str =
        let lid =
          let uu____2582 =
            FStar_List.map FStar_Ident.id_of_text
              (FStar_Util.split lid_str ".") in
          FStar_Ident.lid_of_ids uu____2582 in
        let lid1 =
          let uu____2585 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid in
          FStar_All.pipe_left (FStar_Util.dflt lid) uu____2585 in
        let uu____2588 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
        FStar_All.pipe_right uu____2588
          (FStar_Util.map_option
             (fun uu____2614  ->
                match uu____2614 with
                | ((uu____2624,typ),r) -> ((FStar_Util.Inr lid1), typ, r))) in
      let docs_of_lid lid =
        let uu____2636 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
        FStar_All.pipe_right uu____2636
          (FStar_Util.map_option FStar_Pervasives.fst) in
      let def_of_lid lid =
        let uu____2653 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
        FStar_Util.bind_opt uu____2653
          (fun uu___206_2673  ->
             match uu___206_2673 with
             | (FStar_Util.Inr (se,uu____2685),uu____2686) ->
                 let uu____2701 = FStar_Syntax_Print.sigelt_to_string se in
                 Some uu____2701
             | uu____2702 -> None) in
      let info_at_pos_opt =
        FStar_Util.bind_opt pos_opt
          (fun uu____2727  ->
             match uu____2727 with
             | (file,row,col) ->
                 FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
      let info_opt =
        match info_at_pos_opt with
        | Some uu____2753 -> info_at_pos_opt
        | None  -> if symbol = "" then None else info_of_lid_str symbol in
      let response =
        match info_opt with
        | None  -> (QueryNOK, FStar_Util.JsonNull)
        | Some (name_or_lid,typ,rng) ->
            let name =
              match name_or_lid with
              | FStar_Util.Inl name -> name
              | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid in
            let typ_str =
              if FStar_List.mem "type" requested_info
              then
                let uu____2809 =
                  FStar_TypeChecker_Normalize.term_to_string tcenv typ in
                Some uu____2809
              else None in
            let doc_str =
              match name_or_lid with
              | FStar_Util.Inr lid when
                  FStar_List.mem "documentation" requested_info ->
                  docs_of_lid lid
              | uu____2815 -> None in
            let def_str =
              match name_or_lid with
              | FStar_Util.Inr lid when
                  FStar_List.mem "definition" requested_info ->
                  def_of_lid lid
              | uu____2822 -> None in
            let def_range =
              if FStar_List.mem "defined-at" requested_info
              then Some rng
              else None in
            let result =
              {
                lr_name = name;
                lr_def_range = def_range;
                lr_typ = typ_str;
                lr_doc = doc_str;
                lr_def = def_str
              } in
            let uu____2830 = json_of_lookup_result result in
            (QueryOK, uu____2830) in
      (response, (FStar_Util.Inl st))
let run_completions st search_term =
  let uu____2853 = st.repl_env in
  match uu____2853 with
  | (dsenv,tcenv) ->
      let rec measure_anchored_match search_term1 candidate =
        match (search_term1, candidate) with
        | ([],uu____2883) -> Some ([], (Prims.parse_int "0"))
        | (uu____2891,[]) -> None
        | (hs::ts,hc::tc) ->
            let hc_text = FStar_Ident.text_of_id hc in
            if FStar_Util.starts_with hc_text hs
            then
              (match ts with
               | [] -> Some (candidate, (FStar_String.length hs))
               | uu____2923 ->
                   let uu____2925 = measure_anchored_match ts tc in
                   FStar_All.pipe_right uu____2925
                     (FStar_Util.map_option
                        (fun uu____2944  ->
                           match uu____2944 with
                           | (matched,len) ->
                               ((hc :: matched),
                                 (((FStar_String.length hc_text) +
                                     (Prims.parse_int "1"))
                                    + len)))))
            else None in
      let rec locate_match needle candidate =
        let uu____2983 = measure_anchored_match needle candidate in
        match uu____2983 with
        | Some (matched,n1) -> Some ([], matched, n1)
        | None  ->
            (match candidate with
             | [] -> None
             | hc::tc ->
                 let uu____3025 = locate_match needle tc in
                 FStar_All.pipe_right uu____3025
                   (FStar_Util.map_option
                      (fun uu____3054  ->
                         match uu____3054 with
                         | (prefix1,matched,len) ->
                             ((hc :: prefix1), matched, len)))) in
      let str_of_ids ids =
        let uu____3080 = FStar_List.map FStar_Ident.text_of_id ids in
        FStar_Util.concat_l "." uu____3080 in
      let match_lident_against needle lident =
        locate_match needle
          (FStar_List.append lident.FStar_Ident.ns [lident.FStar_Ident.ident]) in
      let shorten_namespace uu____3109 =
        match uu____3109 with
        | (prefix1,matched,match_len) ->
            let naked_match =
              match matched with
              | uu____3127::[] -> true
              | uu____3128 -> false in
            let uu____3130 =
              FStar_ToSyntax_Env.shorten_module_path dsenv prefix1
                naked_match in
            (match uu____3130 with
             | (stripped_ns,shortened) ->
                 let uu____3145 = str_of_ids shortened in
                 let uu____3146 = str_of_ids matched in
                 let uu____3147 = str_of_ids stripped_ns in
                 (uu____3145, uu____3146, uu____3147, match_len)) in
      let prepare_candidate uu____3158 =
        match uu____3158 with
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
                    let uu____3248 =
                      FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                        dsenv lid in
                    FStar_Option.map
                      (fun fqn  ->
                         let uu____3256 =
                           let uu____3258 =
                             FStar_List.map FStar_Ident.id_of_text orig_ns in
                           FStar_List.append uu____3258
                             [fqn.FStar_Ident.ident] in
                         ([], uu____3256, matched_length)) uu____3248
                  else None)) in
        let case_b_find_matches_in_env uu____3277 =
          let matches =
            FStar_List.filter_map (match_lident_against needle)
              all_lidents_in_env in
          FStar_All.pipe_right matches
            (FStar_List.filter
               (fun uu____3313  ->
                  match uu____3313 with
                  | (ns,id,uu____3321) ->
                      let uu____3326 =
                        let uu____3328 = FStar_Ident.lid_of_ids id in
                        FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                          dsenv uu____3328 in
                      (match uu____3326 with
                       | None  -> false
                       | Some l ->
                           let uu____3330 =
                             FStar_Ident.lid_of_ids (FStar_List.append ns id) in
                           FStar_Ident.lid_equals l uu____3330))) in
        let uu____3331 = FStar_Util.prefix needle in
        match uu____3331 with
        | (ns,id) ->
            let matched_ids =
              match ns with
              | [] -> case_b_find_matches_in_env ()
              | uu____3356 ->
                  let l = FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
                  let uu____3359 =
                    FStar_ToSyntax_Env.resolve_module_name dsenv l true in
                  (match uu____3359 with
                   | None  -> case_b_find_matches_in_env ()
                   | Some m -> case_a_find_transitive_includes ns m id) in
            FStar_All.pipe_right matched_ids
              (FStar_List.map
                 (fun x  ->
                    let uu____3392 = shorten_namespace x in
                    prepare_candidate uu____3392)) in
      let json_candidates =
        let uu____3399 =
          FStar_Util.sort_with
            (fun uu____3407  ->
               fun uu____3408  ->
                 match (uu____3407, uu____3408) with
                 | ((cd1,ns1,uu____3423),(cd2,ns2,uu____3426)) ->
                     (match FStar_String.compare cd1 cd2 with
                      | _0_50 when _0_50 = (Prims.parse_int "0") ->
                          FStar_String.compare ns1 ns2
                      | n1 -> n1)) matches in
        FStar_List.map
          (fun uu____3437  ->
             match uu____3437 with
             | (candidate,ns,match_len) ->
                 FStar_Util.JsonList
                   [FStar_Util.JsonInt match_len;
                   FStar_Util.JsonStr ns;
                   FStar_Util.JsonStr candidate]) uu____3399 in
      ((QueryOK, (FStar_Util.JsonList json_candidates)), (FStar_Util.Inl st))
let run_compute st term rules =
  let run_and_rewind st1 task =
    let env_mark = mark st1.repl_env in
    let results = task st1 in
    let env = reset_mark env_mark in
    let st' =
      let uu___220_3507 = st1 in
      {
        repl_line = (uu___220_3507.repl_line);
        repl_column = (uu___220_3507.repl_column);
        repl_fname = (uu___220_3507.repl_fname);
        repl_stack = (uu___220_3507.repl_stack);
        repl_curmod = (uu___220_3507.repl_curmod);
        repl_env = env;
        repl_ts = (uu___220_3507.repl_ts);
        repl_stdin = (uu___220_3507.repl_stdin)
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
          ((uu____3539,{ FStar_Syntax_Syntax.lbname = uu____3540;
                         FStar_Syntax_Syntax.lbunivs = uu____3541;
                         FStar_Syntax_Syntax.lbtyp = uu____3542;
                         FStar_Syntax_Syntax.lbeff = uu____3543;
                         FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____3545,uu____3546);
        FStar_Syntax_Syntax.sigrng = uu____3547;
        FStar_Syntax_Syntax.sigquals = uu____3548;
        FStar_Syntax_Syntax.sigmeta = uu____3549;_}::[] -> Some def
    | uu____3568 -> None in
  let parse1 frag =
    let uu____3578 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
    match uu____3578 with
    | FStar_Util.Inl (FStar_Util.Inr decls,uu____3591) -> Some decls
    | uu____3614 -> None in
  let desugar dsenv decls =
    let uu____3634 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
    snd uu____3634 in
  let typecheck tcenv decls =
    let uu____3647 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
    match uu____3647 with | (ses,uu____3655,uu____3656) -> ses in
  let rules1 =
    FStar_List.append
      (match rules with
       | Some rules1 -> rules1
       | None  ->
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
       let uu____3669 = st1.repl_env in
       match uu____3669 with
       | (dsenv,tcenv) ->
           let frag = dummy_let_fragment term in
           (match st1.repl_curmod with
            | None  ->
                (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
            | uu____3677 ->
                let uu____3678 = parse1 frag in
                (match uu____3678 with
                 | None  ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Count not parse this term"))
                 | Some decls ->
                     (try
                        let decls1 = desugar dsenv decls in
                        let ses = typecheck tcenv decls1 in
                        match find_let_body ses with
                        | None  ->
                            (QueryNOK,
                              (FStar_Util.JsonStr
                                 "Typechecking yielded an unexpected term"))
                        | Some def ->
                            let normalized = normalize_term1 tcenv rules1 def in
                            let uu____3705 =
                              let uu____3706 =
                                FStar_Syntax_Print.term_to_string normalized in
                              FStar_Util.JsonStr uu____3706 in
                            (QueryOK, uu____3705)
                      with
                      | e ->
                          let uu____3711 =
                            let uu____3712 = FStar_Errors.issue_of_exn e in
                            match uu____3712 with
                            | Some issue ->
                                let uu____3715 =
                                  FStar_Errors.format_issue issue in
                                FStar_Util.JsonStr uu____3715
                            | None  -> raise e in
                          (QueryNOK, uu____3711)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____3736 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____3748 -> false
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
  fun uu___207_3768  ->
    match uu___207_3768 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> Prims.parse_int "1"
type search_candidate =
  {
  sc_lid: FStar_Ident.lid;
  sc_typ: FStar_Syntax_Syntax.typ option FStar_ST.ref;
  sc_fvars: FStar_Ident.lid FStar_Util.set option FStar_ST.ref;}
let __proj__Mksearch_candidate__item__sc_lid:
  search_candidate -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_lid
let __proj__Mksearch_candidate__item__sc_typ:
  search_candidate -> FStar_Syntax_Syntax.typ option FStar_ST.ref =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_typ
let __proj__Mksearch_candidate__item__sc_fvars:
  search_candidate -> FStar_Ident.lid FStar_Util.set option FStar_ST.ref =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_fvars
let sc_of_lid: FStar_Ident.lid -> search_candidate =
  fun lid  ->
    let uu____3848 = FStar_Util.mk_ref None in
    let uu____3853 = FStar_Util.mk_ref None in
    { sc_lid = lid; sc_typ = uu____3848; sc_fvars = uu____3853 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____3871 = FStar_ST.read sc.sc_typ in
      match uu____3871 with
      | Some t -> t
      | None  ->
          let typ =
            let uu____3880 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____3880 with
            | None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                  FStar_Range.dummyRange
            | Some ((uu____3896,typ),uu____3898) -> typ in
          (FStar_ST.write sc.sc_typ (Some typ); typ)
let sc_fvars:
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lid FStar_Util.set
  =
  fun tcenv  ->
    fun sc  ->
      let uu____3918 = FStar_ST.read sc.sc_fvars in
      match uu____3918 with
      | Some fv -> fv
      | None  ->
          let fv =
            let uu____3932 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____3932 in
          (FStar_ST.write sc.sc_fvars (Some fv); fv)
let json_of_search_result:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json
  =
  fun dsenv  ->
    fun tcenv  ->
      fun sc  ->
        let typ_str =
          let uu____3949 = sc_typ tcenv sc in
          FStar_Syntax_Print.term_to_string uu____3949 in
        let uu____3950 =
          let uu____3954 =
            let uu____3957 =
              let uu____3958 =
                let uu____3959 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____3959.FStar_Ident.str in
              FStar_Util.JsonStr uu____3958 in
            ("lid", uu____3957) in
          [uu____3954; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____3950
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____3972 -> true
    | uu____3973 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____3980 -> uu____3980
let run_search st search_str =
  let uu____3999 = st.repl_env in
  match uu____3999 with
  | (dsenv,tcenv) ->
      let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
      let st_matches candidate term =
        let found =
          match term.st_term with
          | NameContainsStr str ->
              FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
          | TypeContainsLid lid ->
              let uu____4020 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____4020 in
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
              let uu____4054 =
                let uu____4055 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____4055 in
              raise uu____4054
            else
              if beg_quote
              then
                (let uu____4057 = strip_quotes term1 in
                 NameContainsStr uu____4057)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____4060 =
                   FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                     lid in
                 match uu____4060 with
                 | None  ->
                     let uu____4062 =
                       let uu____4063 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____4063 in
                     raise uu____4062
                 | Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____4078 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.strcat (if term.st_negate then "-" else "") uu____4078 in
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
              (fun uu____4114  ->
                 FStar_Options.set_option "print_effect_args"
                   (FStar_Options.Bool true);
                 FStar_List.map (json_of_search_result dsenv tcenv) sorted1) in
          match results with
          | [] ->
              let kwds =
                let uu____4119 = FStar_List.map pprint_one terms in
                FStar_Util.concat_l " " uu____4119 in
              let uu____4121 =
                let uu____4122 =
                  FStar_Util.format1 "No results found for query [%s]" kwds in
                InvalidSearch uu____4122 in
              raise uu____4121
          | uu____4125 -> (QueryOK, (FStar_Util.JsonList js))
        with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s)) in
      (results, (FStar_Util.Inl st))
let run_query:
  repl_state ->
    query' ->
      ((query_status* FStar_Util.json)* (repl_state,Prims.int)
        FStar_Util.either)
  =
  fun st  ->
    fun uu___208_4154  ->
      match uu___208_4154 with
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
    let uu____4192 = let uu____4199 = run_query st in uu____4199 query.qq in
    match uu____4192 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____4229 = let uu____4231 = FStar_ST.read issues in e :: uu____4231 in
    FStar_ST.write issues uu____4229 in
  let count_errors uu____4242 =
    let uu____4243 =
      let uu____4245 = FStar_ST.read issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____4245 in
    FStar_List.length uu____4243 in
  let report1 uu____4257 =
    let uu____4258 = FStar_ST.read issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____4258 in
  let clear1 uu____4266 = FStar_ST.write issues [] in
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
    (let uu____4278 = deps_of_our_file filename in
     match uu____4278 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____4292 = tc_deps None [] env filenames [] in
         (match uu____4292 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____4308 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____4309 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____4308 uu____4309 in
              let env2 =
                let uu____4313 =
                  FStar_TypeChecker_Env.set_range (snd env1) initial_range in
                ((fst env1), uu____4313) in
              let env3 =
                match maybe_intf with
                | Some intf -> FStar_Universal.load_interface_decls env2 intf
                | None  -> env2 in
              let init_st =
                let uu____4321 = FStar_Util.open_stdin () in
                {
                  repl_line = (Prims.parse_int "1");
                  repl_column = (Prims.parse_int "0");
                  repl_fname = filename;
                  repl_stack = stack;
                  repl_curmod = None;
                  repl_env = env3;
                  repl_ts = ts;
                  repl_stdin = uu____4321
                } in
              let uu____4322 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ()) in
              if uu____4322
              then
                let uu____4323 =
                  let uu____4324 = FStar_Options.file_list () in
                  FStar_List.hd uu____4324 in
                FStar_SMTEncoding_Solver.with_hints_db uu____4323
                  (fun uu____4326  -> go init_st)
              else go init_st))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    FStar_Errors.set_handler interactive_error_handler;
    (let uu____4334 =
       let uu____4335 = FStar_Options.codegen () in
       FStar_Option.isSome uu____4335 in
     if uu____4334
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (try interactive_mode' filename
     with
     | e -> (FStar_Errors.set_handler FStar_Errors.default_handler; raise e))