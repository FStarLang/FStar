open Prims
let tc_one_file remaining uenv =
  let uu____26 = uenv in
  match uu____26 with
  | (dsenv,env) ->
      let uu____40 =
        match remaining with
        | intf::impl::remaining1 when
            FStar_Universal.needs_interleaving intf impl ->
            let uu____61 =
              FStar_Universal.tc_one_file_and_intf (Some intf) impl dsenv env in
            (match uu____61 with
             | (uu____76,dsenv1,env1) ->
                 (((Some intf), impl), dsenv1, env1, remaining1))
        | intf_or_impl::remaining1 ->
            let uu____93 =
              FStar_Universal.tc_one_file_and_intf None intf_or_impl dsenv
                env in
            (match uu____93 with
             | (uu____108,dsenv1,env1) ->
                 ((None, intf_or_impl), dsenv1, env1, remaining1))
        | [] -> failwith "Impossible" in
      (match uu____40 with
       | ((intf,impl),dsenv1,env1,remaining1) ->
           ((intf, impl), (dsenv1, env1), None, remaining1))
let tc_prims:
  Prims.unit -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) =
  fun uu____165  ->
    let uu____166 = FStar_Universal.tc_prims () in
    match uu____166 with | (uu____174,dsenv,env) -> (dsenv, env)
type env_t = (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
type modul_t = FStar_Syntax_Syntax.modul Prims.option
type stack_t = (env_t* modul_t) Prims.list
let pop uu____199 msg =
  match uu____199 with
  | (uu____203,env) ->
      (FStar_Universal.pop_context env msg; FStar_Options.pop ())
let push:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    Prims.bool ->
      Prims.bool ->
        Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____218  ->
    fun lax1  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____218 with
          | (dsenv,env) ->
              let env1 =
                let uu___229_229 = env in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___229_229.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___229_229.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___229_229.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___229_229.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___229_229.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___229_229.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___229_229.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___229_229.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___229_229.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___229_229.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___229_229.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___229_229.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___229_229.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___229_229.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___229_229.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___229_229.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___229_229.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___229_229.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = lax1;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___229_229.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___229_229.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___229_229.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___229_229.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___229_229.FStar_TypeChecker_Env.qname_and_index)
                } in
              let res = FStar_Universal.push_context (dsenv, env1) msg in
              (FStar_Options.push ();
               if restore_cmd_line_options1
               then
                 (let uu____235 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____235 Prims.ignore)
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
    FStar_Syntax_Syntax.modul Prims.option ->
      (FStar_Parser_ParseIt.input_frag* Prims.bool) ->
        (FStar_Syntax_Syntax.modul Prims.option* (FStar_ToSyntax_Env.env*
          FStar_TypeChecker_Env.env)* Prims.int) Prims.option
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
  Prims.string -> (Prims.string Prims.list* Prims.string Prims.option) =
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
  (Prims.string Prims.option* Prims.string* FStar_Util.time Prims.option*
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
                  let uu____529 = FStar_Options.lax () in
                  push env uu____529 true "typecheck_modul" in
                let uu____530 = tc_one_file remaining env1 in
                (match uu____530 with
                 | ((intf,impl),env2,modl,remaining1) ->
                     let uu____563 =
                       let intf_t =
                         match intf with
                         | Some intf1 ->
                             let uu____571 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             Some uu____571
                         | None  -> None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____563 with
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
                 | (uu____637,uu____638) ->
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
                     | uu____702 -> (false, depnames1))
                | Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____719 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____766::ts3 ->
                    (pop env1 "";
                     (let uu____788 =
                        let uu____796 = FStar_List.hd stack in
                        let uu____801 = FStar_List.tl stack in
                        (uu____796, uu____801) in
                      match uu____788 with
                      | ((env2,uu____815),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____849 = ts_elt in
                  (match uu____849 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____867 = match_dep depnames intf impl in
                       (match uu____867 with
                        | (b,depnames') ->
                            let uu____878 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____878
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____890 =
                                 let uu____898 = FStar_List.hd st in
                                 let uu____903 = FStar_List.tl st in
                                 (uu____898, uu____903) in
                               match uu____890 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____943 = deps_of_our_file filename in
            match uu____943 with
            | (filenames,uu____952) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___223_983  ->
    match uu___223_983 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____987 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____987
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____989 -> "list (...)"
    | FStar_Util.JsonAssoc uu____991 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string* FStar_Util.json)
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1002 -> true
    | uu____1005 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string* FStar_Util.json) =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1016 -> uu____1016
let js_fail expected got = Prims.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___224_1033  ->
    match uu___224_1033 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___225_1038  ->
    match uu___225_1038 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list: FStar_Util.json -> FStar_Util.json Prims.list =
  fun uu___226_1044  ->
    match uu___226_1044 with
    | FStar_Util.JsonList l -> l
    | other -> js_fail "list" other
let js_assoc: FStar_Util.json -> (Prims.string* FStar_Util.json) Prims.list =
  fun uu___227_1055  ->
    match uu___227_1055 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
type push_kind =
  | PushLax
  | PushFull
let uu___is_PushLax: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | PushLax  -> true | uu____1070 -> false
let uu___is_PushFull: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | PushFull  -> true | uu____1074 -> false
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1078 = js_str s in
    match uu____1078 with
    | "lax" -> PushLax
    | "full" -> PushFull
    | uu____1079 -> js_fail "push_kind" s
type query' =
  | Exit
  | DescribeProtocol
  | Pop
  | Push of (push_kind* Prims.string* Prims.int* Prims.int)
  | AutoComplete of Prims.string
  | Lookup of (Prims.string* (Prims.string* Prims.int* Prims.int)
  Prims.option* Prims.string Prims.list)
  | ProtocolViolation of Prims.string
and query = {
  qq: query';
  qid: Prims.string;}
let uu___is_Exit: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1113 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1117 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1121 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1130 -> false
let __proj__Push__item___0:
  query' -> (push_kind* Prims.string* Prims.int* Prims.int) =
  fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1154 -> false
let __proj__AutoComplete__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____1174 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string* (Prims.string* Prims.int* Prims.int) Prims.option*
      Prims.string Prims.list)
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____1210 -> false
let __proj__ProtocolViolation__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0
let interactive_protocol_vernum: Prims.int = Prims.parse_int "1"
let interactive_protocol_features: Prims.string Prims.list =
  ["autocomplete";
  "describe-protocol";
  "exit";
  "lookup";
  "lookup/documentation";
  "pop";
  "push"]
exception InvalidQuery of Prims.string
let uu___is_InvalidQuery: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____1232 -> true
    | uu____1233 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____1240 -> uu____1240
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____1244 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____1248 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____1252 -> false
let try_assoc key a =
  let uu____1274 =
    FStar_Util.try_find
      (fun uu____1280  -> match uu____1280 with | (k,uu____1284) -> k = key)
      a in
  FStar_Util.map_option Prims.snd uu____1274
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____1306 = try_assoc key a in
      match uu____1306 with
      | Some v1 -> v1
      | None  ->
          let uu____1309 =
            let uu____1310 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____1310 in
          Prims.raise uu____1309 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____1319 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____1319 js_str in
    let query =
      let uu____1321 = assoc1 "query" "query" request in
      FStar_All.pipe_right uu____1321 js_str in
    let args =
      let uu____1326 = assoc1 "query" "args" request in
      FStar_All.pipe_right uu____1326 js_assoc in
    let arg k = assoc1 "[args]" k args in
    let try_arg k = try_assoc k args in
    let uu____1339 =
      match query with
      | "exit" -> Exit
      | "pop" -> Pop
      | "describe-protocol" -> DescribeProtocol
      | "push" ->
          let uu____1340 =
            let uu____1345 =
              let uu____1346 = arg "kind" in
              FStar_All.pipe_right uu____1346 js_pushkind in
            let uu____1347 =
              let uu____1348 = arg "code" in
              FStar_All.pipe_right uu____1348 js_str in
            let uu____1349 =
              let uu____1350 = arg "line" in
              FStar_All.pipe_right uu____1350 js_int in
            let uu____1351 =
              let uu____1352 = arg "column" in
              FStar_All.pipe_right uu____1352 js_int in
            (uu____1345, uu____1347, uu____1349, uu____1351) in
          Push uu____1340
      | "autocomplete" ->
          let uu____1353 =
            let uu____1354 = arg "partial-symbol" in
            FStar_All.pipe_right uu____1354 js_str in
          AutoComplete uu____1353
      | "lookup" ->
          let uu____1355 =
            let uu____1364 =
              let uu____1365 = arg "symbol" in
              FStar_All.pipe_right uu____1365 js_str in
            let uu____1366 =
              let uu____1371 =
                let uu____1376 = try_arg "location" in
                FStar_All.pipe_right uu____1376
                  (FStar_Util.map_option js_assoc) in
              FStar_All.pipe_right uu____1371
                (FStar_Util.map_option
                   (fun loc  ->
                      let uu____1404 =
                        let uu____1405 = assoc1 "[location]" "filename" loc in
                        FStar_All.pipe_right uu____1405 js_str in
                      let uu____1406 =
                        let uu____1407 = assoc1 "[location]" "line" loc in
                        FStar_All.pipe_right uu____1407 js_int in
                      let uu____1408 =
                        let uu____1409 = assoc1 "[location]" "column" loc in
                        FStar_All.pipe_right uu____1409 js_int in
                      (uu____1404, uu____1406, uu____1408))) in
            let uu____1410 =
              let uu____1412 =
                let uu____1414 = arg "requested-info" in
                FStar_All.pipe_right uu____1414 js_list in
              FStar_List.map js_str uu____1412 in
            (uu____1364, uu____1366, uu____1410) in
          Lookup uu____1355
      | uu____1421 ->
          let uu____1422 = FStar_Util.format1 "Unknown query '%s'" query in
          ProtocolViolation uu____1422 in
    { qq = uu____1339; qid }
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____1427 = FStar_Util.read_line stream in
      match uu____1427 with
      | None  -> FStar_All.exit (Prims.parse_int "0")
      | Some line ->
          let uu____1430 = FStar_Util.json_of_string line in
          (match uu____1430 with
           | None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | Some request -> unpack_interactive_query request)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) ->
        let uu____1437 =
          let uu____1438 =
            let uu____1439 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____1439 in
          ProtocolViolation uu____1438 in
        { qq = uu____1437; qid = "?" }
let json_of_opt json_of_a opt_a =
  let uu____1459 = FStar_Util.map_option json_of_a opt_a in
  FStar_Util.dflt FStar_Util.JsonNull uu____1459
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____1464 =
      let uu____1466 =
        let uu____1467 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____1467 in
      let uu____1468 =
        let uu____1470 =
          let uu____1471 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____1471 in
        [uu____1470] in
      uu____1466 :: uu____1468 in
    FStar_Util.JsonList uu____1464
let json_of_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____1475 =
      let uu____1479 =
        let uu____1482 =
          let uu____1483 = FStar_Range.file_of_range r in
          FStar_Util.JsonStr uu____1483 in
        ("fname", uu____1482) in
      let uu____1484 =
        let uu____1488 =
          let uu____1491 =
            let uu____1492 = FStar_Range.start_of_range r in
            json_of_pos uu____1492 in
          ("beg", uu____1491) in
        let uu____1493 =
          let uu____1497 =
            let uu____1500 =
              let uu____1501 = FStar_Range.end_of_range r in
              json_of_pos uu____1501 in
            ("end", uu____1500) in
          [uu____1497] in
        uu____1488 :: uu____1493 in
      uu____1479 :: uu____1484 in
    FStar_Util.JsonAssoc uu____1475
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
    let uu____1516 =
      let uu____1520 =
        let uu____1524 =
          let uu____1528 =
            let uu____1531 =
              let uu____1532 =
                match issue.FStar_Errors.issue_range with
                | None  -> []
                | Some r -> let uu____1536 = json_of_range r in [uu____1536] in
              FStar_Util.JsonList uu____1532 in
            ("ranges", uu____1531) in
          [uu____1528] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____1524 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____1520 in
    FStar_Util.JsonAssoc uu____1516
type lookup_result =
  {
  lr_name: Prims.string;
  lr_def_range: FStar_Range.range Prims.option;
  lr_typ: Prims.string Prims.option;
  lr_doc: Prims.string Prims.option;}
let json_of_lookup_result: lookup_result -> FStar_Util.json =
  fun lr  ->
    let uu____1585 =
      let uu____1589 =
        let uu____1593 =
          let uu____1596 = json_of_opt json_of_range lr.lr_def_range in
          ("defined-at", uu____1596) in
        let uu____1597 =
          let uu____1601 =
            let uu____1604 =
              json_of_opt (fun _0_32  -> FStar_Util.JsonStr _0_32) lr.lr_typ in
            ("type", uu____1604) in
          let uu____1605 =
            let uu____1609 =
              let uu____1612 =
                json_of_opt (fun _0_33  -> FStar_Util.JsonStr _0_33)
                  lr.lr_doc in
              ("documentation", uu____1612) in
            [uu____1609] in
          uu____1601 :: uu____1605 in
        uu____1593 :: uu____1597 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____1589 in
    FStar_Util.JsonAssoc uu____1585
let json_of_protocol_info: (Prims.string* FStar_Util.json) Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____1628 =
      FStar_List.map (fun _0_34  -> FStar_Util.JsonStr _0_34)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_35  -> FStar_Util.JsonList _0_35) uu____1628 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____1641 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____1641);
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
  fun uu____1679  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____1682 =
        FStar_List.map (fun _0_36  -> FStar_Util.JsonStr _0_36)
          interactive_protocol_features in
      FStar_Util.JsonList uu____1682 in
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
let run_exit st =
  ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol st =
  ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
    (FStar_Util.Inl st))
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
            ((let uu___234_1850 = st in
              {
                repl_line = (uu___234_1850.repl_line);
                repl_column = (uu___234_1850.repl_column);
                repl_fname = (uu___234_1850.repl_fname);
                repl_stack = stack;
                repl_curmod = curmod;
                repl_env = env;
                repl_ts = (uu___234_1850.repl_ts);
                repl_stdin = (uu___234_1850.repl_stdin)
              })))))
let run_push st kind text1 line column1 =
  let uu____1884 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
  match uu____1884 with
  | (stack,env,ts) ->
      let uu____1897 =
        if (FStar_List.length stack) = (FStar_List.length ts)
        then
          let uu____1920 =
            update_deps st.repl_fname st.repl_curmod stack env ts in
          (true, uu____1920)
        else (false, (stack, env, ts)) in
      (match uu____1897 with
       | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
           let stack2 = (env1, (st.repl_curmod)) :: stack1 in
           let env2 =
             push env1 (kind = PushLax) restore_cmd_line_options1 "#push" in
           let env_mark = mark env2 in
           let frag =
             {
               FStar_Parser_ParseIt.frag_text = text1;
               FStar_Parser_ParseIt.frag_line = line;
               FStar_Parser_ParseIt.frag_col = column1
             } in
           let res = check_frag env_mark st.repl_curmod (frag, false) in
           let errors =
             let uu____1967 = FStar_Errors.report_all () in
             FStar_All.pipe_right uu____1967 (FStar_List.map json_of_issue) in
           (FStar_Errors.clear ();
            (let st' =
               let uu___235_1973 = st in
               {
                 repl_line = line;
                 repl_column = column1;
                 repl_fname = (uu___235_1973.repl_fname);
                 repl_stack = stack2;
                 repl_curmod = (uu___235_1973.repl_curmod);
                 repl_env = (uu___235_1973.repl_env);
                 repl_ts = ts1;
                 repl_stdin = (uu___235_1973.repl_stdin)
               } in
             match res with
             | Some (curmod,env3,nerrs) when nerrs = (Prims.parse_int "0") ->
                 let env4 = commit_mark env3 in
                 ((QueryOK, (FStar_Util.JsonList errors)),
                   (FStar_Util.Inl
                      (let uu___236_2002 = st' in
                       {
                         repl_line = (uu___236_2002.repl_line);
                         repl_column = (uu___236_2002.repl_column);
                         repl_fname = (uu___236_2002.repl_fname);
                         repl_stack = (uu___236_2002.repl_stack);
                         repl_curmod = curmod;
                         repl_env = env4;
                         repl_ts = (uu___236_2002.repl_ts);
                         repl_stdin = (uu___236_2002.repl_stdin)
                       })))
             | uu____2003 ->
                 let env3 = reset_mark env_mark in
                 let uu____2014 =
                   run_pop
                     (let uu___237_2021 = st' in
                      {
                        repl_line = (uu___237_2021.repl_line);
                        repl_column = (uu___237_2021.repl_column);
                        repl_fname = (uu___237_2021.repl_fname);
                        repl_stack = (uu___237_2021.repl_stack);
                        repl_curmod = (uu___237_2021.repl_curmod);
                        repl_env = env3;
                        repl_ts = (uu___237_2021.repl_ts);
                        repl_stdin = (uu___237_2021.repl_stdin)
                      }) in
                 (match uu____2014 with
                  | (uu____2028,st'') ->
                      ((QueryNOK, (FStar_Util.JsonList errors)), st'')))))
let run_lookup st symbol pos_opt requested_info =
  let uu____2080 = st.repl_env in
  match uu____2080 with
  | (dsenv,tcenv) ->
      let info_of_lid_str lid_str =
        let lid =
          let uu____2100 =
            FStar_List.map FStar_Ident.id_of_text
              (FStar_Util.split lid_str ".") in
          FStar_Ident.lid_of_ids uu____2100 in
        let lid1 =
          let uu____2103 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid in
          FStar_All.pipe_left (FStar_Util.dflt lid) uu____2103 in
        let uu____2106 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
        FStar_All.pipe_right uu____2106
          (FStar_Util.map_option
             (fun uu____2132  ->
                match uu____2132 with
                | ((uu____2142,typ),r) -> ((FStar_Util.Inr lid1), typ, r))) in
      let docs_of_lid lid =
        let uu____2154 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
        FStar_All.pipe_right uu____2154 (FStar_Util.map_option Prims.fst) in
      let info_at_pos_opt =
        FStar_Util.bind_opt pos_opt
          (fun uu____2181  ->
             match uu____2181 with
             | (file,row,col) ->
                 FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
      let info_opt =
        match info_at_pos_opt with
        | Some uu____2207 -> info_at_pos_opt
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
                let uu____2263 =
                  FStar_TypeChecker_Normalize.term_to_string tcenv typ in
                Some uu____2263
              else None in
            let doc_str =
              match name_or_lid with
              | FStar_Util.Inr lid when
                  FStar_List.mem "documentation" requested_info ->
                  docs_of_lid lid
              | uu____2269 -> None in
            let def_range =
              if FStar_List.mem "defined-at" requested_info
              then Some rng
              else None in
            let result =
              {
                lr_name = name;
                lr_def_range = def_range;
                lr_typ = typ_str;
                lr_doc = doc_str
              } in
            let uu____2277 = json_of_lookup_result result in
            (QueryOK, uu____2277) in
      (response, (FStar_Util.Inl st))
let run_completions st search_term =
  let uu____2300 = st.repl_env in
  match uu____2300 with
  | (dsenv,tcenv) ->
      let rec measure_anchored_match search_term1 candidate =
        match (search_term1, candidate) with
        | ([],uu____2330) -> Some ([], (Prims.parse_int "0"))
        | (uu____2338,[]) -> None
        | (hs::ts,hc::tc) ->
            let hc_text = FStar_Ident.text_of_id hc in
            if FStar_Util.starts_with hc_text hs
            then
              (match ts with
               | [] -> Some (candidate, (FStar_String.length hs))
               | uu____2368 ->
                   let uu____2370 = measure_anchored_match ts tc in
                   FStar_All.pipe_right uu____2370
                     (FStar_Util.map_option
                        (fun uu____2389  ->
                           match uu____2389 with
                           | (matched,len) ->
                               ((hc :: matched),
                                 (((FStar_String.length hc_text) +
                                     (Prims.parse_int "1"))
                                    + len)))))
            else None in
      let rec locate_match needle candidate =
        let uu____2425 = measure_anchored_match needle candidate in
        match uu____2425 with
        | Some (matched,n1) -> Some ([], matched, n1)
        | None  ->
            (match candidate with
             | [] -> None
             | hc::tc ->
                 let uu____2467 = locate_match needle tc in
                 FStar_All.pipe_right uu____2467
                   (FStar_Util.map_option
                      (fun uu____2496  ->
                         match uu____2496 with
                         | (prefix1,matched,len) ->
                             ((hc :: prefix1), matched, len)))) in
      let str_of_ids ids =
        let uu____2522 = FStar_List.map FStar_Ident.text_of_id ids in
        FStar_Util.concat_l "." uu____2522 in
      let match_lident_against needle lident =
        locate_match needle
          (FStar_List.append lident.FStar_Ident.ns [lident.FStar_Ident.ident]) in
      let shorten_namespace uu____2551 =
        match uu____2551 with
        | (prefix1,matched,match_len) ->
            let naked_match =
              match matched with
              | uu____2569::[] -> true
              | uu____2570 -> false in
            let uu____2572 =
              FStar_ToSyntax_Env.shorten_module_path dsenv prefix1
                naked_match in
            (match uu____2572 with
             | (stripped_ns,shortened) ->
                 let uu____2587 = str_of_ids shortened in
                 let uu____2588 = str_of_ids matched in
                 let uu____2589 = str_of_ids stripped_ns in
                 (uu____2587, uu____2588, uu____2589, match_len)) in
      let prepare_candidate uu____2600 =
        match uu____2600 with
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
                    let uu____2682 =
                      FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                        dsenv lid in
                    FStar_Option.map
                      (fun fqn  ->
                         let uu____2690 =
                           let uu____2692 =
                             FStar_List.map FStar_Ident.id_of_text orig_ns in
                           FStar_List.append uu____2692
                             [fqn.FStar_Ident.ident] in
                         ([], uu____2690, matched_length)) uu____2682
                  else None)) in
        let case_b_find_matches_in_env uu____2711 =
          let matches =
            FStar_List.filter_map (match_lident_against needle)
              all_lidents_in_env in
          FStar_All.pipe_right matches
            (FStar_List.filter
               (fun uu____2747  ->
                  match uu____2747 with
                  | (ns,id,uu____2755) ->
                      let uu____2760 =
                        let uu____2762 = FStar_Ident.lid_of_ids id in
                        FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                          dsenv uu____2762 in
                      (match uu____2760 with
                       | None  -> false
                       | Some l ->
                           let uu____2764 =
                             FStar_Ident.lid_of_ids (FStar_List.append ns id) in
                           FStar_Ident.lid_equals l uu____2764))) in
        let uu____2765 = FStar_Util.prefix needle in
        match uu____2765 with
        | (ns,id) ->
            let matched_ids =
              match ns with
              | [] -> case_b_find_matches_in_env ()
              | uu____2790 ->
                  let l = FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
                  let uu____2793 =
                    FStar_ToSyntax_Env.resolve_module_name dsenv l true in
                  (match uu____2793 with
                   | None  -> case_b_find_matches_in_env ()
                   | Some m -> case_a_find_transitive_includes ns m id) in
            FStar_All.pipe_right matched_ids
              (FStar_List.map
                 (fun x  ->
                    let uu____2826 = shorten_namespace x in
                    prepare_candidate uu____2826)) in
      let json_candidates =
        let uu____2833 =
          FStar_Util.sort_with
            (fun uu____2841  ->
               fun uu____2842  ->
                 match (uu____2841, uu____2842) with
                 | ((cd1,ns1,uu____2857),(cd2,ns2,uu____2860)) ->
                     (match FStar_String.compare cd1 cd2 with
                      | _0_37 when _0_37 = (Prims.parse_int "0") ->
                          FStar_String.compare ns1 ns2
                      | n1 -> n1)) matches in
        FStar_List.map
          (fun uu____2871  ->
             match uu____2871 with
             | (candidate,ns,match_len) ->
                 FStar_Util.JsonList
                   [FStar_Util.JsonInt match_len;
                   FStar_Util.JsonStr ns;
                   FStar_Util.JsonStr candidate]) uu____2833 in
      ((QueryOK, (FStar_Util.JsonList json_candidates)), (FStar_Util.Inl st))
let run_query:
  repl_state ->
    query' ->
      ((query_status* FStar_Util.json)* (repl_state,Prims.int)
        FStar_Util.either)
  =
  fun st  ->
    fun uu___228_2901  ->
      match uu___228_2901 with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | Pop  -> run_pop st
      | Push (kind,text1,l,c) -> run_push st kind text1 l c
      | AutoComplete search_term -> run_completions st search_term
      | Lookup (symbol,pos_opt,rqi) -> run_lookup st symbol pos_opt rqi
      | ProtocolViolation query -> run_protocol_violation st query
let rec go: repl_state -> Prims.unit =
  fun st  ->
    let query = read_interactive_query st.repl_stdin in
    let uu____2931 = let uu____2938 = run_query st in uu____2938 query.qq in
    match uu____2931 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____2968 = let uu____2970 = FStar_ST.read issues in e :: uu____2970 in
    FStar_ST.write issues uu____2968 in
  let count_errors uu____2981 =
    let uu____2982 =
      let uu____2984 = FStar_ST.read issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____2984 in
    FStar_List.length uu____2982 in
  let report1 uu____2995 =
    let uu____2996 = FStar_ST.read issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____2996 in
  let clear1 uu____3004 = FStar_ST.write issues [] in
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
    (let uu____3014 = deps_of_our_file filename in
     match uu____3014 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____3028 = tc_deps None [] env filenames [] in
         (match uu____3028 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____3044 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____3045 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____3044 uu____3045 in
              let env2 =
                let uu____3049 =
                  FStar_TypeChecker_Env.set_range (Prims.snd env1)
                    initial_range in
                ((Prims.fst env1), uu____3049) in
              let env3 =
                match maybe_intf with
                | Some intf -> FStar_Universal.load_interface_decls env2 intf
                | None  -> env2 in
              let init_st =
                let uu____3057 = FStar_Util.open_stdin () in
                {
                  repl_line = (Prims.parse_int "1");
                  repl_column = (Prims.parse_int "0");
                  repl_fname = filename;
                  repl_stack = stack;
                  repl_curmod = None;
                  repl_env = env3;
                  repl_ts = ts;
                  repl_stdin = uu____3057
                } in
              let uu____3058 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ()) in
              if uu____3058
              then
                let uu____3059 =
                  let uu____3060 = FStar_Options.file_list () in
                  FStar_List.hd uu____3060 in
                FStar_SMTEncoding_Solver.with_hints_db uu____3059
                  (fun uu____3062  -> go init_st)
              else go init_st))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    FStar_Errors.set_handler interactive_error_handler;
    (let uu____3070 =
       let uu____3071 = FStar_Options.codegen () in
       FStar_Option.isSome uu____3071 in
     if uu____3070
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (try interactive_mode' filename
     with
     | e ->
         (FStar_Errors.set_handler FStar_Errors.default_handler;
          Prims.raise e))