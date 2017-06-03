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
              FStar_Universal.tc_one_file dsenv env (Some intf) impl in
            (match uu____61 with
             | (uu____76,dsenv1,env1) ->
                 (((Some intf), impl), dsenv1, env1, remaining1))
        | intf_or_impl::remaining1 ->
            let uu____93 =
              FStar_Universal.tc_one_file dsenv env None intf_or_impl in
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
type modul_t = FStar_Syntax_Syntax.modul option
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
                let uu___226_229 = env in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___226_229.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___226_229.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___226_229.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___226_229.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___226_229.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___226_229.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___226_229.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___226_229.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___226_229.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___226_229.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___226_229.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___226_229.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___226_229.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___226_229.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___226_229.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___226_229.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___226_229.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___226_229.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = lax1;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___226_229.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___226_229.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___226_229.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___226_229.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___226_229.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___226_229.FStar_TypeChecker_Env.proof_ns)
                } in
              let res = FStar_Universal.push_context (dsenv, env1) msg in
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
let report_fail: Prims.unit -> Prims.unit =
  fun uu____445  ->
    (let uu____447 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____447 FStar_Pervasives.ignore);
    FStar_Errors.clear ()
type input_chunks =
  | Push of (Prims.bool* Prims.int* Prims.int)
  | Pop of Prims.string
  | Code of (Prims.string* (Prims.string* Prims.string))
  | Info of (Prims.string* Prims.bool* (Prims.string* Prims.int* Prims.int)
  option)
  | Completions of Prims.string
let uu___is_Push: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____487 -> false
let __proj__Push__item___0:
  input_chunks -> (Prims.bool* Prims.int* Prims.int) =
  fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_Pop: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____508 -> false
let __proj__Pop__item___0: input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Pop _0 -> _0
let uu___is_Code: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____524 -> false
let __proj__Code__item___0:
  input_chunks -> (Prims.string* (Prims.string* Prims.string)) =
  fun projectee  -> match projectee with | Code _0 -> _0
let uu___is_Info: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Info _0 -> true | uu____555 -> false
let __proj__Info__item___0:
  input_chunks ->
    (Prims.string* Prims.bool* (Prims.string* Prims.int* Prims.int) option)
  = fun projectee  -> match projectee with | Info _0 -> _0
let uu___is_Completions: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Completions _0 -> true | uu____588 -> false
let __proj__Completions__item___0: input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Completions _0 -> _0
type interactive_state =
  {
  chunk: FStar_Util.string_builder;
  stdin: FStar_Util.stream_reader option FStar_ST.ref;
  buffer: input_chunks Prims.list FStar_ST.ref;
  log: FStar_Util.file_handle option FStar_ST.ref;}
let the_interactive_state: interactive_state =
  let uu____651 = FStar_Util.new_string_builder () in
  let uu____652 = FStar_Util.mk_ref None in
  let uu____657 = FStar_Util.mk_ref [] in
  let uu____662 = FStar_Util.mk_ref None in
  { chunk = uu____651; stdin = uu____652; buffer = uu____657; log = uu____662
  }
let rec read_chunk: Prims.unit -> input_chunks =
  fun uu____675  ->
    let s = the_interactive_state in
    let log =
      let uu____680 = FStar_Options.debug_any () in
      if uu____680
      then
        let transcript =
          let uu____684 = FStar_ST.read s.log in
          match uu____684 with
          | Some transcript -> transcript
          | None  ->
              let transcript = FStar_Util.open_file_for_writing "transcript" in
              (FStar_ST.write s.log (Some transcript); transcript) in
        fun line  ->
          (FStar_Util.append_to_file transcript line;
           FStar_Util.flush_file transcript)
      else (fun uu____698  -> ()) in
    let stdin =
      let uu____700 = FStar_ST.read s.stdin in
      match uu____700 with
      | Some i -> i
      | None  ->
          let i = FStar_Util.open_stdin () in
          (FStar_ST.write s.stdin (Some i); i) in
    let line =
      let uu____712 = FStar_Util.read_line stdin in
      match uu____712 with
      | None  -> FStar_All.exit (Prims.parse_int "0")
      | Some l -> l in
    log line;
    (let l = FStar_Util.trim_string line in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____722::ok::fail1::[] -> (ok, fail1)
         | uu____725 -> ("ok", "fail") in
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
               let uu____736 =
                 FStar_Util.substring_from l (FStar_String.length "#push") in
               FStar_Util.trim_string uu____736 in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu____750 = FStar_Util.int_of_string l1 in
                   let uu____751 = FStar_Util.int_of_string c in
                   (true, uu____750, uu____751)
               | l1::c::[] ->
                   let uu____754 = FStar_Util.int_of_string l1 in
                   let uu____755 = FStar_Util.int_of_string c in
                   (false, uu____754, uu____755)
               | uu____756 ->
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
              | uu____760::symbol::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   Info (symbol, true, None))
              | uu____770::symbol::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   (let uu____776 =
                      let uu____784 =
                        let uu____789 =
                          let uu____793 = FStar_Util.int_of_string row in
                          let uu____794 = FStar_Util.int_of_string col in
                          (file, uu____793, uu____794) in
                        Some uu____789 in
                      (symbol, false, uu____784) in
                    Info uu____776))
              | uu____802 ->
                  (FStar_Util.print_error
                     (Prims.strcat "Unrecognized \"#info\" request: " l);
                   FStar_All.exit (Prims.parse_int "1")))
           else
             if FStar_Util.starts_with l "#completions "
             then
               (match FStar_Util.split l " " with
                | uu____806::prefix1::"#"::[] ->
                    (FStar_Util.clear_string_builder s.chunk;
                     Completions prefix1)
                | uu____809 ->
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
  fun uu____818  ->
    let s = the_interactive_state in
    let uu____820 = FStar_ST.read s.buffer in
    match uu____820 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.write s.buffer chunks; chunk)
let fill_buffer: Prims.unit -> Prims.unit =
  fun uu____834  ->
    let s = the_interactive_state in
    let uu____836 =
      let uu____838 = FStar_ST.read s.buffer in
      let uu____843 = let uu____845 = read_chunk () in [uu____845] in
      FStar_List.append uu____838 uu____843 in
    FStar_ST.write s.buffer uu____836
let deps_of_our_file:
  Prims.string -> (Prims.string Prims.list* Prims.string option) =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename] in
    let uu____858 =
      FStar_List.partition
        (fun x  ->
           let uu____864 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____865 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____864 <> uu____865) deps in
    match uu____858 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____882 =
                  (let uu____883 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____883) ||
                    (let uu____884 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____884) in
                if uu____882
                then
                  let uu____885 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____885
                else ());
               Some intf)
          | impl::[] -> None
          | uu____888 ->
              ((let uu____891 =
                  FStar_Util.format1 "Unexpected: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____891);
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
            | uu____924 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____935 = FStar_Options.lax () in
                  push env uu____935 true "typecheck_modul" in
                let uu____936 = tc_one_file remaining env1 in
                (match uu____936 with
                 | ((intf,impl),env2,modl,remaining1) ->
                     let uu____969 =
                       let intf_t =
                         match intf with
                         | Some intf1 ->
                             let uu____977 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             Some uu____977
                         | None  -> None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____969 with
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
                 | (uu____1043,uu____1044) ->
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
                     | uu____1108 -> (false, depnames1))
                | Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1125 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1172::ts3 ->
                    (pop env1 "";
                     (let uu____1194 =
                        let uu____1202 = FStar_List.hd stack in
                        let uu____1207 = FStar_List.tl stack in
                        (uu____1202, uu____1207) in
                      match uu____1194 with
                      | ((env2,uu____1221),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1255 = ts_elt in
                  (match uu____1255 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1273 = match_dep depnames intf impl in
                       (match uu____1273 with
                        | (b,depnames') ->
                            let uu____1284 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1284
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1296 =
                                 let uu____1304 = FStar_List.hd st in
                                 let uu____1309 = FStar_List.tl st in
                                 (uu____1304, uu____1309) in
                               match uu____1296 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1349 = deps_of_our_file filename in
            match uu____1349 with
            | (filenames,uu____1358) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let format_info:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term ->
        FStar_Range.range -> Prims.string option -> Prims.string
  =
  fun env  ->
    fun name  ->
      fun typ  ->
        fun range  ->
          fun doc1  ->
            let uu____1404 = FStar_Range.string_of_range range in
            let uu____1405 =
              FStar_TypeChecker_Normalize.term_to_string env typ in
            let uu____1406 =
              match doc1 with
              | Some docstring -> FStar_Util.format1 "#doc %s" docstring
              | None  -> "" in
            FStar_Util.format4 "(defined at %s) %s: %s%s" uu____1404 name
              uu____1405 uu____1406
let rec go:
  (Prims.int* Prims.int) ->
    Prims.string -> stack_t -> modul_t -> env_t -> m_timestamps -> Prims.unit
  =
  fun line_col  ->
    fun filename  ->
      fun stack  ->
        fun curmod  ->
          fun env  ->
            fun ts  ->
              let uu____1430 = shift_chunk () in
              match uu____1430 with
              | Info (symbol,fqn_only,pos_opt) ->
                  let uu____1442 = env in
                  (match uu____1442 with
                   | (dsenv,tcenv) ->
                       let info_at_pos_opt =
                         match pos_opt with
                         | None  -> None
                         | Some (file,row,col) ->
                             FStar_TypeChecker_Err.info_at_pos (snd env) file
                               row col in
                       let info_opt =
                         match info_at_pos_opt with
                         | Some uu____1485 -> info_at_pos_opt
                         | None  ->
                             if symbol = ""
                             then None
                             else
                               (let lid =
                                  let uu____1514 =
                                    FStar_List.map FStar_Ident.id_of_text
                                      (FStar_Util.split symbol ".") in
                                  FStar_Ident.lid_of_ids uu____1514 in
                                let lid1 =
                                  if fqn_only
                                  then lid
                                  else
                                    (let uu____1518 =
                                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                         dsenv lid in
                                     match uu____1518 with
                                     | None  -> lid
                                     | Some lid1 -> lid1) in
                                let uu____1521 =
                                  FStar_TypeChecker_Env.try_lookup_lid
                                    (snd env) lid1 in
                                FStar_All.pipe_right uu____1521
                                  (FStar_Util.map_option
                                     (fun uu____1547  ->
                                        match uu____1547 with
                                        | ((uu____1557,typ),r) ->
                                            ((FStar_Util.Inr lid1), typ, r)))) in
                       ((match info_opt with
                         | None  -> FStar_Util.print_string "\n#done-nok\n"
                         | Some (name_or_lid,typ,rng) ->
                             let uu____1582 =
                               match name_or_lid with
                               | FStar_Util.Inl name -> (name, None)
                               | FStar_Util.Inr lid ->
                                   let uu____1592 =
                                     FStar_Ident.string_of_lid lid in
                                   let uu____1593 =
                                     let uu____1595 =
                                       FStar_ToSyntax_Env.try_lookup_doc
                                         dsenv lid in
                                     FStar_All.pipe_right uu____1595
                                       (FStar_Util.map_option
                                          FStar_Pervasives.fst) in
                                   (uu____1592, uu____1593) in
                             (match uu____1582 with
                              | (name,doc1) ->
                                  let uu____1612 =
                                    format_info (snd env) name typ rng doc1 in
                                  FStar_Util.print1 "%s\n#done-ok\n"
                                    uu____1612));
                        go line_col filename stack curmod env ts))
              | Completions search_term ->
                  let rec measure_anchored_match search_term1 candidate =
                    match (search_term1, candidate) with
                    | ([],uu____1635) -> Some ([], (Prims.parse_int "0"))
                    | (uu____1643,[]) -> None
                    | (hs::ts1,hc::tc) ->
                        let hc_text = FStar_Ident.text_of_id hc in
                        if FStar_Util.starts_with hc_text hs
                        then
                          (match ts1 with
                           | [] -> Some (candidate, (FStar_String.length hs))
                           | uu____1675 ->
                               let uu____1677 = measure_anchored_match ts1 tc in
                               FStar_All.pipe_right uu____1677
                                 (FStar_Util.map_option
                                    (fun uu____1696  ->
                                       match uu____1696 with
                                       | (matched,len) ->
                                           ((hc :: matched),
                                             (((FStar_String.length hc_text)
                                                 + (Prims.parse_int "1"))
                                                + len)))))
                        else None in
                  let rec locate_match needle candidate =
                    let uu____1735 = measure_anchored_match needle candidate in
                    match uu____1735 with
                    | Some (matched,n1) -> Some ([], matched, n1)
                    | None  ->
                        (match candidate with
                         | [] -> None
                         | hc::tc ->
                             let uu____1777 = locate_match needle tc in
                             FStar_All.pipe_right uu____1777
                               (FStar_Util.map_option
                                  (fun uu____1806  ->
                                     match uu____1806 with
                                     | (prefix1,matched,len) ->
                                         ((hc :: prefix1), matched, len)))) in
                  let str_of_ids ids =
                    let uu____1832 =
                      FStar_List.map FStar_Ident.text_of_id ids in
                    FStar_Util.concat_l "." uu____1832 in
                  let match_lident_against needle lident =
                    locate_match needle
                      (FStar_List.append lident.FStar_Ident.ns
                         [lident.FStar_Ident.ident]) in
                  let shorten_namespace uu____1861 =
                    match uu____1861 with
                    | (prefix1,matched,match_len) ->
                        let naked_match =
                          match matched with
                          | uu____1879::[] -> true
                          | uu____1880 -> false in
                        let uu____1882 =
                          FStar_ToSyntax_Env.shorten_module_path (fst env)
                            prefix1 naked_match in
                        (match uu____1882 with
                         | (stripped_ns,shortened) ->
                             let uu____1897 = str_of_ids shortened in
                             let uu____1898 = str_of_ids matched in
                             let uu____1899 = str_of_ids stripped_ns in
                             (uu____1897, uu____1898, uu____1899, match_len)) in
                  let prepare_candidate uu____1910 =
                    match uu____1910 with
                    | (prefix1,matched,stripped_ns,match_len) ->
                        if prefix1 = ""
                        then (matched, stripped_ns, match_len)
                        else
                          ((Prims.strcat prefix1 (Prims.strcat "." matched)),
                            stripped_ns,
                            (((FStar_String.length prefix1) + match_len) +
                               (Prims.parse_int "1"))) in
                  let needle = FStar_Util.split search_term "." in
                  let all_lidents_in_env =
                    FStar_TypeChecker_Env.lidents (snd env) in
                  let matches =
                    let case_a_find_transitive_includes orig_ns m id =
                      let dsenv = fst env in
                      let exported_names =
                        FStar_ToSyntax_Env.transitive_exported_ids dsenv m in
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
                                let uu____2001 =
                                  FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                    dsenv lid in
                                FStar_Option.map
                                  (fun fqn  ->
                                     let uu____2009 =
                                       let uu____2011 =
                                         FStar_List.map
                                           FStar_Ident.id_of_text orig_ns in
                                       FStar_List.append uu____2011
                                         [fqn.FStar_Ident.ident] in
                                     ([], uu____2009, matched_length))
                                  uu____2001
                              else None)) in
                    let case_b_find_matches_in_env uu____2030 =
                      let uu____2037 = env in
                      match uu____2037 with
                      | (dsenv,uu____2045) ->
                          let matches =
                            FStar_List.filter_map
                              (match_lident_against needle)
                              all_lidents_in_env in
                          FStar_All.pipe_right matches
                            (FStar_List.filter
                               (fun uu____2075  ->
                                  match uu____2075 with
                                  | (ns,id,uu____2083) ->
                                      let uu____2088 =
                                        let uu____2090 =
                                          FStar_Ident.lid_of_ids id in
                                        FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                          dsenv uu____2090 in
                                      (match uu____2088 with
                                       | None  -> false
                                       | Some l ->
                                           let uu____2092 =
                                             FStar_Ident.lid_of_ids
                                               (FStar_List.append ns id) in
                                           FStar_Ident.lid_equals l
                                             uu____2092))) in
                    let uu____2093 = FStar_Util.prefix needle in
                    match uu____2093 with
                    | (ns,id) ->
                        let matched_ids =
                          match ns with
                          | [] -> case_b_find_matches_in_env ()
                          | uu____2118 ->
                              let l =
                                FStar_Ident.lid_of_path ns
                                  FStar_Range.dummyRange in
                              let uu____2121 =
                                FStar_ToSyntax_Env.resolve_module_name
                                  (fst env) l true in
                              (match uu____2121 with
                               | None  -> case_b_find_matches_in_env ()
                               | Some m ->
                                   case_a_find_transitive_includes ns m id) in
                        FStar_All.pipe_right matched_ids
                          (FStar_List.map
                             (fun x  ->
                                let uu____2154 = shorten_namespace x in
                                prepare_candidate uu____2154)) in
                  ((let uu____2160 =
                      FStar_Util.sort_with
                        (fun uu____2168  ->
                           fun uu____2169  ->
                             match (uu____2168, uu____2169) with
                             | ((cd1,ns1,uu____2184),(cd2,ns2,uu____2187)) ->
                                 (match FStar_String.compare cd1 cd2 with
                                  | _0_41 when _0_41 = (Prims.parse_int "0")
                                      -> FStar_String.compare ns1 ns2
                                  | n1 -> n1)) matches in
                    FStar_List.iter
                      (fun uu____2198  ->
                         match uu____2198 with
                         | (candidate,ns,match_len) ->
                             let uu____2205 =
                               FStar_Util.string_of_int match_len in
                             FStar_Util.print3 "%s %s %s \n" uu____2205 ns
                               candidate) uu____2160);
                   FStar_Util.print_string "#done-ok\n";
                   go line_col filename stack curmod env ts)
              | Pop msg ->
                  (pop env msg;
                   (let uu____2209 =
                      match stack with
                      | [] ->
                          (FStar_Util.print_error "too many pops";
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd1::tl1 -> (hd1, tl1) in
                    match uu____2209 with
                    | ((env1,curmod1),stack1) ->
                        (if
                           (FStar_List.length stack1) =
                             (FStar_List.length ts)
                         then cleanup env1
                         else ();
                         go line_col filename stack1 curmod1 env1 ts)))
              | Push (lax1,l,c) ->
                  let uu____2280 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____2307 =
                        update_deps filename curmod stack env ts in
                      (true, uu____2307)
                    else (false, (stack, env, ts)) in
                  (match uu____2280 with
                   | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
                       let stack2 = (env1, curmod) :: stack1 in
                       let env2 =
                         push env1 lax1 restore_cmd_line_options1 "#push" in
                       go (l, c) filename stack2 curmod env2 ts1)
              | Code (text1,(ok,fail1)) ->
                  let fail2 curmod1 env_mark =
                    report_fail ();
                    FStar_Util.print1 "%s\n" fail1;
                    (let env1 = reset_mark env_mark in
                     go line_col filename stack curmod1 env1 ts) in
                  let env_mark = mark env in
                  let frag =
                    {
                      FStar_Parser_ParseIt.frag_text = text1;
                      FStar_Parser_ParseIt.frag_line = (fst line_col);
                      FStar_Parser_ParseIt.frag_col = (snd line_col)
                    } in
                  let res = check_frag env_mark curmod (frag, false) in
                  (match res with
                   | Some (curmod1,env1,n_errs) ->
                       if n_errs = (Prims.parse_int "0")
                       then
                         (FStar_Util.print1 "\n%s\n" ok;
                          (let env2 = commit_mark env1 in
                           go line_col filename stack curmod1 env2 ts))
                       else fail2 curmod1 env_mark
                   | uu____2387 -> fail2 curmod env_mark)
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    (let uu____2399 =
       let uu____2400 = FStar_Options.codegen () in
       FStar_Option.isSome uu____2400 in
     if uu____2399
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____2403 = deps_of_our_file filename in
     match uu____2403 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____2417 = tc_deps None [] env filenames [] in
         (match uu____2417 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____2433 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____2434 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____2433 uu____2434 in
              let env2 =
                let uu____2438 =
                  FStar_TypeChecker_Env.set_range (snd env1) initial_range in
                ((fst env1), uu____2438) in
              let env3 =
                match maybe_intf with
                | Some intf -> FStar_Universal.load_interface_decls env2 intf
                | None  -> env2 in
              let uu____2445 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ()) in
              if uu____2445
              then
                let uu____2446 =
                  let uu____2447 = FStar_Options.file_list () in
                  FStar_List.hd uu____2447 in
                FStar_SMTEncoding_Solver.with_hints_db uu____2446
                  (fun uu____2449  ->
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack None env3 ts)
              else
                go ((Prims.parse_int "1"), (Prims.parse_int "0")) filename
                  stack None env3 ts))