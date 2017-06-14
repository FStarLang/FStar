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
let push:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    Prims.bool ->
      Prims.bool ->
        Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____205  ->
    fun lax1  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____205 with
          | (dsenv,env) ->
              let env1 =
                let uu___227_216 = env in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___227_216.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___227_216.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___227_216.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___227_216.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___227_216.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___227_216.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___227_216.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___227_216.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___227_216.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___227_216.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___227_216.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___227_216.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___227_216.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___227_216.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___227_216.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___227_216.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___227_216.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___227_216.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = lax1;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___227_216.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___227_216.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___227_216.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___227_216.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___227_216.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___227_216.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___227_216.FStar_TypeChecker_Env.synth)
                } in
              let res = FStar_Universal.push_context (dsenv, env1) msg in
              (FStar_Options.push ();
               if restore_cmd_line_options1
               then
                 (let uu____222 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____222 FStar_Pervasives.ignore)
               else ();
               res)
let mark:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____230  ->
    match uu____230 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.mark dsenv in
        let env1 = FStar_TypeChecker_Env.mark env in
        (FStar_Options.push (); (dsenv1, env1))
let reset_mark uu____250 =
  match uu____250 with
  | (uu____253,env) ->
      let dsenv = FStar_ToSyntax_Env.reset_mark () in
      let env1 = FStar_TypeChecker_Env.reset_mark env in
      (FStar_Options.pop (); (dsenv, env1))
let cleanup uu____266 =
  match uu____266 with
  | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
let commit_mark:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____277  ->
    match uu____277 with
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
  fun uu____304  ->
    fun curmod  ->
      fun frag  ->
        match uu____304 with
        | (dsenv,env) ->
            (try
               let uu____336 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag in
               match uu____336 with
               | Some (m,dsenv1,env1) ->
                   let uu____358 =
                     let uu____365 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____365) in
                   Some uu____358
               | uu____375 -> None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____397 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____397 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
             | FStar_Errors.Err msg when
                 let uu____410 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____410 ->
                 ((let uu____412 =
                     let uu____416 =
                       let uu____419 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____419) in
                     [uu____416] in
                   FStar_TypeChecker_Err.add_errors env uu____412);
                  None))
let report_fail: Prims.unit -> Prims.unit =
  fun uu____432  ->
    (let uu____434 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____434 FStar_Pervasives.ignore);
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
    match projectee with | Push _0 -> true | uu____479 -> false
let __proj__Push__item___0:
  input_chunks -> (Prims.bool* Prims.int* Prims.int) =
  fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_Pop: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____500 -> false
let __proj__Pop__item___0: input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Pop _0 -> _0
let uu___is_Code: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____516 -> false
let __proj__Code__item___0:
  input_chunks -> (Prims.string* (Prims.string* Prims.string)) =
  fun projectee  -> match projectee with | Code _0 -> _0
let uu___is_Info: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Info _0 -> true | uu____547 -> false
let __proj__Info__item___0:
  input_chunks ->
    (Prims.string* Prims.bool* (Prims.string* Prims.int* Prims.int) option)
  = fun projectee  -> match projectee with | Info _0 -> _0
let uu___is_Completions: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Completions _0 -> true | uu____580 -> false
let __proj__Completions__item___0: input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Completions _0 -> _0
type interactive_state =
  {
  chunk: FStar_Util.string_builder;
  stdin: FStar_Util.stream_reader option FStar_ST.ref;
  buffer: input_chunks Prims.list FStar_ST.ref;
  log: FStar_Util.file_handle option FStar_ST.ref;}
let __proj__Mkinteractive_state__item__chunk:
  interactive_state -> FStar_Util.string_builder =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__chunk
let __proj__Mkinteractive_state__item__stdin:
  interactive_state -> FStar_Util.stream_reader option FStar_ST.ref =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__stdin
let __proj__Mkinteractive_state__item__buffer:
  interactive_state -> input_chunks Prims.list FStar_ST.ref =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__buffer
let __proj__Mkinteractive_state__item__log:
  interactive_state -> FStar_Util.file_handle option FStar_ST.ref =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__log
let the_interactive_state: interactive_state =
  let uu____686 = FStar_Util.new_string_builder () in
  let uu____687 = FStar_Util.mk_ref None in
  let uu____692 = FStar_Util.mk_ref [] in
  let uu____697 = FStar_Util.mk_ref None in
  { chunk = uu____686; stdin = uu____687; buffer = uu____692; log = uu____697
  }
let rec read_chunk: Prims.unit -> input_chunks =
  fun uu____710  ->
    let s = the_interactive_state in
    let log =
      let uu____715 = FStar_Options.debug_any () in
      if uu____715
      then
        let transcript =
          let uu____719 = FStar_ST.read s.log in
          match uu____719 with
          | Some transcript -> transcript
          | None  ->
              let transcript = FStar_Util.open_file_for_writing "transcript" in
              (FStar_ST.write s.log (Some transcript); transcript) in
        fun line  ->
          (FStar_Util.append_to_file transcript line;
           FStar_Util.flush_file transcript)
      else (fun uu____733  -> ()) in
    let stdin =
      let uu____735 = FStar_ST.read s.stdin in
      match uu____735 with
      | Some i -> i
      | None  ->
          let i = FStar_Util.open_stdin () in
          (FStar_ST.write s.stdin (Some i); i) in
    let line =
      let uu____747 = FStar_Util.read_line stdin in
      match uu____747 with
      | None  -> FStar_All.exit (Prims.parse_int "0")
      | Some l -> l in
    log line;
    (let l = FStar_Util.trim_string line in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____757::ok::fail1::[] -> (ok, fail1)
         | uu____760 -> ("ok", "fail") in
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
               let uu____771 =
                 FStar_Util.substring_from l (FStar_String.length "#push") in
               FStar_Util.trim_string uu____771 in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu____785 = FStar_Util.int_of_string l1 in
                   let uu____786 = FStar_Util.int_of_string c in
                   (true, uu____785, uu____786)
               | l1::c::[] ->
                   let uu____789 = FStar_Util.int_of_string l1 in
                   let uu____790 = FStar_Util.int_of_string c in
                   (false, uu____789, uu____790)
               | uu____791 ->
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
              | uu____795::symbol::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   Info (symbol, true, None))
              | uu____805::symbol::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   (let uu____811 =
                      let uu____819 =
                        let uu____824 =
                          let uu____828 = FStar_Util.int_of_string row in
                          let uu____829 = FStar_Util.int_of_string col in
                          (file, uu____828, uu____829) in
                        Some uu____824 in
                      (symbol, false, uu____819) in
                    Info uu____811))
              | uu____837 ->
                  (FStar_Util.print_error
                     (Prims.strcat "Unrecognized \"#info\" request: " l);
                   FStar_All.exit (Prims.parse_int "1")))
           else
             if FStar_Util.starts_with l "#completions "
             then
               (match FStar_Util.split l " " with
                | uu____841::prefix1::"#"::[] ->
                    (FStar_Util.clear_string_builder s.chunk;
                     Completions prefix1)
                | uu____844 ->
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
  fun uu____853  ->
    let s = the_interactive_state in
    let uu____855 = FStar_ST.read s.buffer in
    match uu____855 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.write s.buffer chunks; chunk)
let fill_buffer: Prims.unit -> Prims.unit =
  fun uu____869  ->
    let s = the_interactive_state in
    let uu____871 =
      let uu____873 = FStar_ST.read s.buffer in
      let uu____878 = let uu____880 = read_chunk () in [uu____880] in
      FStar_List.append uu____873 uu____878 in
    FStar_ST.write s.buffer uu____871
let deps_of_our_file:
  Prims.string -> (Prims.string Prims.list* Prims.string option) =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename] in
    let uu____893 =
      FStar_List.partition
        (fun x  ->
           let uu____899 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____900 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____899 <> uu____900) deps in
    match uu____893 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____917 =
                  (let uu____918 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____918) ||
                    (let uu____919 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____919) in
                if uu____917
                then
                  let uu____920 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____920
                else ());
               Some intf)
          | impl::[] -> None
          | uu____923 ->
              ((let uu____926 =
                  FStar_Util.format1 "Unexpected: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____926);
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
            | uu____959 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____970 = FStar_Options.lax () in
                  push env uu____970 true "typecheck_modul" in
                let uu____971 = tc_one_file remaining env1 in
                (match uu____971 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____999 =
                       let intf_t =
                         match intf with
                         | Some intf1 ->
                             let uu____1007 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             Some uu____1007
                         | None  -> None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____999 with
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
                 | (uu____1073,uu____1074) ->
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
                     | uu____1138 -> (false, depnames1))
                | Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1155 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1202::ts3 ->
                    (pop env1 "";
                     (let uu____1224 =
                        let uu____1232 = FStar_List.hd stack in
                        let uu____1237 = FStar_List.tl stack in
                        (uu____1232, uu____1237) in
                      match uu____1224 with
                      | ((env2,uu____1251),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1285 = ts_elt in
                  (match uu____1285 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1303 = match_dep depnames intf impl in
                       (match uu____1303 with
                        | (b,depnames') ->
                            let uu____1314 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1314
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1326 =
                                 let uu____1334 = FStar_List.hd st in
                                 let uu____1339 = FStar_List.tl st in
                                 (uu____1334, uu____1339) in
                               match uu____1326 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1379 = deps_of_our_file filename in
            match uu____1379 with
            | (filenames,uu____1388) ->
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
            let uu____1434 = FStar_Range.string_of_range range in
            let uu____1435 =
              FStar_TypeChecker_Normalize.term_to_string env typ in
            let uu____1436 =
              match doc1 with
              | Some docstring -> FStar_Util.format1 "#doc %s" docstring
              | None  -> "" in
            FStar_Util.format4 "(defined at %s) %s: %s%s" uu____1434 name
              uu____1435 uu____1436
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
              let uu____1460 = shift_chunk () in
              match uu____1460 with
              | Info (symbol,fqn_only,pos_opt) ->
                  let uu____1472 = env in
                  (match uu____1472 with
                   | (dsenv,tcenv) ->
                       let info_at_pos_opt =
                         match pos_opt with
                         | None  -> None
                         | Some (file,row,col) ->
                             FStar_TypeChecker_Err.info_at_pos (snd env) file
                               row col in
                       let info_opt =
                         match info_at_pos_opt with
                         | Some uu____1515 -> info_at_pos_opt
                         | None  ->
                             if symbol = ""
                             then None
                             else
                               (let lid =
                                  let uu____1544 =
                                    FStar_List.map FStar_Ident.id_of_text
                                      (FStar_Util.split symbol ".") in
                                  FStar_Ident.lid_of_ids uu____1544 in
                                let lid1 =
                                  if fqn_only
                                  then lid
                                  else
                                    (let uu____1548 =
                                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                         dsenv lid in
                                     match uu____1548 with
                                     | None  -> lid
                                     | Some lid1 -> lid1) in
                                let uu____1551 =
                                  FStar_TypeChecker_Env.try_lookup_lid
                                    (snd env) lid1 in
                                FStar_All.pipe_right uu____1551
                                  (FStar_Util.map_option
                                     (fun uu____1577  ->
                                        match uu____1577 with
                                        | ((uu____1587,typ),r) ->
                                            ((FStar_Util.Inr lid1), typ, r)))) in
                       ((match info_opt with
                         | None  -> FStar_Util.print_string "\n#done-nok\n"
                         | Some (name_or_lid,typ,rng) ->
                             let uu____1612 =
                               match name_or_lid with
                               | FStar_Util.Inl name -> (name, None)
                               | FStar_Util.Inr lid ->
                                   let uu____1622 =
                                     FStar_Ident.string_of_lid lid in
                                   let uu____1623 =
                                     let uu____1625 =
                                       FStar_ToSyntax_Env.try_lookup_doc
                                         dsenv lid in
                                     FStar_All.pipe_right uu____1625
                                       (FStar_Util.map_option
                                          FStar_Pervasives.fst) in
                                   (uu____1622, uu____1623) in
                             (match uu____1612 with
                              | (name,doc1) ->
                                  let uu____1642 =
                                    format_info (snd env) name typ rng doc1 in
                                  FStar_Util.print1 "%s\n#done-ok\n"
                                    uu____1642));
                        go line_col filename stack curmod env ts))
              | Completions search_term ->
                  let rec measure_anchored_match search_term1 candidate =
                    match (search_term1, candidate) with
                    | ([],uu____1665) -> Some ([], (Prims.parse_int "0"))
                    | (uu____1673,[]) -> None
                    | (hs::ts1,hc::tc) ->
                        let hc_text = FStar_Ident.text_of_id hc in
                        if FStar_Util.starts_with hc_text hs
                        then
                          (match ts1 with
                           | [] -> Some (candidate, (FStar_String.length hs))
                           | uu____1705 ->
                               let uu____1707 = measure_anchored_match ts1 tc in
                               FStar_All.pipe_right uu____1707
                                 (FStar_Util.map_option
                                    (fun uu____1726  ->
                                       match uu____1726 with
                                       | (matched,len) ->
                                           ((hc :: matched),
                                             (((FStar_String.length hc_text)
                                                 + (Prims.parse_int "1"))
                                                + len)))))
                        else None in
                  let rec locate_match needle candidate =
                    let uu____1765 = measure_anchored_match needle candidate in
                    match uu____1765 with
                    | Some (matched,n1) -> Some ([], matched, n1)
                    | None  ->
                        (match candidate with
                         | [] -> None
                         | hc::tc ->
                             let uu____1807 = locate_match needle tc in
                             FStar_All.pipe_right uu____1807
                               (FStar_Util.map_option
                                  (fun uu____1836  ->
                                     match uu____1836 with
                                     | (prefix1,matched,len) ->
                                         ((hc :: prefix1), matched, len)))) in
                  let str_of_ids ids =
                    let uu____1862 =
                      FStar_List.map FStar_Ident.text_of_id ids in
                    FStar_Util.concat_l "." uu____1862 in
                  let match_lident_against needle lident =
                    locate_match needle
                      (FStar_List.append lident.FStar_Ident.ns
                         [lident.FStar_Ident.ident]) in
                  let shorten_namespace uu____1891 =
                    match uu____1891 with
                    | (prefix1,matched,match_len) ->
                        let naked_match =
                          match matched with
                          | uu____1909::[] -> true
                          | uu____1910 -> false in
                        let uu____1912 =
                          FStar_ToSyntax_Env.shorten_module_path (fst env)
                            prefix1 naked_match in
                        (match uu____1912 with
                         | (stripped_ns,shortened) ->
                             let uu____1927 = str_of_ids shortened in
                             let uu____1928 = str_of_ids matched in
                             let uu____1929 = str_of_ids stripped_ns in
                             (uu____1927, uu____1928, uu____1929, match_len)) in
                  let prepare_candidate uu____1940 =
                    match uu____1940 with
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
                                let uu____2031 =
                                  FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                    dsenv lid in
                                FStar_Option.map
                                  (fun fqn  ->
                                     let uu____2039 =
                                       let uu____2041 =
                                         FStar_List.map
                                           FStar_Ident.id_of_text orig_ns in
                                       FStar_List.append uu____2041
                                         [fqn.FStar_Ident.ident] in
                                     ([], uu____2039, matched_length))
                                  uu____2031
                              else None)) in
                    let case_b_find_matches_in_env uu____2060 =
                      let uu____2067 = env in
                      match uu____2067 with
                      | (dsenv,uu____2075) ->
                          let matches =
                            FStar_List.filter_map
                              (match_lident_against needle)
                              all_lidents_in_env in
                          FStar_All.pipe_right matches
                            (FStar_List.filter
                               (fun uu____2105  ->
                                  match uu____2105 with
                                  | (ns,id,uu____2113) ->
                                      let uu____2118 =
                                        let uu____2120 =
                                          FStar_Ident.lid_of_ids id in
                                        FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                          dsenv uu____2120 in
                                      (match uu____2118 with
                                       | None  -> false
                                       | Some l ->
                                           let uu____2122 =
                                             FStar_Ident.lid_of_ids
                                               (FStar_List.append ns id) in
                                           FStar_Ident.lid_equals l
                                             uu____2122))) in
                    let uu____2123 = FStar_Util.prefix needle in
                    match uu____2123 with
                    | (ns,id) ->
                        let matched_ids =
                          match ns with
                          | [] -> case_b_find_matches_in_env ()
                          | uu____2148 ->
                              let l =
                                FStar_Ident.lid_of_path ns
                                  FStar_Range.dummyRange in
                              let uu____2151 =
                                FStar_ToSyntax_Env.resolve_module_name
                                  (fst env) l true in
                              (match uu____2151 with
                               | None  -> case_b_find_matches_in_env ()
                               | Some m ->
                                   case_a_find_transitive_includes ns m id) in
                        FStar_All.pipe_right matched_ids
                          (FStar_List.map
                             (fun x  ->
                                let uu____2184 = shorten_namespace x in
                                prepare_candidate uu____2184)) in
                  ((let uu____2190 =
                      FStar_Util.sort_with
                        (fun uu____2198  ->
                           fun uu____2199  ->
                             match (uu____2198, uu____2199) with
                             | ((cd1,ns1,uu____2214),(cd2,ns2,uu____2217)) ->
                                 (match FStar_String.compare cd1 cd2 with
                                  | _0_51 when _0_51 = (Prims.parse_int "0")
                                      -> FStar_String.compare ns1 ns2
                                  | n1 -> n1)) matches in
                    FStar_List.iter
                      (fun uu____2228  ->
                         match uu____2228 with
                         | (candidate,ns,match_len) ->
                             let uu____2235 =
                               FStar_Util.string_of_int match_len in
                             FStar_Util.print3 "%s %s %s \n" uu____2235 ns
                               candidate) uu____2190);
                   FStar_Util.print_string "#done-ok\n";
                   go line_col filename stack curmod env ts)
              | Pop msg ->
                  (pop env msg;
                   (let uu____2239 =
                      match stack with
                      | [] ->
                          (FStar_Util.print_error "too many pops";
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd1::tl1 -> (hd1, tl1) in
                    match uu____2239 with
                    | ((env1,curmod1),stack1) ->
                        (if
                           (FStar_List.length stack1) =
                             (FStar_List.length ts)
                         then cleanup env1
                         else ();
                         go line_col filename stack1 curmod1 env1 ts)))
              | Push (lax1,l,c) ->
                  let uu____2310 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____2337 =
                        update_deps filename curmod stack env ts in
                      (true, uu____2337)
                    else (false, (stack, env, ts)) in
                  (match uu____2310 with
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
                   | uu____2417 -> fail2 curmod env_mark)
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    (let uu____2429 =
       let uu____2430 = FStar_Options.codegen () in
       FStar_Option.isSome uu____2430 in
     if uu____2429
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____2433 = deps_of_our_file filename in
     match uu____2433 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____2447 = tc_deps None [] env filenames [] in
         (match uu____2447 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____2463 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____2464 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____2463 uu____2464 in
              let env2 =
                let uu____2468 =
                  FStar_TypeChecker_Env.set_range (snd env1) initial_range in
                ((fst env1), uu____2468) in
              let env3 =
                match maybe_intf with
                | Some intf -> FStar_Universal.load_interface_decls env2 intf
                | None  -> env2 in
              let uu____2475 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ()) in
              if uu____2475
              then
                let uu____2476 =
                  let uu____2477 = FStar_Options.file_list () in
                  FStar_List.hd uu____2477 in
                FStar_SMTEncoding_Solver.with_hints_db uu____2476
                  (fun uu____2479  ->
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack None env3 ts)
              else
                go ((Prims.parse_int "1"), (Prims.parse_int "0")) filename
                  stack None env3 ts))