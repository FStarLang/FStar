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
                let uu___176_216 = env in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___176_216.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___176_216.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___176_216.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___176_216.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___176_216.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___176_216.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___176_216.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___176_216.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___176_216.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___176_216.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___176_216.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___176_216.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___176_216.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___176_216.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___176_216.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___176_216.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___176_216.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___176_216.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = lax1;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___176_216.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___176_216.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___176_216.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___176_216.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___176_216.FStar_TypeChecker_Env.qname_and_index)
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
               let uu____342 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag in
               match uu____342 with
               | Some (m,dsenv1,env1) ->
                   let uu____364 =
                     let uu____371 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____371) in
                   Some uu____364
               | uu____381 -> None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____407 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____407 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
             | FStar_Errors.Err msg when
                 let uu____420 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____420 ->
                 ((let uu____422 =
                     let uu____426 =
                       let uu____429 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____429) in
                     [uu____426] in
                   FStar_TypeChecker_Err.add_errors env uu____422);
                  None))
let report_fail: Prims.unit -> Prims.unit =
  fun uu____442  ->
    (let uu____444 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____444 FStar_Pervasives.ignore);
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
    match projectee with | Push _0 -> true | uu____489 -> false
let __proj__Push__item___0:
  input_chunks -> (Prims.bool* Prims.int* Prims.int) =
  fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_Pop: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____510 -> false
let __proj__Pop__item___0: input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Pop _0 -> _0
let uu___is_Code: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____526 -> false
let __proj__Code__item___0:
  input_chunks -> (Prims.string* (Prims.string* Prims.string)) =
  fun projectee  -> match projectee with | Code _0 -> _0
let uu___is_Info: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Info _0 -> true | uu____557 -> false
let __proj__Info__item___0:
  input_chunks ->
    (Prims.string* Prims.bool* (Prims.string* Prims.int* Prims.int) option)
  = fun projectee  -> match projectee with | Info _0 -> _0
let uu___is_Completions: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Completions _0 -> true | uu____590 -> false
let __proj__Completions__item___0: input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Completions _0 -> _0
type interactive_state =
  {
  chunk: FStar_Util.string_builder;
  stdin: FStar_Util.stream_reader option FStar_ST.ref;
  buffer: input_chunks Prims.list FStar_ST.ref;
  log: FStar_Util.file_handle option FStar_ST.ref;}
let the_interactive_state: interactive_state =
  let uu____657 = FStar_Util.new_string_builder () in
  let uu____658 = FStar_Util.mk_ref None in
  let uu____663 = FStar_Util.mk_ref [] in
  let uu____668 = FStar_Util.mk_ref None in
  { chunk = uu____657; stdin = uu____658; buffer = uu____663; log = uu____668
  }
let rec read_chunk: Prims.unit -> input_chunks =
  fun uu____681  ->
    let s = the_interactive_state in
    let log =
      let uu____686 = FStar_Options.debug_any () in
      if uu____686
      then
        let transcript =
          let uu____690 = FStar_ST.read s.log in
          match uu____690 with
          | Some transcript -> transcript
          | None  ->
              let transcript = FStar_Util.open_file_for_writing "transcript" in
              (FStar_ST.write s.log (Some transcript); transcript) in
        fun line  ->
          (FStar_Util.append_to_file transcript line;
           FStar_Util.flush_file transcript)
      else (fun uu____704  -> ()) in
    let stdin =
      let uu____706 = FStar_ST.read s.stdin in
      match uu____706 with
      | Some i -> i
      | None  ->
          let i = FStar_Util.open_stdin () in
          (FStar_ST.write s.stdin (Some i); i) in
    let line =
      let uu____718 = FStar_Util.read_line stdin in
      match uu____718 with
      | None  -> FStar_All.exit (Prims.parse_int "0")
      | Some l -> l in
    log line;
    (let l = FStar_Util.trim_string line in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____728::ok::fail::[] -> (ok, fail)
         | uu____731 -> ("ok", "fail") in
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
               let uu____742 =
                 FStar_Util.substring_from l (FStar_String.length "#push") in
               FStar_Util.trim_string uu____742 in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu____754 = FStar_Util.int_of_string l1 in
                   let uu____755 = FStar_Util.int_of_string c in
                   (true, uu____754, uu____755)
               | l1::c::[] ->
                   let uu____758 = FStar_Util.int_of_string l1 in
                   let uu____759 = FStar_Util.int_of_string c in
                   (false, uu____758, uu____759)
               | uu____760 ->
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
              | uu____764::symbol::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   Info (symbol, true, None))
              | uu____774::symbol::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   (let uu____780 =
                      let uu____788 =
                        let uu____793 =
                          let uu____797 = FStar_Util.int_of_string row in
                          let uu____798 = FStar_Util.int_of_string col in
                          (file, uu____797, uu____798) in
                        Some uu____793 in
                      (symbol, false, uu____788) in
                    Info uu____780))
              | uu____806 ->
                  (FStar_Util.print_error
                     (Prims.strcat "Unrecognized \"#info\" request: " l);
                   FStar_All.exit (Prims.parse_int "1")))
           else
             if FStar_Util.starts_with l "#completions "
             then
               (match FStar_Util.split l " " with
                | uu____810::prefix1::"#"::[] ->
                    (FStar_Util.clear_string_builder s.chunk;
                     Completions prefix1)
                | uu____813 ->
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
  fun uu____822  ->
    let s = the_interactive_state in
    let uu____824 = FStar_ST.read s.buffer in
    match uu____824 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.write s.buffer chunks; chunk)
let fill_buffer: Prims.unit -> Prims.unit =
  fun uu____838  ->
    let s = the_interactive_state in
    let uu____840 =
      let uu____842 = FStar_ST.read s.buffer in
      let uu____847 = let uu____849 = read_chunk () in [uu____849] in
      FStar_List.append uu____842 uu____847 in
    FStar_ST.write s.buffer uu____840
let deps_of_our_file:
  Prims.string -> (Prims.string Prims.list* Prims.string option) =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename] in
    let uu____862 =
      FStar_List.partition
        (fun x  ->
           let uu____871 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____872 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____871 <> uu____872) deps in
    match uu____862 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____889 =
                  (let uu____892 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____892) ||
                    (let uu____894 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____894) in
                if uu____889
                then
                  let uu____895 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____895
                else ());
               Some intf)
          | impl::[] -> None
          | uu____898 ->
              ((let uu____901 =
                  FStar_Util.format1 "Unexpected: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____901);
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
            | uu____934 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____945 = FStar_Options.lax () in
                  push env uu____945 true "typecheck_modul" in
                let uu____946 = tc_one_file remaining env1 in
                (match uu____946 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____974 =
                       let intf_t =
                         match intf with
                         | Some intf1 ->
                             let uu____982 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             Some uu____982
                         | None  -> None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____974 with
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
                 | (uu____1051,uu____1052) ->
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
                     | uu____1116 -> (false, depnames1))
                | Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1133 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1180::ts3 ->
                    (pop env1 "";
                     (let uu____1202 =
                        let uu____1210 = FStar_List.hd stack in
                        let uu____1215 = FStar_List.tl stack in
                        (uu____1210, uu____1215) in
                      match uu____1202 with
                      | ((env2,uu____1229),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1263 = ts_elt in
                  (match uu____1263 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1281 = match_dep depnames intf impl in
                       (match uu____1281 with
                        | (b,depnames') ->
                            let uu____1292 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1292
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1304 =
                                 let uu____1312 = FStar_List.hd st in
                                 let uu____1317 = FStar_List.tl st in
                                 (uu____1312, uu____1317) in
                               match uu____1304 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1357 = deps_of_our_file filename in
            match uu____1357 with
            | (filenames,uu____1366) ->
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
            let uu____1412 = FStar_Range.string_of_range range in
            let uu____1413 =
              FStar_TypeChecker_Normalize.term_to_string env typ in
            let uu____1414 =
              match doc1 with
              | Some docstring -> FStar_Util.format1 "#doc %s" docstring
              | None  -> "" in
            FStar_Util.format4 "(defined at %s) %s: %s%s" uu____1412 name
              uu____1413 uu____1414
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
              let uu____1438 = shift_chunk () in
              match uu____1438 with
              | Info (symbol,fqn_only,pos_opt) ->
                  let uu____1450 = env in
                  (match uu____1450 with
                   | (dsenv,tcenv) ->
                       let info_at_pos_opt =
                         match pos_opt with
                         | None  -> None
                         | Some (file,row,col) ->
                             FStar_TypeChecker_Err.info_at_pos (snd env) file
                               row col in
                       let info_opt =
                         match info_at_pos_opt with
                         | Some uu____1493 -> info_at_pos_opt
                         | None  ->
                             if symbol = ""
                             then None
                             else
                               (let lid =
                                  let uu____1522 =
                                    FStar_List.map FStar_Ident.id_of_text
                                      (FStar_Util.split symbol ".") in
                                  FStar_Ident.lid_of_ids uu____1522 in
                                let lid1 =
                                  if fqn_only
                                  then lid
                                  else
                                    (let uu____1526 =
                                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                         dsenv lid in
                                     match uu____1526 with
                                     | None  -> lid
                                     | Some lid1 -> lid1) in
                                let uu____1529 =
                                  FStar_TypeChecker_Env.try_lookup_lid
                                    (snd env) lid1 in
                                FStar_All.pipe_right uu____1529
                                  (FStar_Util.map_option
                                     (fun uu____1559  ->
                                        match uu____1559 with
                                        | ((uu____1569,typ),r) ->
                                            ((FStar_Util.Inr lid1), typ, r)))) in
                       ((match info_opt with
                         | None  -> FStar_Util.print_string "\n#done-nok\n"
                         | Some (name_or_lid,typ,rng) ->
                             let uu____1594 =
                               match name_or_lid with
                               | FStar_Util.Inl name -> (name, None)
                               | FStar_Util.Inr lid ->
                                   let uu____1604 =
                                     FStar_Ident.string_of_lid lid in
                                   let uu____1605 =
                                     let uu____1607 =
                                       FStar_ToSyntax_Env.try_lookup_doc
                                         dsenv lid in
                                     FStar_All.pipe_right uu____1607
                                       (FStar_Util.map_option
                                          FStar_Pervasives.fst) in
                                   (uu____1604, uu____1605) in
                             (match uu____1594 with
                              | (name,doc1) ->
                                  let uu____1624 =
                                    format_info (snd env) name typ rng doc1 in
                                  FStar_Util.print1 "%s\n#done-ok\n"
                                    uu____1624));
                        go line_col filename stack curmod env ts))
              | Completions search_term ->
                  let rec measure_anchored_match search_term1 candidate =
                    match (search_term1, candidate) with
                    | ([],uu____1647) -> Some ([], (Prims.parse_int "0"))
                    | (uu____1655,[]) -> None
                    | (hs::ts1,hc::tc) ->
                        let hc_text = FStar_Ident.text_of_id hc in
                        if FStar_Util.starts_with hc_text hs
                        then
                          (match ts1 with
                           | [] -> Some (candidate, (FStar_String.length hs))
                           | uu____1685 ->
                               let uu____1687 = measure_anchored_match ts1 tc in
                               FStar_All.pipe_right uu____1687
                                 (FStar_Util.map_option
                                    (fun uu____1709  ->
                                       match uu____1709 with
                                       | (matched,len) ->
                                           ((hc :: matched),
                                             (((FStar_String.length hc_text)
                                                 + (Prims.parse_int "1"))
                                                + len)))))
                        else None in
                  let rec locate_match needle candidate =
                    let uu____1745 = measure_anchored_match needle candidate in
                    match uu____1745 with
                    | Some (matched,n1) -> Some ([], matched, n1)
                    | None  ->
                        (match candidate with
                         | [] -> None
                         | hc::tc ->
                             let uu____1787 = locate_match needle tc in
                             FStar_All.pipe_right uu____1787
                               (FStar_Util.map_option
                                  (fun uu____1820  ->
                                     match uu____1820 with
                                     | (prefix1,matched,len) ->
                                         ((hc :: prefix1), matched, len)))) in
                  let str_of_ids ids =
                    let uu____1846 =
                      FStar_List.map FStar_Ident.text_of_id ids in
                    FStar_Util.concat_l "." uu____1846 in
                  let match_lident_against needle lident =
                    locate_match needle
                      (FStar_List.append lident.FStar_Ident.ns
                         [lident.FStar_Ident.ident]) in
                  let shorten_namespace uu____1875 =
                    match uu____1875 with
                    | (prefix1,matched,match_len) ->
                        let naked_match =
                          match matched with
                          | uu____1893::[] -> true
                          | uu____1894 -> false in
                        let uu____1896 =
                          FStar_ToSyntax_Env.shorten_module_path (fst env)
                            prefix1 naked_match in
                        (match uu____1896 with
                         | (stripped_ns,shortened) ->
                             let uu____1911 = str_of_ids shortened in
                             let uu____1912 = str_of_ids matched in
                             let uu____1913 = str_of_ids stripped_ns in
                             (uu____1911, uu____1912, uu____1913, match_len)) in
                  let prepare_candidate uu____1924 =
                    match uu____1924 with
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
                                let uu____2012 =
                                  FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                    dsenv lid in
                                FStar_Option.map
                                  (fun fqn  ->
                                     let uu____2022 =
                                       let uu____2024 =
                                         FStar_List.map
                                           FStar_Ident.id_of_text orig_ns in
                                       FStar_List.append uu____2024
                                         [fqn.FStar_Ident.ident] in
                                     ([], uu____2022, matched_length))
                                  uu____2012
                              else None)) in
                    let case_b_find_matches_in_env uu____2043 =
                      let uu____2050 = env in
                      match uu____2050 with
                      | (dsenv,uu____2058) ->
                          let matches =
                            FStar_List.filter_map
                              (match_lident_against needle)
                              all_lidents_in_env in
                          FStar_All.pipe_right matches
                            (FStar_List.filter
                               (fun uu____2093  ->
                                  match uu____2093 with
                                  | (ns,id,uu____2101) ->
                                      let uu____2106 =
                                        let uu____2108 =
                                          FStar_Ident.lid_of_ids id in
                                        FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                          dsenv uu____2108 in
                                      (match uu____2106 with
                                       | None  -> false
                                       | Some l ->
                                           let uu____2110 =
                                             FStar_Ident.lid_of_ids
                                               (FStar_List.append ns id) in
                                           FStar_Ident.lid_equals l
                                             uu____2110))) in
                    let uu____2111 = FStar_Util.prefix needle in
                    match uu____2111 with
                    | (ns,id) ->
                        let matched_ids =
                          match ns with
                          | [] -> case_b_find_matches_in_env ()
                          | uu____2136 ->
                              let l =
                                FStar_Ident.lid_of_path ns
                                  FStar_Range.dummyRange in
                              let uu____2139 =
                                FStar_ToSyntax_Env.resolve_module_name
                                  (fst env) l true in
                              (match uu____2139 with
                               | None  -> case_b_find_matches_in_env ()
                               | Some m ->
                                   case_a_find_transitive_includes ns m id) in
                        FStar_All.pipe_right matched_ids
                          (FStar_List.map
                             (fun x  ->
                                let uu____2174 = shorten_namespace x in
                                prepare_candidate uu____2174)) in
                  ((let uu____2180 =
                      FStar_Util.sort_with
                        (fun uu____2196  ->
                           fun uu____2197  ->
                             match (uu____2196, uu____2197) with
                             | ((cd1,ns1,uu____2212),(cd2,ns2,uu____2215)) ->
                                 (match FStar_String.compare cd1 cd2 with
                                  | _0_38 when _0_38 = (Prims.parse_int "0")
                                      -> FStar_String.compare ns1 ns2
                                  | n1 -> n1)) matches in
                    FStar_List.iter
                      (fun uu____2231  ->
                         match uu____2231 with
                         | (candidate,ns,match_len) ->
                             let uu____2238 =
                               FStar_Util.string_of_int match_len in
                             FStar_Util.print3 "%s %s %s \n" uu____2238 ns
                               candidate) uu____2180);
                   FStar_Util.print_string "#done-ok\n";
                   go line_col filename stack curmod env ts)
              | Pop msg ->
                  (pop env msg;
                   (let uu____2242 =
                      match stack with
                      | [] ->
                          (FStar_Util.print_error "too many pops";
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd1::tl1 -> (hd1, tl1) in
                    match uu____2242 with
                    | ((env1,curmod1),stack1) ->
                        (if
                           (FStar_List.length stack1) =
                             (FStar_List.length ts)
                         then cleanup env1
                         else ();
                         go line_col filename stack1 curmod1 env1 ts)))
              | Push (lax1,l,c) ->
                  let uu____2309 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____2332 =
                        update_deps filename curmod stack env ts in
                      (true, uu____2332)
                    else (false, (stack, env, ts)) in
                  (match uu____2309 with
                   | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
                       let stack2 = (env1, curmod) :: stack1 in
                       let env2 =
                         push env1 lax1 restore_cmd_line_options1 "#push" in
                       go (l, c) filename stack2 curmod env2 ts1)
              | Code (text1,(ok,fail)) ->
                  let fail1 curmod1 env_mark =
                    report_fail ();
                    FStar_Util.print1 "%s\n" fail;
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
                       else fail1 curmod1 env_mark
                   | uu____2412 -> fail1 curmod env_mark)
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    (let uu____2424 =
       let uu____2425 = FStar_Options.codegen () in
       FStar_Option.isSome uu____2425 in
     if uu____2424
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____2428 = deps_of_our_file filename in
     match uu____2428 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____2442 = tc_deps None [] env filenames [] in
         (match uu____2442 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____2458 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____2459 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____2458 uu____2459 in
              let env2 =
                let uu____2463 =
                  FStar_TypeChecker_Env.set_range (snd env1) initial_range in
                ((fst env1), uu____2463) in
              let env3 =
                match maybe_intf with
                | Some intf -> FStar_Universal.load_interface_decls env2 intf
                | None  -> env2 in
              let uu____2470 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ()) in
              if uu____2470
              then
                let uu____2471 =
                  let uu____2472 = FStar_Options.file_list () in
                  FStar_List.hd uu____2472 in
                FStar_SMTEncoding_Solver.with_hints_db uu____2471
                  (fun uu____2475  ->
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack None env3 ts)
              else
                go ((Prims.parse_int "1"), (Prims.parse_int "0")) filename
                  stack None env3 ts))