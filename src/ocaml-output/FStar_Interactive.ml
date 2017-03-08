open Prims
let tc_one_file remaining uenv =
  let uu____26 = uenv in
  match uu____26 with
  | (dsenv,env) ->
      let uu____40 =
        match remaining with
        | intf::impl::remaining when
            FStar_Universal.needs_interleaving intf impl ->
            let uu____61 =
              FStar_Universal.tc_one_file_and_intf (Some intf) impl dsenv env in
            (match uu____61 with
             | (uu____76,dsenv,env) ->
                 (((Some intf), impl), dsenv, env, remaining))
        | intf_or_impl::remaining ->
            let uu____93 =
              FStar_Universal.tc_one_file_and_intf None intf_or_impl dsenv
                env in
            (match uu____93 with
             | (uu____108,dsenv,env) ->
                 ((None, intf_or_impl), dsenv, env, remaining))
        | [] -> failwith "Impossible" in
      (match uu____40 with
       | ((intf,impl),dsenv,env,remaining) ->
           ((intf, impl), (dsenv, env), None, remaining))
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
    fun lax  ->
      fun restore_cmd_line_options  ->
        fun msg  ->
          match uu____218 with
          | (dsenv,env) ->
              let env =
                let uu___183_229 = env in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___183_229.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___183_229.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___183_229.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___183_229.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___183_229.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___183_229.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___183_229.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___183_229.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___183_229.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___183_229.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___183_229.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___183_229.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___183_229.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___183_229.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___183_229.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___183_229.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___183_229.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___183_229.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = lax;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___183_229.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___183_229.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___183_229.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___183_229.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___183_229.FStar_TypeChecker_Env.qname_and_index)
                } in
              let res = FStar_Universal.push_context (dsenv, env) msg in
              (FStar_Options.push ();
               if restore_cmd_line_options
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
        let dsenv = FStar_ToSyntax_Env.mark dsenv in
        let env = FStar_TypeChecker_Env.mark env in
        (FStar_Options.push (); (dsenv, env))
let reset_mark uu____263 =
  match uu____263 with
  | (uu____266,env) ->
      let dsenv = FStar_ToSyntax_Env.reset_mark () in
      let env = FStar_TypeChecker_Env.reset_mark env in
      (FStar_Options.pop (); (dsenv, env))
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
        let dsenv = FStar_ToSyntax_Env.commit_mark dsenv in
        let env = FStar_TypeChecker_Env.commit_mark env in (dsenv, env)
let check_frag:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    FStar_Syntax_Syntax.modul Prims.option ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul Prims.option* (FStar_ToSyntax_Env.env*
          FStar_TypeChecker_Env.env)* Prims.int) Prims.option
  =
  fun uu____315  ->
    fun curmod  ->
      fun text  ->
        match uu____315 with
        | (dsenv,env) ->
            (try
               let uu____345 =
                 FStar_Universal.tc_one_fragment curmod dsenv env text in
               match uu____345 with
               | Some (m,dsenv,env) ->
                   let uu____367 =
                     let uu____374 = FStar_Errors.get_err_count () in
                     (m, (dsenv, env), uu____374) in
                   Some uu____367
               | uu____384 -> None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____406 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____406 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
             | FStar_Errors.Err msg when
                 let uu____419 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____419 ->
                 ((let uu____421 =
                     let uu____425 =
                       let uu____428 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____428) in
                     [uu____425] in
                   FStar_TypeChecker_Err.add_errors env uu____421);
                  None))
let report_fail: Prims.unit -> Prims.unit =
  fun uu____441  ->
    (let uu____443 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____443 Prims.ignore);
    FStar_ST.write FStar_Errors.num_errs (Prims.parse_int "0")
type input_chunks =
  | Push of (Prims.bool* Prims.int* Prims.int)
  | Pop of Prims.string
  | Code of (Prims.string* (Prims.string* Prims.string))
let uu___is_Push: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____472 -> false
let __proj__Push__item___0:
  input_chunks -> (Prims.bool* Prims.int* Prims.int) =
  fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_Pop: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____493 -> false
let __proj__Pop__item___0: input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Pop _0 -> _0
let uu___is_Code: input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____509 -> false
let __proj__Code__item___0:
  input_chunks -> (Prims.string* (Prims.string* Prims.string)) =
  fun projectee  -> match projectee with | Code _0 -> _0
type interactive_state =
  {
  chunk: FStar_Util.string_builder;
  stdin: FStar_Util.stream_reader Prims.option FStar_ST.ref;
  buffer: input_chunks Prims.list FStar_ST.ref;
  log: FStar_Util.file_handle Prims.option FStar_ST.ref;}
let the_interactive_state: interactive_state =
  let uu____584 = FStar_Util.new_string_builder () in
  let uu____585 = FStar_Util.mk_ref None in
  let uu____590 = FStar_Util.mk_ref [] in
  let uu____595 = FStar_Util.mk_ref None in
  { chunk = uu____584; stdin = uu____585; buffer = uu____590; log = uu____595
  }
let rec read_chunk: Prims.unit -> input_chunks =
  fun uu____608  ->
    let s = the_interactive_state in
    let log =
      let uu____613 = FStar_Options.debug_any () in
      if uu____613
      then
        let transcript =
          let uu____617 = FStar_ST.read s.log in
          match uu____617 with
          | Some transcript -> transcript
          | None  ->
              let transcript = FStar_Util.open_file_for_writing "transcript" in
              (FStar_ST.write s.log (Some transcript); transcript) in
        fun line  ->
          (FStar_Util.append_to_file transcript line;
           FStar_Util.flush_file transcript)
      else (fun uu____631  -> ()) in
    let stdin =
      let uu____633 = FStar_ST.read s.stdin in
      match uu____633 with
      | Some i -> i
      | None  ->
          let i = FStar_Util.open_stdin () in
          (FStar_ST.write s.stdin (Some i); i) in
    let line =
      let uu____645 = FStar_Util.read_line stdin in
      match uu____645 with
      | None  -> FStar_All.exit (Prims.parse_int "0")
      | Some l -> l in
    log line;
    (let l = FStar_Util.trim_string line in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____655::ok::fail::[] -> (ok, fail)
         | uu____658 -> ("ok", "fail") in
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
               let uu____669 =
                 FStar_Util.substring_from l (FStar_String.length "#push") in
               FStar_Util.trim_string uu____669 in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l::c::"#lax"::[] ->
                   let uu____681 = FStar_Util.int_of_string l in
                   let uu____682 = FStar_Util.int_of_string c in
                   (true, uu____681, uu____682)
               | l::c::[] ->
                   let uu____685 = FStar_Util.int_of_string l in
                   let uu____686 = FStar_Util.int_of_string c in
                   (false, uu____685, uu____686)
               | uu____687 ->
                   (FStar_Util.print_warning
                      (Prims.strcat
                         "Error locations may be wrong, unrecognized string after #push: "
                         lc_lax);
                    (false, (Prims.parse_int "1"), (Prims.parse_int "0"))) in
             Push lc))
         else
           if l = "#finish"
           then FStar_All.exit (Prims.parse_int "0")
           else
             (FStar_Util.string_builder_append s.chunk line;
              FStar_Util.string_builder_append s.chunk "\n";
              read_chunk ()))
let shift_chunk: Prims.unit -> input_chunks =
  fun uu____696  ->
    let s = the_interactive_state in
    let uu____698 = FStar_ST.read s.buffer in
    match uu____698 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.write s.buffer chunks; chunk)
let fill_buffer: Prims.unit -> Prims.unit =
  fun uu____712  ->
    let s = the_interactive_state in
    let uu____714 =
      let uu____716 = FStar_ST.read s.buffer in
      let uu____721 = let uu____723 = read_chunk () in [uu____723] in
      FStar_List.append uu____716 uu____721 in
    FStar_ST.write s.buffer uu____714
let deps_of_our_file:
  Prims.string -> (Prims.string Prims.list* Prims.string Prims.option) =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename] in
    let uu____736 =
      FStar_List.partition
        (fun x  ->
           let uu____742 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____743 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____742 <> uu____743) deps in
    match uu____736 with
    | (deps,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____760 =
                  (let uu____761 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____761) ||
                    (let uu____762 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____762) in
                if uu____760
                then
                  let uu____763 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____763
                else ());
               Some intf)
          | impl::[] -> None
          | uu____766 ->
              ((let uu____769 =
                  FStar_Util.format1 "Unexpected: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____769);
               None) in
        (deps, maybe_intf)
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
            | uu____802 ->
                let stack = (env, m) :: stack in
                let env =
                  let uu____813 = FStar_Options.lax () in
                  push env uu____813 true "typecheck_modul" in
                let uu____814 = tc_one_file remaining env in
                (match uu____814 with
                 | ((intf,impl),env,modl,remaining) ->
                     let uu____847 =
                       let intf_t =
                         match intf with
                         | Some intf ->
                             let uu____855 =
                               FStar_Util.get_file_last_modification_time
                                 intf in
                             Some uu____855
                         | None  -> None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____847 with
                      | (intf_t,impl_t) ->
                          tc_deps m stack env remaining
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
                 | (Some intf,Some intf_t) ->
                     let intf_mt =
                       FStar_Util.get_file_last_modification_time intf in
                     FStar_Util.is_before intf_t intf_mt
                 | (None ,None ) -> false
                 | (uu____921,uu____922) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None") in
            let rec iterate depnames st env' ts good_stack good_ts =
              let match_dep depnames intf impl =
                match intf with
                | None  ->
                    (match depnames with
                     | dep::depnames' ->
                         if dep = impl
                         then (true, depnames')
                         else (false, depnames)
                     | uu____986 -> (false, depnames))
                | Some intf ->
                    (match depnames with
                     | depintf::dep::depnames' ->
                         if (depintf = intf) && (dep = impl)
                         then (true, depnames')
                         else (false, depnames)
                     | uu____1003 -> (false, depnames)) in
              let rec pop_tc_and_stack env stack ts =
                match ts with
                | [] -> env
                | uu____1050::ts ->
                    (pop env "";
                     (let uu____1072 =
                        let uu____1080 = FStar_List.hd stack in
                        let uu____1085 = FStar_List.tl stack in
                        (uu____1080, uu____1085) in
                      match uu____1072 with
                      | ((env,uu____1099),stack) ->
                          pop_tc_and_stack env stack ts)) in
              match ts with
              | ts_elt::ts' ->
                  let uu____1133 = ts_elt in
                  (match uu____1133 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1151 = match_dep depnames intf impl in
                       (match uu____1151 with
                        | (b,depnames') ->
                            let uu____1162 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1162
                            then
                              let env =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts in
                              tc_deps m good_stack env depnames good_ts
                            else
                              (let uu____1174 =
                                 let uu____1182 = FStar_List.hd st in
                                 let uu____1187 = FStar_List.tl st in
                                 (uu____1182, uu____1187) in
                               match uu____1174 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____1227 = deps_of_our_file filename in
            match uu____1227 with
            | (filenames,uu____1236) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
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
              let uu____1287 = shift_chunk () in
              match uu____1287 with
              | Pop msg ->
                  (pop env msg;
                   (let uu____1290 =
                      match stack with
                      | [] ->
                          (FStar_Util.print_error "too many pops";
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd::tl -> (hd, tl) in
                    match uu____1290 with
                    | ((env,curmod),stack) ->
                        (if
                           (FStar_List.length stack) = (FStar_List.length ts)
                         then cleanup env
                         else ();
                         go line_col filename stack curmod env ts)))
              | Push (lax,l,c) ->
                  let uu____1357 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____1380 =
                        update_deps filename curmod stack env ts in
                      (true, uu____1380)
                    else (false, (stack, env, ts)) in
                  (match uu____1357 with
                   | (restore_cmd_line_options,(stack,env,ts)) ->
                       let stack = (env, curmod) :: stack in
                       let env =
                         push env lax restore_cmd_line_options "#push" in
                       go (l, c) filename stack curmod env ts)
              | Code (text,(ok,fail)) ->
                  let fail curmod env_mark =
                    report_fail ();
                    FStar_Util.print1 "%s\n" fail;
                    (let env = reset_mark env_mark in
                     go line_col filename stack curmod env ts) in
                  let env_mark = mark env in
                  let frag =
                    {
                      FStar_Parser_ParseIt.frag_text = text;
                      FStar_Parser_ParseIt.frag_line = (Prims.fst line_col);
                      FStar_Parser_ParseIt.frag_col = (Prims.snd line_col)
                    } in
                  let res = check_frag env_mark curmod frag in
                  (match res with
                   | Some (curmod,env,n_errs) ->
                       if n_errs = (Prims.parse_int "0")
                       then
                         (FStar_Util.print1 "\n%s\n" ok;
                          (let env = commit_mark env in
                           go line_col filename stack curmod env ts))
                       else fail curmod env_mark
                   | uu____1460 -> fail curmod env_mark)
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    (let uu____1472 =
       let uu____1473 = FStar_Options.codegen () in
       FStar_Option.isSome uu____1473 in
     if uu____1472
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____1476 = deps_of_our_file filename in
     match uu____1476 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____1490 = tc_deps None [] env filenames [] in
         (match uu____1490 with
          | (stack,env,ts) ->
              let uu____1505 =
                match maybe_intf with
                | Some intf ->
                    let frag =
                      let uu____1518 = FStar_Util.file_get_contents intf in
                      {
                        FStar_Parser_ParseIt.frag_text = uu____1518;
                        FStar_Parser_ParseIt.frag_line =
                          (Prims.parse_int "0");
                        FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
                      } in
                    let uu____1519 = check_frag env None frag in
                    (match uu____1519 with
                     | Some (curmod,env,n_errs) ->
                         (if n_errs <> (Prims.parse_int "0")
                          then
                            ((let uu____1549 =
                                FStar_Util.format1
                                  "Found the interface %s but it has errors!"
                                  intf in
                              FStar_Util.print_warning uu____1549);
                             FStar_All.exit (Prims.parse_int "1"))
                          else ();
                          FStar_Util.print_string
                            "Reminder: fst+fsti in interactive mode is unsound.\n";
                          (curmod, env))
                     | None  ->
                         ((let uu____1562 =
                             FStar_Util.format1
                               "Found the interface %s but could not parse it first!"
                               intf in
                           FStar_Util.print_warning uu____1562);
                          FStar_All.exit (Prims.parse_int "1")))
                | None  -> (None, env) in
              (match uu____1505 with
               | (initial_mod,env) ->
                   let uu____1577 =
                     (FStar_Options.record_hints ()) ||
                       (FStar_Options.use_hints ()) in
                   if uu____1577
                   then
                     let uu____1578 =
                       let uu____1579 = FStar_Options.file_list () in
                       FStar_List.hd uu____1579 in
                     FStar_SMTEncoding_Solver.with_hints_db uu____1578
                       (fun uu____1581  ->
                          go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                            filename stack initial_mod env ts)
                   else
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack initial_mod env ts)))