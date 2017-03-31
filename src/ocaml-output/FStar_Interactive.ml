open Prims
let tc_one_file remaining uenv =
  let uu____26 = uenv  in
  match uu____26 with
  | (dsenv,env) ->
      let uu____40 =
        match remaining with
        | intf::impl::remaining1 when
            FStar_Universal.needs_interleaving intf impl ->
            let uu____61 =
              FStar_Universal.tc_one_file_and_intf (Some intf) impl dsenv env
               in
            (match uu____61 with
             | (uu____76,dsenv1,env1) ->
                 (((Some intf), impl), dsenv1, env1, remaining1))
        | intf_or_impl::remaining1 ->
            let uu____93 =
              FStar_Universal.tc_one_file_and_intf None intf_or_impl dsenv
                env
               in
            (match uu____93 with
             | (uu____108,dsenv1,env1) ->
                 ((None, intf_or_impl), dsenv1, env1, remaining1))
        | [] -> failwith "Impossible"  in
      (match uu____40 with
       | ((intf,impl),dsenv1,env1,remaining1) ->
           ((intf, impl), (dsenv1, env1), None, remaining1))
  
let tc_prims :
  Prims.unit -> (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) =
  fun uu____165  ->
    let uu____166 = FStar_Universal.tc_prims ()  in
    match uu____166 with | (uu____174,dsenv,env) -> (dsenv, env)
  
type env_t = (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)
type modul_t = FStar_Syntax_Syntax.modul Prims.option
type stack_t = (env_t * modul_t) Prims.list
let pop uu____199 msg =
  match uu____199 with
  | (uu____203,env) ->
      (FStar_Universal.pop_context env msg; FStar_Options.pop ())
  
let push :
  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) ->
    Prims.bool ->
      Prims.bool ->
        Prims.string -> (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)
  =
  fun uu____218  ->
    fun lax1  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____218 with
          | (dsenv,env) ->
              let env1 =
                let uu___184_229 = env  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___184_229.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___184_229.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___184_229.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___184_229.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___184_229.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___184_229.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___184_229.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___184_229.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___184_229.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___184_229.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___184_229.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___184_229.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___184_229.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___184_229.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___184_229.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___184_229.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___184_229.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___184_229.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = lax1;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___184_229.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___184_229.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___184_229.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___184_229.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___184_229.FStar_TypeChecker_Env.qname_and_index)
                }  in
              let res = FStar_Universal.push_context (dsenv, env1) msg  in
              (FStar_Options.push ();
               if restore_cmd_line_options1
               then
                 (let uu____235 =
                    FStar_Options.restore_cmd_line_options false  in
                  FStar_All.pipe_right uu____235 Prims.ignore)
               else ();
               res)
  
let mark :
  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) ->
    (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)
  =
  fun uu____243  ->
    match uu____243 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.mark dsenv  in
        let env1 = FStar_TypeChecker_Env.mark env  in
        (FStar_Options.push (); (dsenv1, env1))
  
let reset_mark uu____263 =
  match uu____263 with
  | (uu____266,env) ->
      let dsenv = FStar_ToSyntax_Env.reset_mark ()  in
      let env1 = FStar_TypeChecker_Env.reset_mark env  in
      (FStar_Options.pop (); (dsenv, env1))
  
let cleanup uu____279 =
  match uu____279 with
  | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env 
let commit_mark :
  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) ->
    (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)
  =
  fun uu____290  ->
    match uu____290 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.commit_mark dsenv  in
        let env1 = FStar_TypeChecker_Env.commit_mark env  in (dsenv1, env1)
  
let check_frag :
  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) ->
    FStar_Syntax_Syntax.modul Prims.option ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul Prims.option * (FStar_ToSyntax_Env.env *
          FStar_TypeChecker_Env.env) * Prims.int) Prims.option
  =
  fun uu____315  ->
    fun curmod  ->
      fun text1  ->
        match uu____315 with
        | (dsenv,env) ->
            (try
               let uu____345 =
                 FStar_Universal.tc_one_fragment curmod dsenv env text1  in
               match uu____345 with
               | Some (m,dsenv1,env1) ->
                   let uu____367 =
                     let uu____374 = FStar_Errors.get_err_count ()  in
                     (m, (dsenv1, env1), uu____374)  in
                   Some uu____367
               | uu____384 -> None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____406 = FStar_Options.trace_error ()  in
                 Prims.op_Negation uu____406 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
             | FStar_Errors.Err msg when
                 let uu____419 = FStar_Options.trace_error ()  in
                 Prims.op_Negation uu____419 ->
                 ((let uu____421 =
                     let uu____425 =
                       let uu____428 = FStar_TypeChecker_Env.get_range env
                          in
                       (msg, uu____428)  in
                     [uu____425]  in
                   FStar_TypeChecker_Err.add_errors env uu____421);
                  None))
  
let report_fail : Prims.unit -> Prims.unit =
  fun uu____441  ->
    (let uu____443 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____443 Prims.ignore);
    FStar_ST.write FStar_Errors.num_errs (Prims.parse_int "0")
  
type input_chunks =
  | Push of (Prims.bool * Prims.int * Prims.int) 
  | Pop of Prims.string 
  | Code of (Prims.string * (Prims.string * Prims.string)) 
  | Info of (Prims.string * Prims.int * Prims.int) 
let uu___is_Push : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____478 -> false
  
let __proj__Push__item___0 :
  input_chunks -> (Prims.bool * Prims.int * Prims.int) =
  fun projectee  -> match projectee with | Push _0 -> _0 
let uu___is_Pop : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____499 -> false
  
let __proj__Pop__item___0 : input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Pop _0 -> _0 
let uu___is_Code : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____515 -> false
  
let __proj__Code__item___0 :
  input_chunks -> (Prims.string * (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Code _0 -> _0 
let uu___is_Info : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Info _0 -> true | uu____542 -> false
  
let __proj__Info__item___0 :
  input_chunks -> (Prims.string * Prims.int * Prims.int) =
  fun projectee  -> match projectee with | Info _0 -> _0 
type interactive_state =
  {
  chunk: FStar_Util.string_builder ;
  stdin: FStar_Util.stream_reader Prims.option FStar_ST.ref ;
  buffer: input_chunks Prims.list FStar_ST.ref ;
  log: FStar_Util.file_handle Prims.option FStar_ST.ref }
let the_interactive_state : interactive_state =
  let uu____614 = FStar_Util.new_string_builder ()  in
  let uu____615 = FStar_Util.mk_ref None  in
  let uu____620 = FStar_Util.mk_ref []  in
  let uu____625 = FStar_Util.mk_ref None  in
  { chunk = uu____614; stdin = uu____615; buffer = uu____620; log = uu____625
  } 
let rec read_chunk : Prims.unit -> input_chunks =
  fun uu____638  ->
    let s = the_interactive_state  in
    let log =
      let uu____643 = FStar_Options.debug_any ()  in
      if uu____643
      then
        let transcript =
          let uu____647 = FStar_ST.read s.log  in
          match uu____647 with
          | Some transcript -> transcript
          | None  ->
              let transcript = FStar_Util.open_file_for_writing "transcript"
                 in
              (FStar_ST.write s.log (Some transcript); transcript)
           in
        fun line  ->
          (FStar_Util.append_to_file transcript line;
           FStar_Util.flush_file transcript)
      else (fun uu____661  -> ())  in
    let stdin =
      let uu____663 = FStar_ST.read s.stdin  in
      match uu____663 with
      | Some i -> i
      | None  ->
          let i = FStar_Util.open_stdin ()  in
          (FStar_ST.write s.stdin (Some i); i)
       in
    let line =
      let uu____675 = FStar_Util.read_line stdin  in
      match uu____675 with
      | None  -> FStar_All.exit (Prims.parse_int "0")
      | Some l -> l  in
    log line;
    (let l = FStar_Util.trim_string line  in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____685::ok::fail1::[] -> (ok, fail1)
         | uu____688 -> ("ok", "fail")  in
       let str = FStar_Util.string_of_string_builder s.chunk  in
       (FStar_Util.clear_string_builder s.chunk; Code (str, responses))
     else
       if FStar_Util.starts_with l "#pop"
       then (FStar_Util.clear_string_builder s.chunk; Pop l)
       else
         if FStar_Util.starts_with l "#push"
         then
           (FStar_Util.clear_string_builder s.chunk;
            (let lc_lax =
               let uu____699 =
                 FStar_Util.substring_from l (FStar_String.length "#push")
                  in
               FStar_Util.trim_string uu____699  in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu____711 = FStar_Util.int_of_string l1  in
                   let uu____712 = FStar_Util.int_of_string c  in
                   (true, uu____711, uu____712)
               | l1::c::[] ->
                   let uu____715 = FStar_Util.int_of_string l1  in
                   let uu____716 = FStar_Util.int_of_string c  in
                   (false, uu____715, uu____716)
               | uu____717 ->
                   (FStar_Util.print_warning
                      (Prims.strcat
                         "Error locations may be wrong, unrecognized string after #push: "
                         lc_lax);
                    (false, (Prims.parse_int "1"), (Prims.parse_int "0")))
                in
             Push lc))
         else
           if FStar_Util.starts_with l "#info"
           then
             (match FStar_Util.split l " " with
              | uu____721::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   (let uu____726 =
                      let uu____730 = FStar_Util.int_of_string row  in
                      let uu____731 = FStar_Util.int_of_string col  in
                      (file, uu____730, uu____731)  in
                    Info uu____726))
              | uu____732 ->
                  (FStar_Util.print_error
                     (Prims.strcat "Unrecognized \"#info\" request: " l);
                   FStar_All.exit (Prims.parse_int "1")))
           else
             if l = "#finish"
             then FStar_All.exit (Prims.parse_int "0")
             else
               (FStar_Util.string_builder_append s.chunk line;
                FStar_Util.string_builder_append s.chunk "\n";
                read_chunk ()))
  
let shift_chunk : Prims.unit -> input_chunks =
  fun uu____741  ->
    let s = the_interactive_state  in
    let uu____743 = FStar_ST.read s.buffer  in
    match uu____743 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.write s.buffer chunks; chunk)
  
let fill_buffer : Prims.unit -> Prims.unit =
  fun uu____757  ->
    let s = the_interactive_state  in
    let uu____759 =
      let uu____761 = FStar_ST.read s.buffer  in
      let uu____766 = let uu____768 = read_chunk ()  in [uu____768]  in
      FStar_List.append uu____761 uu____766  in
    FStar_ST.write s.buffer uu____759
  
let deps_of_our_file :
  Prims.string -> (Prims.string Prims.list * Prims.string Prims.option) =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename]
       in
    let uu____781 =
      FStar_List.partition
        (fun x  ->
           let uu____787 = FStar_Parser_Dep.lowercase_module_name x  in
           let uu____788 = FStar_Parser_Dep.lowercase_module_name filename
              in
           uu____787 <> uu____788) deps
       in
    match uu____781 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____805 =
                  (let uu____806 = FStar_Parser_Dep.is_interface intf  in
                   Prims.op_Negation uu____806) ||
                    (let uu____807 = FStar_Parser_Dep.is_implementation impl
                        in
                     Prims.op_Negation uu____807)
                   in
                if uu____805
                then
                  let uu____808 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl
                     in
                  FStar_Util.print_warning uu____808
                else ());
               Some intf)
          | impl::[] -> None
          | uu____811 ->
              ((let uu____814 =
                  FStar_Util.format1 "Unexpected: ended up with %s"
                    (FStar_String.concat " " same_name)
                   in
                FStar_Util.print_warning uu____814);
               None)
           in
        (deps1, maybe_intf)
  
type m_timestamps =
  (Prims.string Prims.option * Prims.string * FStar_Util.time Prims.option *
    FStar_Util.time) Prims.list
let rec tc_deps :
  modul_t ->
    stack_t ->
      env_t ->
        Prims.string Prims.list ->
          m_timestamps -> (stack_t * env_t * m_timestamps)
  =
  fun m  ->
    fun stack  ->
      fun env  ->
        fun remaining  ->
          fun ts  ->
            match remaining with
            | [] -> (stack, env, ts)
            | uu____847 ->
                let stack1 = (env, m) :: stack  in
                let env1 =
                  let uu____858 = FStar_Options.lax ()  in
                  push env uu____858 true "typecheck_modul"  in
                let uu____859 = tc_one_file remaining env1  in
                (match uu____859 with
                 | ((intf,impl),env2,modl,remaining1) ->
                     let uu____892 =
                       let intf_t =
                         match intf with
                         | Some intf1 ->
                             let uu____900 =
                               FStar_Util.get_file_last_modification_time
                                 intf1
                                in
                             Some uu____900
                         | None  -> None  in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl  in
                       (intf_t, impl_t)  in
                     (match uu____892 with
                      | (intf_t,impl_t) ->
                          tc_deps m stack1 env2 remaining1
                            ((intf, impl, intf_t, impl_t) :: ts)))
  
let update_deps :
  Prims.string ->
    modul_t ->
      stack_t -> env_t -> m_timestamps -> (stack_t * env_t * m_timestamps)
  =
  fun filename  ->
    fun m  ->
      fun stk  ->
        fun env  ->
          fun ts  ->
            let is_stale intf impl intf_t impl_t =
              let impl_mt = FStar_Util.get_file_last_modification_time impl
                 in
              (FStar_Util.is_before impl_t impl_mt) ||
                (match (intf, intf_t) with
                 | (Some intf1,Some intf_t1) ->
                     let intf_mt =
                       FStar_Util.get_file_last_modification_time intf1  in
                     FStar_Util.is_before intf_t1 intf_mt
                 | (None ,None ) -> false
                 | (uu____966,uu____967) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None")
               in
            let rec iterate depnames st env' ts1 good_stack good_ts =
              let match_dep depnames1 intf impl =
                match intf with
                | None  ->
                    (match depnames1 with
                     | dep1::depnames' ->
                         if dep1 = impl
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1031 -> (false, depnames1))
                | Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1048 -> (false, depnames1))
                 in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1095::ts3 ->
                    (pop env1 "";
                     (let uu____1117 =
                        let uu____1125 = FStar_List.hd stack  in
                        let uu____1130 = FStar_List.tl stack  in
                        (uu____1125, uu____1130)  in
                      match uu____1117 with
                      | ((env2,uu____1144),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3))
                 in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1178 = ts_elt  in
                  (match uu____1178 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1196 = match_dep depnames intf impl  in
                       (match uu____1196 with
                        | (b,depnames') ->
                            let uu____1207 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t)
                               in
                            if uu____1207
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1
                                 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____1219 =
                                 let uu____1227 = FStar_List.hd st  in
                                 let uu____1232 = FStar_List.tl st  in
                                 (uu____1227, uu____1232)  in
                               match uu____1219 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts  in
            let uu____1272 = deps_of_our_file filename  in
            match uu____1272 with
            | (filenames,uu____1281) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
  
let rec go :
  (Prims.int * Prims.int) ->
    Prims.string -> stack_t -> modul_t -> env_t -> m_timestamps -> Prims.unit
  =
  fun line_col  ->
    fun filename  ->
      fun stack  ->
        fun curmod  ->
          fun env  ->
            fun ts  ->
              let uu____1332 = shift_chunk ()  in
              match uu____1332 with
              | Info (file,row,col) ->
                  let iopt =
                    FStar_TypeChecker_Common.info_at_pos file row col  in
                  (match iopt with
                   | None  ->
                       let uu____1338 = FStar_Util.string_of_int row  in
                       let uu____1339 = FStar_Util.string_of_int col  in
                       FStar_Util.print3
                         "No information found at %s:(%s, %s)\n" file
                         uu____1338 uu____1339
                   | Some s -> FStar_Util.print1 "<info>%s</info>/n" s)
              | Pop msg ->
                  (pop env msg;
                   (let uu____1343 =
                      match stack with
                      | [] ->
                          (FStar_Util.print_error "too many pops";
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd1::tl1 -> (hd1, tl1)  in
                    match uu____1343 with
                    | ((env1,curmod1),stack1) ->
                        (if
                           (FStar_List.length stack1) =
                             (FStar_List.length ts)
                         then cleanup env1
                         else ();
                         go line_col filename stack1 curmod1 env1 ts)))
              | Push (lax1,l,c) ->
                  let uu____1410 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____1433 =
                        update_deps filename curmod stack env ts  in
                      (true, uu____1433)
                    else (false, (stack, env, ts))  in
                  (match uu____1410 with
                   | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
                       let stack2 = (env1, curmod) :: stack1  in
                       let env2 =
                         push env1 lax1 restore_cmd_line_options1 "#push"  in
                       go (l, c) filename stack2 curmod env2 ts1)
              | Code (text1,(ok,fail1)) ->
                  let fail2 curmod1 env_mark =
                    report_fail ();
                    FStar_Util.print1 "%s\n" fail1;
                    (let env1 = reset_mark env_mark  in
                     go line_col filename stack curmod1 env1 ts)
                     in
                  let env_mark = mark env  in
                  let frag =
                    {
                      FStar_Parser_ParseIt.frag_text = text1;
                      FStar_Parser_ParseIt.frag_line = (Prims.fst line_col);
                      FStar_Parser_ParseIt.frag_col = (Prims.snd line_col)
                    }  in
                  let res = check_frag env_mark curmod frag  in
                  (match res with
                   | Some (curmod1,env1,n_errs) ->
                       if n_errs = (Prims.parse_int "0")
                       then
                         (FStar_Util.print1 "\n%s\n" ok;
                          (let env2 = commit_mark env1  in
                           go line_col filename stack curmod1 env2 ts))
                       else fail2 curmod1 env_mark
                   | uu____1513 -> fail2 curmod env_mark)
  
let interactive_mode : Prims.string -> Prims.unit =
  fun filename  ->
    (let uu____1525 =
       let uu____1526 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____1526  in
     if uu____1525
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____1529 = deps_of_our_file filename  in
     match uu____1529 with
     | (filenames,maybe_intf) ->
         let env = tc_prims ()  in
         let uu____1543 = tc_deps None [] env filenames []  in
         (match uu____1543 with
          | (stack,env1,ts) ->
              let uu____1558 =
                match maybe_intf with
                | Some intf ->
                    let frag =
                      let uu____1571 = FStar_Util.file_get_contents intf  in
                      {
                        FStar_Parser_ParseIt.frag_text = uu____1571;
                        FStar_Parser_ParseIt.frag_line =
                          (Prims.parse_int "0");
                        FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
                      }  in
                    let uu____1572 = check_frag env1 None frag  in
                    (match uu____1572 with
                     | Some (curmod,env2,n_errs) ->
                         (if n_errs <> (Prims.parse_int "0")
                          then
                            ((let uu____1602 =
                                FStar_Util.format1
                                  "Found the interface %s but it has errors!"
                                  intf
                                 in
                              FStar_Util.print_warning uu____1602);
                             FStar_All.exit (Prims.parse_int "1"))
                          else ();
                          FStar_Util.print_string
                            "Reminder: fst+fsti in interactive mode is unsound.\n";
                          (curmod, env2))
                     | None  ->
                         ((let uu____1615 =
                             FStar_Util.format1
                               "Found the interface %s but could not parse it first!"
                               intf
                              in
                           FStar_Util.print_warning uu____1615);
                          FStar_All.exit (Prims.parse_int "1")))
                | None  -> (None, env1)  in
              (match uu____1558 with
               | (initial_mod,env2) ->
                   let uu____1630 =
                     (FStar_Options.record_hints ()) ||
                       (FStar_Options.use_hints ())
                      in
                   if uu____1630
                   then
                     let uu____1631 =
                       let uu____1632 = FStar_Options.file_list ()  in
                       FStar_List.hd uu____1632  in
                     FStar_SMTEncoding_Solver.with_hints_db uu____1631
                       (fun uu____1634  ->
                          go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                            filename stack initial_mod env2 ts)
                   else
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack initial_mod env2 ts)))
  