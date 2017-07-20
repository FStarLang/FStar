open Prims
let tc_one_file :
  Prims.string Prims.list ->
    FStar_Universal.uenv ->
      ((Prims.string FStar_Pervasives_Native.option,Prims.string)
         FStar_Pervasives_Native.tuple2,(FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
                                          FStar_Pervasives_Native.tuple2,
        Prims.string Prims.list) FStar_Pervasives_Native.tuple3
  =
  fun remaining  ->
    fun uenv  ->
      let uu____31 = uenv  in
      match uu____31 with
      | (dsenv,env) ->
          let uu____52 =
            match remaining with
            | intf::impl::remaining1 when
                FStar_Universal.needs_interleaving intf impl ->
                let uu____90 =
                  FStar_Universal.tc_one_file dsenv env
                    (FStar_Pervasives_Native.Some intf) impl
                   in
                (match uu____90 with
                 | (uu____119,dsenv1,env1) ->
                     (((FStar_Pervasives_Native.Some intf), impl), dsenv1,
                       env1, remaining1))
            | intf_or_impl::remaining1 ->
                let uu____148 =
                  FStar_Universal.tc_one_file dsenv env
                    FStar_Pervasives_Native.None intf_or_impl
                   in
                (match uu____148 with
                 | (uu____177,dsenv1,env1) ->
                     ((FStar_Pervasives_Native.None, intf_or_impl), dsenv1,
                       env1, remaining1))
            | [] -> failwith "Impossible"  in
          (match uu____52 with
           | ((intf,impl),dsenv1,env1,remaining1) ->
               ((intf, impl), (dsenv1, env1), remaining1))
  
let tc_prims :
  Prims.unit ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____276  ->
    let uu____277 = FStar_Universal.tc_prims ()  in
    match uu____277 with | (uu____292,dsenv,env) -> (dsenv, env)
  
type env_t =
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t,modul_t) FStar_Pervasives_Native.tuple2 Prims.list
let pop :
  'Auu____321 .
    ('Auu____321,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.string -> Prims.unit
  =
  fun uu____332  ->
    fun msg  ->
      match uu____332 with
      | (uu____338,env) ->
          (FStar_Universal.pop_context env msg; FStar_Options.pop ())
  
let push :
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    Prims.bool ->
      Prims.bool ->
        Prims.string ->
          (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2
  =
  fun uu____361  ->
    fun lax1  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____361 with
          | (dsenv,env) ->
              let env1 =
                let uu___213_376 = env  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___213_376.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___213_376.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___213_376.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___213_376.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___213_376.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___213_376.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___213_376.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___213_376.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___213_376.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___213_376.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___213_376.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___213_376.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___213_376.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___213_376.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___213_376.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___213_376.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___213_376.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___213_376.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = lax1;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___213_376.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___213_376.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___213_376.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___213_376.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___213_376.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___213_376.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___213_376.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___213_376.FStar_TypeChecker_Env.is_native_tactic)
                }  in
              let res = FStar_Universal.push_context (dsenv, env1) msg  in
              (FStar_Options.push ();
               if restore_cmd_line_options1
               then
                 (let uu____384 =
                    FStar_Options.restore_cmd_line_options false  in
                  FStar_All.pipe_right uu____384 FStar_Pervasives.ignore)
               else ();
               res)
  
let mark :
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____397  ->
    match uu____397 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.mark dsenv  in
        let env1 = FStar_TypeChecker_Env.mark env  in
        (FStar_Options.push (); (dsenv1, env1))
  
let reset_mark :
  'Auu____415 .
    ('Auu____415,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____427  ->
    match uu____427 with
    | (uu____432,env) ->
        let dsenv = FStar_ToSyntax_Env.reset_mark ()  in
        let env1 = FStar_TypeChecker_Env.reset_mark env  in
        (FStar_Options.pop (); (dsenv, env1))
  
let cleanup :
  'Auu____441 .
    ('Auu____441,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.unit
  =
  fun uu____449  ->
    match uu____449 with
    | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
  
let commit_mark :
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____467  ->
    match uu____467 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.commit_mark dsenv  in
        let env1 = FStar_TypeChecker_Env.commit_mark env  in (dsenv1, env1)
  
let check_frag :
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
  fun uu____513  ->
    fun curmod  ->
      fun frag  ->
        match uu____513 with
        | (dsenv,env) ->
            (try
               let uu____577 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag  in
               match uu____577 with
               | FStar_Pervasives_Native.Some (m,dsenv1,env1) ->
                   let uu____617 =
                     let uu____630 = FStar_Errors.get_err_count ()  in
                     (m, (dsenv1, env1), uu____630)  in
                   FStar_Pervasives_Native.Some uu____617
               | uu____649 -> FStar_Pervasives_Native.None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____693 = FStar_Options.trace_error ()  in
                 Prims.op_Negation uu____693 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____716 = FStar_Options.trace_error ()  in
                 Prims.op_Negation uu____716 ->
                 ((let uu____718 =
                     let uu____725 =
                       let uu____730 = FStar_TypeChecker_Env.get_range env
                          in
                       (msg, uu____730)  in
                     [uu____725]  in
                   FStar_TypeChecker_Err.add_errors env uu____718);
                  FStar_Pervasives_Native.None))
  
let report_fail : Prims.unit -> Prims.unit =
  fun uu____754  ->
    (let uu____756 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____756 FStar_Pervasives.ignore);
    FStar_Errors.clear ()
  
type input_chunks =
  | Push of (Prims.bool,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 
  | Pop of Prims.string 
  | Code of
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2 
  | Info of
  (Prims.string,Prims.bool,(Prims.string,Prims.int,Prims.int)
                             FStar_Pervasives_Native.tuple3
                             FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3 
  | Completions of Prims.string 
let uu___is_Push : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____822 -> false
  
let __proj__Push__item___0 :
  input_chunks ->
    (Prims.bool,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Push _0 -> _0 
let uu___is_Pop : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____854 -> false
  
let __proj__Pop__item___0 : input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Pop _0 -> _0 
let uu___is_Code : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____876 -> false
  
let __proj__Code__item___0 :
  input_chunks ->
    (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Code _0 -> _0 
let uu___is_Info : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Info _0 -> true | uu____928 -> false
  
let __proj__Info__item___0 :
  input_chunks ->
    (Prims.string,Prims.bool,(Prims.string,Prims.int,Prims.int)
                               FStar_Pervasives_Native.tuple3
                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Info _0 -> _0 
let uu___is_Completions : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Completions _0 -> true | uu____984 -> false
  
let __proj__Completions__item___0 : input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Completions _0 -> _0 
type interactive_state =
  {
  chunk: FStar_Util.string_builder ;
  stdin: FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref ;
  buffer: input_chunks Prims.list FStar_ST.ref ;
  log: FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref }
let __proj__Mkinteractive_state__item__chunk :
  interactive_state -> FStar_Util.string_builder =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__chunk
  
let __proj__Mkinteractive_state__item__stdin :
  interactive_state ->
    FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__stdin
  
let __proj__Mkinteractive_state__item__buffer :
  interactive_state -> input_chunks Prims.list FStar_ST.ref =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__buffer
  
let __proj__Mkinteractive_state__item__log :
  interactive_state ->
    FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { chunk = __fname__chunk; stdin = __fname__stdin;
        buffer = __fname__buffer; log = __fname__log;_} -> __fname__log
  
let the_interactive_state : interactive_state =
  let uu____1137 = FStar_Util.new_string_builder ()  in
  let uu____1138 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let uu____1145 = FStar_Util.mk_ref []  in
  let uu____1152 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  {
    chunk = uu____1137;
    stdin = uu____1138;
    buffer = uu____1145;
    log = uu____1152
  } 
let rec read_chunk : Prims.unit -> input_chunks =
  fun uu____1168  ->
    let s = the_interactive_state  in
    let log1 =
      let uu____1173 = FStar_Options.debug_any ()  in
      if uu____1173
      then
        let transcript =
          let uu____1177 = FStar_ST.read s.log  in
          match uu____1177 with
          | FStar_Pervasives_Native.Some transcript -> transcript
          | FStar_Pervasives_Native.None  ->
              let transcript = FStar_Util.open_file_for_writing "transcript"
                 in
              (FStar_ST.write s.log (FStar_Pervasives_Native.Some transcript);
               transcript)
           in
        fun line  ->
          (FStar_Util.append_to_file transcript line;
           FStar_Util.flush_file transcript)
      else (fun uu____1190  -> ())  in
    let stdin =
      let uu____1192 = FStar_ST.read s.stdin  in
      match uu____1192 with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None  ->
          let i = FStar_Util.open_stdin ()  in
          (FStar_ST.write s.stdin (FStar_Pervasives_Native.Some i); i)
       in
    let line =
      let uu____1203 = FStar_Util.read_line stdin  in
      match uu____1203 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some l -> l  in
    log1 line;
    (let l = FStar_Util.trim_string line  in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____1218::ok::fail4::[] -> (ok, fail4)
         | uu____1221 -> ("ok", "fail")  in
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
               let uu____1235 =
                 FStar_Util.substring_from l (FStar_String.length "#push")
                  in
               FStar_Util.trim_string uu____1235  in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l1::c::"#lax"::[] ->
                   let uu____1251 = FStar_Util.int_of_string l1  in
                   let uu____1252 = FStar_Util.int_of_string c  in
                   (true, uu____1251, uu____1252)
               | l1::c::[] ->
                   let uu____1255 = FStar_Util.int_of_string l1  in
                   let uu____1256 = FStar_Util.int_of_string c  in
                   (false, uu____1255, uu____1256)
               | uu____1257 ->
                   (FStar_Util.print_warning
                      (Prims.strcat
                         "Error locations may be wrong, unrecognized string after #push: "
                         lc_lax);
                    (false, (Prims.parse_int "1"), (Prims.parse_int "0")))
                in
             Push lc))
         else
           if FStar_Util.starts_with l "#info "
           then
             (match FStar_Util.split l " " with
              | uu____1262::symbol::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   Info (symbol, true, FStar_Pervasives_Native.None))
              | uu____1279::symbol::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   (let uu____1285 =
                      let uu____1300 =
                        let uu____1309 =
                          let uu____1316 = FStar_Util.int_of_string row  in
                          let uu____1317 = FStar_Util.int_of_string col  in
                          (file, uu____1316, uu____1317)  in
                        FStar_Pervasives_Native.Some uu____1309  in
                      (symbol, false, uu____1300)  in
                    Info uu____1285))
              | uu____1332 ->
                  (FStar_Util.print_error
                     (Prims.strcat "Unrecognized \"#info\" request: " l);
                   FStar_All.exit (Prims.parse_int "1")))
           else
             if FStar_Util.starts_with l "#completions "
             then
               (match FStar_Util.split l " " with
                | uu____1337::prefix1::"#"::[] ->
                    (FStar_Util.clear_string_builder s.chunk;
                     Completions prefix1)
                | uu____1340 ->
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
  
let shift_chunk : Prims.unit -> input_chunks =
  fun uu____1351  ->
    let s = the_interactive_state  in
    let uu____1353 = FStar_ST.read s.buffer  in
    match uu____1353 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.write s.buffer chunks; chunk)
  
let fill_buffer : Prims.unit -> Prims.unit =
  fun uu____1368  ->
    let s = the_interactive_state  in
    let uu____1370 =
      let uu____1373 = FStar_ST.read s.buffer  in
      let uu____1378 = let uu____1381 = read_chunk ()  in [uu____1381]  in
      FStar_List.append uu____1373 uu____1378  in
    FStar_ST.write s.buffer uu____1370
  
let deps_of_our_file :
  Prims.string ->
    (Prims.string Prims.list,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename]
       in
    let uu____1399 =
      FStar_List.partition
        (fun x  ->
           let uu____1412 = FStar_Parser_Dep.lowercase_module_name x  in
           let uu____1413 = FStar_Parser_Dep.lowercase_module_name filename
              in
           uu____1412 <> uu____1413) deps
       in
    match uu____1399 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____1440 =
                  (let uu____1443 = FStar_Parser_Dep.is_interface intf  in
                   Prims.op_Negation uu____1443) ||
                    (let uu____1445 = FStar_Parser_Dep.is_implementation impl
                        in
                     Prims.op_Negation uu____1445)
                   in
                if uu____1440
                then
                  let uu____1446 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl
                     in
                  FStar_Util.print_warning uu____1446
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____1449 ->
              ((let uu____1453 =
                  FStar_Util.format1 "Unexpected: ended up with %s"
                    (FStar_String.concat " " same_name)
                   in
                FStar_Util.print_warning uu____1453);
               FStar_Pervasives_Native.None)
           in
        (deps1, maybe_intf)
  
type m_timestamps =
  (Prims.string FStar_Pervasives_Native.option,Prims.string,FStar_Util.time
                                                              FStar_Pervasives_Native.option,
    FStar_Util.time) FStar_Pervasives_Native.tuple4 Prims.list
let rec tc_deps :
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
            | uu____1508 ->
                let stack1 = (env, m) :: stack  in
                let env1 =
                  let uu____1527 = FStar_Options.lax ()  in
                  push env uu____1527 true "typecheck_modul"  in
                let uu____1528 = tc_one_file remaining env1  in
                (match uu____1528 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____1579 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____1592 =
                               FStar_Util.get_file_last_modification_time
                                 intf1
                                in
                             FStar_Pervasives_Native.Some uu____1592
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                          in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl  in
                       (intf_t, impl_t)  in
                     (match uu____1579 with
                      | (intf_t,impl_t) ->
                          tc_deps m stack1 env2 remaining1
                            ((intf, impl, intf_t, impl_t) :: ts)))
  
let update_deps :
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
              let impl_mt = FStar_Util.get_file_last_modification_time impl
                 in
              (FStar_Util.is_before impl_t impl_mt) ||
                (match (intf, intf_t) with
                 | (FStar_Pervasives_Native.Some
                    intf1,FStar_Pervasives_Native.Some intf_t1) ->
                     let intf_mt =
                       FStar_Util.get_file_last_modification_time intf1  in
                     FStar_Util.is_before intf_t1 intf_mt
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> false
                 | (uu____1696,uu____1697) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None")
               in
            let rec iterate depnames st env' ts1 good_stack good_ts =
              let match_dep depnames1 intf impl =
                match intf with
                | FStar_Pervasives_Native.None  ->
                    (match depnames1 with
                     | dep1::depnames' ->
                         if dep1 = impl
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1792 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1820 -> (false, depnames1))
                 in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1903::ts3 ->
                    (pop env1 "";
                     (let uu____1944 =
                        let uu____1959 = FStar_List.hd stack  in
                        let uu____1968 = FStar_List.tl stack  in
                        (uu____1959, uu____1968)  in
                      match uu____1944 with
                      | ((env2,uu____1994),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3))
                 in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____2058 = ts_elt  in
                  (match uu____2058 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____2089 = match_dep depnames intf impl  in
                       (match uu____2089 with
                        | (b,depnames') ->
                            let uu____2108 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t)
                               in
                            if uu____2108
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1
                                 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____2129 =
                                 let uu____2144 = FStar_List.hd st  in
                                 let uu____2153 = FStar_List.tl st  in
                                 (uu____2144, uu____2153)  in
                               match uu____2129 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts  in
            let uu____2230 = deps_of_our_file filename  in
            match uu____2230 with
            | (filenames,uu____2246) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
  
let format_info :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term ->
        FStar_Range.range ->
          Prims.string FStar_Pervasives_Native.option -> Prims.string
  =
  fun env  ->
    fun name  ->
      fun typ  ->
        fun range  ->
          fun doc1  ->
            let uu____2327 = FStar_Range.string_of_range range  in
            let uu____2328 =
              FStar_TypeChecker_Normalize.term_to_string env typ  in
            let uu____2329 =
              match doc1 with
              | FStar_Pervasives_Native.Some docstring ->
                  FStar_Util.format1 "#doc %s" docstring
              | FStar_Pervasives_Native.None  -> ""  in
            FStar_Util.format4 "(defined at %s) %s: %s%s" uu____2327 name
              uu____2328 uu____2329
  
let rec go :
  (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2 ->
    Prims.string -> stack_t -> modul_t -> env_t -> m_timestamps -> Prims.unit
  =
  fun line_col  ->
    fun filename  ->
      fun stack  ->
        fun curmod  ->
          fun env  ->
            fun ts  ->
              let uu____2363 = shift_chunk ()  in
              match uu____2363 with
              | Info (symbol,fqn_only,pos_opt) ->
                  let uu____2383 = env  in
                  (match uu____2383 with
                   | (dsenv,tcenv) ->
                       let info_at_pos_opt =
                         match pos_opt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some (file,row,col) ->
                             FStar_TypeChecker_Err.info_at_pos
                               (FStar_Pervasives_Native.snd env) file row col
                          in
                       let info_opt =
                         match info_at_pos_opt with
                         | FStar_Pervasives_Native.Some uu____2461 ->
                             info_at_pos_opt
                         | FStar_Pervasives_Native.None  ->
                             if symbol = ""
                             then FStar_Pervasives_Native.None
                             else
                               (let lid =
                                  let uu____2516 =
                                    FStar_List.map FStar_Ident.id_of_text
                                      (FStar_Util.split symbol ".")
                                     in
                                  FStar_Ident.lid_of_ids uu____2516  in
                                let lid1 =
                                  if fqn_only
                                  then lid
                                  else
                                    (let uu____2521 =
                                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                         dsenv lid
                                        in
                                     match uu____2521 with
                                     | FStar_Pervasives_Native.None  -> lid
                                     | FStar_Pervasives_Native.Some lid1 ->
                                         lid1)
                                   in
                                let uu____2525 =
                                  FStar_TypeChecker_Env.try_lookup_lid
                                    (FStar_Pervasives_Native.snd env) lid1
                                   in
                                FStar_All.pipe_right uu____2525
                                  (FStar_Util.map_option
                                     (fun uu____2580  ->
                                        match uu____2580 with
                                        | ((uu____2599,typ),r) ->
                                            ((FStar_Util.Inr lid1), typ, r))))
                          in
                       ((match info_opt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Util.print_string "\n#done-nok\n"
                         | FStar_Pervasives_Native.Some (name_or_lid,typ,rng)
                             ->
                             let uu____2642 =
                               match name_or_lid with
                               | FStar_Util.Inl name ->
                                   (name, FStar_Pervasives_Native.None)
                               | FStar_Util.Inr lid ->
                                   let uu____2659 =
                                     FStar_Ident.string_of_lid lid  in
                                   let uu____2660 =
                                     let uu____2663 =
                                       FStar_ToSyntax_Env.try_lookup_doc
                                         dsenv lid
                                        in
                                     FStar_All.pipe_right uu____2663
                                       (FStar_Util.map_option
                                          FStar_Pervasives_Native.fst)
                                      in
                                   (uu____2659, uu____2660)
                                in
                             (match uu____2642 with
                              | (name,doc1) ->
                                  let uu____2694 =
                                    format_info
                                      (FStar_Pervasives_Native.snd env) name
                                      typ rng doc1
                                     in
                                  FStar_Util.print1 "%s\n#done-ok\n"
                                    uu____2694));
                        go line_col filename stack curmod env ts))
              | Completions search_term ->
                  let rec measure_anchored_match search_term1 candidate =
                    match (search_term1, candidate) with
                    | ([],uu____2731) ->
                        FStar_Pervasives_Native.Some
                          ([], (Prims.parse_int "0"))
                    | (uu____2746,[]) -> FStar_Pervasives_Native.None
                    | (hs::ts1,hc::tc) ->
                        let hc_text = FStar_Ident.text_of_id hc  in
                        if FStar_Util.starts_with hc_text hs
                        then
                          (match ts1 with
                           | [] ->
                               FStar_Pervasives_Native.Some
                                 (candidate, (FStar_String.length hs))
                           | uu____2796 ->
                               let uu____2799 = measure_anchored_match ts1 tc
                                  in
                               FStar_All.pipe_right uu____2799
                                 (FStar_Util.map_option
                                    (fun uu____2839  ->
                                       match uu____2839 with
                                       | (matched,len) ->
                                           ((hc :: matched),
                                             (((FStar_String.length hc_text)
                                                 + (Prims.parse_int "1"))
                                                + len)))))
                        else FStar_Pervasives_Native.None
                     in
                  let rec locate_match needle candidate =
                    let uu____2894 = measure_anchored_match needle candidate
                       in
                    match uu____2894 with
                    | FStar_Pervasives_Native.Some (matched,n1) ->
                        FStar_Pervasives_Native.Some ([], matched, n1)
                    | FStar_Pervasives_Native.None  ->
                        (match candidate with
                         | [] -> FStar_Pervasives_Native.None
                         | hc::tc ->
                             let uu____2973 = locate_match needle tc  in
                             FStar_All.pipe_right uu____2973
                               (FStar_Util.map_option
                                  (fun uu____3034  ->
                                     match uu____3034 with
                                     | (prefix1,matched,len) ->
                                         ((hc :: prefix1), matched, len))))
                     in
                  let str_of_ids ids =
                    let uu____3078 =
                      FStar_List.map FStar_Ident.text_of_id ids  in
                    FStar_Util.concat_l "." uu____3078  in
                  let match_lident_against needle lident =
                    locate_match needle
                      (FStar_List.append lident.FStar_Ident.ns
                         [lident.FStar_Ident.ident])
                     in
                  let shorten_namespace uu____3125 =
                    match uu____3125 with
                    | (prefix1,matched,match_len) ->
                        let naked_match =
                          match matched with
                          | uu____3156::[] -> true
                          | uu____3157 -> false  in
                        let uu____3160 =
                          FStar_ToSyntax_Env.shorten_module_path
                            (FStar_Pervasives_Native.fst env) prefix1
                            naked_match
                           in
                        (match uu____3160 with
                         | (stripped_ns,shortened) ->
                             let uu____3187 = str_of_ids shortened  in
                             let uu____3188 = str_of_ids matched  in
                             let uu____3189 = str_of_ids stripped_ns  in
                             (uu____3187, uu____3188, uu____3189, match_len))
                     in
                  let prepare_candidate uu____3207 =
                    match uu____3207 with
                    | (prefix1,matched,stripped_ns,match_len) ->
                        if prefix1 = ""
                        then (matched, stripped_ns, match_len)
                        else
                          ((Prims.strcat prefix1 (Prims.strcat "." matched)),
                            stripped_ns,
                            (((FStar_String.length prefix1) + match_len) +
                               (Prims.parse_int "1")))
                     in
                  let needle = FStar_Util.split search_term "."  in
                  let all_lidents_in_env =
                    FStar_TypeChecker_Env.lidents
                      (FStar_Pervasives_Native.snd env)
                     in
                  let matches =
                    let case_a_find_transitive_includes orig_ns m id =
                      let dsenv = FStar_Pervasives_Native.fst env  in
                      let exported_names =
                        FStar_ToSyntax_Env.transitive_exported_ids dsenv m
                         in
                      let matched_length =
                        FStar_List.fold_left
                          (fun out  ->
                             fun s  ->
                               ((FStar_String.length s) + out) +
                                 (Prims.parse_int "1"))
                          (FStar_String.length id) orig_ns
                         in
                      FStar_All.pipe_right exported_names
                        (FStar_List.filter_map
                           (fun n1  ->
                              if FStar_Util.starts_with n1 id
                              then
                                let lid =
                                  FStar_Ident.lid_of_ns_and_id
                                    (FStar_Ident.ids_of_lid m)
                                    (FStar_Ident.id_of_text n1)
                                   in
                                let uu____3336 =
                                  FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                    dsenv lid
                                   in
                                FStar_Option.map
                                  (fun fqn  ->
                                     let uu____3352 =
                                       let uu____3355 =
                                         FStar_List.map
                                           FStar_Ident.id_of_text orig_ns
                                          in
                                       FStar_List.append uu____3355
                                         [fqn.FStar_Ident.ident]
                                        in
                                     ([], uu____3352, matched_length))
                                  uu____3336
                              else FStar_Pervasives_Native.None))
                       in
                    let case_b_find_matches_in_env uu____3388 =
                      let uu____3401 = env  in
                      match uu____3401 with
                      | (dsenv,uu____3415) ->
                          let matches =
                            FStar_List.filter_map
                              (match_lident_against needle)
                              all_lidents_in_env
                             in
                          FStar_All.pipe_right matches
                            (FStar_List.filter
                               (fun uu____3478  ->
                                  match uu____3478 with
                                  | (ns,id,uu____3491) ->
                                      let uu____3500 =
                                        let uu____3503 =
                                          FStar_Ident.lid_of_ids id  in
                                        FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                                          dsenv uu____3503
                                         in
                                      (match uu____3500 with
                                       | FStar_Pervasives_Native.None  ->
                                           false
                                       | FStar_Pervasives_Native.Some l ->
                                           let uu____3505 =
                                             FStar_Ident.lid_of_ids
                                               (FStar_List.append ns id)
                                              in
                                           FStar_Ident.lid_equals l
                                             uu____3505)))
                       in
                    let uu____3506 = FStar_Util.prefix needle  in
                    match uu____3506 with
                    | (ns,id) ->
                        let matched_ids =
                          match ns with
                          | [] -> case_b_find_matches_in_env ()
                          | uu____3552 ->
                              let l =
                                FStar_Ident.lid_of_path ns
                                  FStar_Range.dummyRange
                                 in
                              let uu____3556 =
                                FStar_ToSyntax_Env.resolve_module_name
                                  (FStar_Pervasives_Native.fst env) l true
                                 in
                              (match uu____3556 with
                               | FStar_Pervasives_Native.None  ->
                                   case_b_find_matches_in_env ()
                               | FStar_Pervasives_Native.Some m ->
                                   case_a_find_transitive_includes ns m id)
                           in
                        FStar_All.pipe_right matched_ids
                          (FStar_List.map
                             (fun x  ->
                                let uu____3621 = shorten_namespace x  in
                                prepare_candidate uu____3621))
                     in
                  ((let uu____3631 =
                      FStar_Util.sort_with
                        (fun uu____3654  ->
                           fun uu____3655  ->
                             match (uu____3654, uu____3655) with
                             | ((cd1,ns1,uu____3682),(cd2,ns2,uu____3685)) ->
                                 (match FStar_String.compare cd1 cd2 with
                                  | _0_48 when _0_48 = (Prims.parse_int "0")
                                      -> FStar_String.compare ns1 ns2
                                  | n1 -> n1)) matches
                       in
                    FStar_List.iter
                      (fun uu____3710  ->
                         match uu____3710 with
                         | (candidate,ns,match_len) ->
                             let uu____3720 =
                               FStar_Util.string_of_int match_len  in
                             FStar_Util.print3 "%s %s %s \n" uu____3720 ns
                               candidate) uu____3631);
                   FStar_Util.print_string "#done-ok\n";
                   go line_col filename stack curmod env ts)
              | Pop msg ->
                  (pop env msg;
                   (let uu____3724 =
                      match stack with
                      | [] ->
                          (FStar_Util.print_error "too many pops";
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd1::tl1 -> (hd1, tl1)  in
                    match uu____3724 with
                    | ((env1,curmod1),stack1) ->
                        (if
                           (FStar_List.length stack1) =
                             (FStar_List.length ts)
                         then cleanup env1
                         else ();
                         go line_col filename stack1 curmod1 env1 ts)))
              | Push (lax1,l,c) ->
                  let uu____3838 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let uu____3875 =
                        update_deps filename curmod stack env ts  in
                      (true, uu____3875)
                    else (false, (stack, env, ts))  in
                  (match uu____3838 with
                   | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
                       let stack2 = (env1, curmod) :: stack1  in
                       let env2 =
                         push env1 lax1 restore_cmd_line_options1 "#push"  in
                       go (l, c) filename stack2 curmod env2 ts1)
              | Code (text1,(ok,fail4)) ->
                  let fail5 curmod1 env_mark =
                    report_fail ();
                    FStar_Util.print1 "%s\n" fail4;
                    (let env1 = reset_mark env_mark  in
                     go line_col filename stack curmod1 env1 ts)
                     in
                  let env_mark = mark env  in
                  let frag =
                    {
                      FStar_Parser_ParseIt.frag_text = text1;
                      FStar_Parser_ParseIt.frag_line =
                        (FStar_Pervasives_Native.fst line_col);
                      FStar_Parser_ParseIt.frag_col =
                        (FStar_Pervasives_Native.snd line_col)
                    }  in
                  let res = check_frag env_mark curmod (frag, false)  in
                  (match res with
                   | FStar_Pervasives_Native.Some (curmod1,env1,n_errs) ->
                       if n_errs = (Prims.parse_int "0")
                       then
                         (FStar_Util.print1 "\n%s\n" ok;
                          (let env2 = commit_mark env1  in
                           go line_col filename stack curmod1 env2 ts))
                       else fail5 curmod1 env_mark
                   | uu____4005 -> fail5 curmod env_mark)
  
let interactive_mode : Prims.string -> Prims.unit =
  fun filename  ->
    (let uu____4025 =
       let uu____4026 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____4026  in
     if uu____4025
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____4030 = deps_of_our_file filename  in
     match uu____4030 with
     | (filenames,maybe_intf) ->
         let env = tc_prims ()  in
         let uu____4054 =
           tc_deps FStar_Pervasives_Native.None [] env filenames []  in
         (match uu____4054 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____4081 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0")
                   in
                let uu____4082 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range "<input>" uu____4081 uu____4082  in
              let env2 =
                let uu____4088 =
                  FStar_TypeChecker_Env.set_range
                    (FStar_Pervasives_Native.snd env1) initial_range
                   in
                ((FStar_Pervasives_Native.fst env1), uu____4088)  in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2  in
              let uu____4099 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ())
                 in
              if uu____4099
              then
                let uu____4100 =
                  let uu____4101 = FStar_Options.file_list ()  in
                  FStar_List.hd uu____4101  in
                FStar_SMTEncoding_Solver.with_hints_db uu____4100
                  (fun uu____4105  ->
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack FStar_Pervasives_Native.None env3 ts)
              else
                go ((Prims.parse_int "1"), (Prims.parse_int "0")) filename
                  stack FStar_Pervasives_Native.None env3 ts))
  