open Prims
let tc_one_file remaining uenv =
  let uu____26 = uenv  in
  match uu____26 with
  | (dsenv,env) ->
      let uu____40 =
        match remaining with
        | intf::impl::remaining when
            FStar_Universal.needs_interleaving intf impl ->
            let uu____61 =
              FStar_Universal.tc_one_file_and_intf (Some intf) impl dsenv env
               in
            (match uu____61 with
             | (uu____76,dsenv,env) ->
                 (((Some intf), impl), dsenv, env, remaining))
        | intf_or_impl::remaining ->
            let uu____93 =
              FStar_Universal.tc_one_file_and_intf None intf_or_impl dsenv
                env
               in
            (match uu____93 with
             | (uu____108,dsenv,env) ->
                 ((None, intf_or_impl), dsenv, env, remaining))
        | [] -> failwith "Impossible"  in
      (match uu____40 with
       | ((intf,impl),dsenv,env,remaining) ->
           ((intf, impl), (dsenv, env), None, remaining))
  
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
    fun lax  ->
      fun restore_cmd_line_options  ->
        fun msg  ->
          match uu____218 with
          | (dsenv,env) ->
              let env =
                let uu___185_229 = env  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___185_229.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___185_229.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___185_229.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___185_229.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___185_229.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___185_229.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___185_229.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___185_229.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___185_229.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___185_229.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___185_229.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___185_229.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___185_229.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___185_229.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___185_229.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___185_229.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___185_229.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___185_229.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = lax;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___185_229.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___185_229.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___185_229.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___185_229.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___185_229.FStar_TypeChecker_Env.qname_and_index)
                }  in
              let res = FStar_Universal.push_context (dsenv, env) msg  in
              (FStar_Options.push ();
               if restore_cmd_line_options
               then
                 (let _0_822 = FStar_Options.restore_cmd_line_options false
                     in
                  FStar_All.pipe_right _0_822 Prims.ignore)
               else ();
               res)
  
let mark :
  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) ->
    (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)
  =
  fun uu____242  ->
    match uu____242 with
    | (dsenv,env) ->
        let dsenv = FStar_ToSyntax_Env.mark dsenv  in
        let env = FStar_TypeChecker_Env.mark env  in
        (FStar_Options.push (); (dsenv, env))
  
let reset_mark uu____262 =
  match uu____262 with
  | (uu____265,env) ->
      let dsenv = FStar_ToSyntax_Env.reset_mark ()  in
      let env = FStar_TypeChecker_Env.reset_mark env  in
      (FStar_Options.pop (); (dsenv, env))
  
let cleanup uu____278 =
  match uu____278 with
  | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env 
let commit_mark :
  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) ->
    (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)
  =
  fun uu____289  ->
    match uu____289 with
    | (dsenv,env) ->
        let dsenv = FStar_ToSyntax_Env.commit_mark dsenv  in
        let env = FStar_TypeChecker_Env.commit_mark env  in (dsenv, env)
  
let check_frag :
  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) ->
    FStar_Syntax_Syntax.modul Prims.option ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul Prims.option * (FStar_ToSyntax_Env.env *
          FStar_TypeChecker_Env.env) * Prims.int) Prims.option
  =
  fun uu____314  ->
    fun curmod  ->
      fun text  ->
        match uu____314 with
        | (dsenv,env) ->
            (try
               let uu____344 =
                 FStar_Universal.tc_one_fragment curmod dsenv env text  in
               match uu____344 with
               | Some (m,dsenv,env) ->
                   Some
                     (let _0_823 = FStar_Errors.get_err_count ()  in
                      (m, (dsenv, env), _0_823))
               | uu____375 -> None
             with
             | FStar_Errors.Error (msg,r) when
                 Prims.op_Negation (FStar_Options.trace_error ()) ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
             | FStar_Errors.Err msg when
                 Prims.op_Negation (FStar_Options.trace_error ()) ->
                 ((let _0_826 =
                     let _0_825 =
                       let _0_824 = FStar_TypeChecker_Env.get_range env  in
                       (msg, _0_824)  in
                     [_0_825]  in
                   FStar_TypeChecker_Err.add_errors env _0_826);
                  None))
  
let report_fail : Prims.unit -> Prims.unit =
  fun uu____422  ->
    (let _0_827 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right _0_827 Prims.ignore);
    FStar_ST.write FStar_Errors.num_errs (Prims.parse_int "0")
  
type input_chunks =
  | Push of (Prims.bool * Prims.int * Prims.int) 
  | Pop of Prims.string 
  | Code of (Prims.string * (Prims.string * Prims.string)) 
  | Info of (Prims.string * Prims.int * Prims.int) 
let uu___is_Push : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____457 -> false
  
let __proj__Push__item___0 :
  input_chunks -> (Prims.bool * Prims.int * Prims.int) =
  fun projectee  -> match projectee with | Push _0 -> _0 
let uu___is_Pop : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Pop _0 -> true | uu____478 -> false
  
let __proj__Pop__item___0 : input_chunks -> Prims.string =
  fun projectee  -> match projectee with | Pop _0 -> _0 
let uu___is_Code : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Code _0 -> true | uu____494 -> false
  
let __proj__Code__item___0 :
  input_chunks -> (Prims.string * (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Code _0 -> _0 
let uu___is_Info : input_chunks -> Prims.bool =
  fun projectee  ->
    match projectee with | Info _0 -> true | uu____521 -> false
  
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
  let _0_831 = FStar_Util.new_string_builder ()  in
  let _0_830 = FStar_Util.mk_ref None  in
  let _0_829 = FStar_Util.mk_ref []  in
  let _0_828 = FStar_Util.mk_ref None  in
  { chunk = _0_831; stdin = _0_830; buffer = _0_829; log = _0_828 } 
let rec read_chunk : Prims.unit -> input_chunks =
  fun uu____604  ->
    let s = the_interactive_state  in
    let log =
      let uu____609 = FStar_Options.debug_any ()  in
      if uu____609
      then
        let transcript =
          let uu____613 = FStar_ST.read s.log  in
          match uu____613 with
          | Some transcript -> transcript
          | None  ->
              let transcript = FStar_Util.open_file_for_writing "transcript"
                 in
              (FStar_ST.write s.log (Some transcript); transcript)
           in
        fun line  ->
          (FStar_Util.append_to_file transcript line;
           FStar_Util.flush_file transcript)
      else (fun uu____627  -> ())  in
    let stdin =
      let uu____629 = FStar_ST.read s.stdin  in
      match uu____629 with
      | Some i -> i
      | None  ->
          let i = FStar_Util.open_stdin ()  in
          (FStar_ST.write s.stdin (Some i); i)
       in
    let line =
      let uu____641 = FStar_Util.read_line stdin  in
      match uu____641 with
      | None  -> FStar_All.exit (Prims.parse_int "0")
      | Some l -> l  in
    log line;
    (let l = FStar_Util.trim_string line  in
     if FStar_Util.starts_with l "#end"
     then
       let responses =
         match FStar_Util.split l " " with
         | uu____651::ok::fail::[] -> (ok, fail)
         | uu____654 -> ("ok", "fail")  in
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
               FStar_Util.trim_string
                 (FStar_Util.substring_from l (FStar_String.length "#push"))
                in
             let lc =
               match FStar_Util.split lc_lax " " with
               | l::c::"#lax"::[] ->
                   let _0_833 = FStar_Util.int_of_string l  in
                   let _0_832 = FStar_Util.int_of_string c  in
                   (true, _0_833, _0_832)
               | l::c::[] ->
                   let _0_835 = FStar_Util.int_of_string l  in
                   let _0_834 = FStar_Util.int_of_string c  in
                   (false, _0_835, _0_834)
               | uu____678 ->
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
              | uu____682::file::row::col::[] ->
                  (FStar_Util.clear_string_builder s.chunk;
                   Info
                     ((let _0_837 = FStar_Util.int_of_string row  in
                       let _0_836 = FStar_Util.int_of_string col  in
                       (file, _0_837, _0_836))))
              | uu____687 ->
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
  fun uu____696  ->
    let s = the_interactive_state  in
    let uu____698 = FStar_ST.read s.buffer  in
    match uu____698 with
    | [] -> read_chunk ()
    | chunk::chunks -> (FStar_ST.write s.buffer chunks; chunk)
  
let fill_buffer : Prims.unit -> Prims.unit =
  fun uu____712  ->
    let s = the_interactive_state  in
    let _0_841 =
      let _0_840 = FStar_ST.read s.buffer  in
      let _0_839 = let _0_838 = read_chunk ()  in [_0_838]  in
      FStar_List.append _0_840 _0_839  in
    FStar_ST.write s.buffer _0_841
  
let deps_of_our_file :
  Prims.string -> (Prims.string Prims.list * Prims.string Prims.option) =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename]
       in
    let uu____729 =
      FStar_List.partition
        (fun x  ->
           let _0_843 = FStar_Parser_Dep.lowercase_module_name x  in
           let _0_842 = FStar_Parser_Dep.lowercase_module_name filename  in
           _0_843 <> _0_842) deps
       in
    match uu____729 with
    | (deps,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____751 =
                  (Prims.op_Negation (FStar_Parser_Dep.is_interface intf)) ||
                    (Prims.op_Negation
                       (FStar_Parser_Dep.is_implementation impl))
                   in
                if uu____751
                then
                  FStar_Util.print_warning
                    (FStar_Util.format2
                       "Found %s and %s but not an interface + implementation"
                       intf impl)
                else ());
               Some intf)
          | impl::[] -> None
          | uu____754 ->
              (FStar_Util.print_warning
                 (FStar_Util.format1 "Unexpected: ended up with %s"
                    (FStar_String.concat " " same_name));
               None)
           in
        (deps, maybe_intf)
  
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
            | uu____789 ->
                let stack = (env, m) :: stack  in
                let env =
                  let _0_844 = FStar_Options.lax ()  in
                  push env _0_844 true "typecheck_modul"  in
                let uu____800 = tc_one_file remaining env  in
                (match uu____800 with
                 | ((intf,impl),env,modl,remaining) ->
                     let uu____833 =
                       let intf_t =
                         match intf with
                         | Some intf ->
                             Some
                               (FStar_Util.get_file_last_modification_time
                                  intf)
                         | None  -> None  in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl  in
                       (intf_t, impl_t)  in
                     (match uu____833 with
                      | (intf_t,impl_t) ->
                          tc_deps m stack env remaining
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
                 | (Some intf,Some intf_t) ->
                     let intf_mt =
                       FStar_Util.get_file_last_modification_time intf  in
                     FStar_Util.is_before intf_t intf_mt
                 | (None ,None ) -> false
                 | (uu____906,uu____907) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None")
               in
            let rec iterate depnames st env' ts good_stack good_ts =
              let match_dep depnames intf impl =
                match intf with
                | None  ->
                    (match depnames with
                     | dep::depnames' ->
                         if dep = impl
                         then (true, depnames')
                         else (false, depnames)
                     | uu____971 -> (false, depnames))
                | Some intf ->
                    (match depnames with
                     | depintf::dep::depnames' ->
                         if (depintf = intf) && (dep = impl)
                         then (true, depnames')
                         else (false, depnames)
                     | uu____988 -> (false, depnames))
                 in
              let rec pop_tc_and_stack env stack ts =
                match ts with
                | [] -> env
                | uu____1035::ts ->
                    (pop env "";
                     (let uu____1057 =
                        let _0_846 = FStar_List.hd stack  in
                        let _0_845 = FStar_List.tl stack  in (_0_846, _0_845)
                         in
                      match uu____1057 with
                      | ((env,uu____1077),stack) ->
                          pop_tc_and_stack env stack ts))
                 in
              match ts with
              | ts_elt::ts' ->
                  let uu____1111 = ts_elt  in
                  (match uu____1111 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1129 = match_dep depnames intf impl  in
                       (match uu____1129 with
                        | (b,depnames') ->
                            let uu____1140 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t)
                               in
                            if uu____1140
                            then
                              let env =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts
                                 in
                              tc_deps m good_stack env depnames good_ts
                            else
                              (let uu____1152 =
                                 let _0_848 = FStar_List.hd st  in
                                 let _0_847 = FStar_List.tl st  in
                                 (_0_848, _0_847)  in
                               match uu____1152 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts  in
            let uu____1198 = deps_of_our_file filename  in
            match uu____1198 with
            | (filenames,uu____1207) ->
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
              let uu____1258 = shift_chunk ()  in
              match uu____1258 with
              | Info (file,row,col) ->
                  let iopt =
                    FStar_TypeChecker_Common.info_at_pos file row col  in
                  (match iopt with
                   | None  ->
                       let _0_850 = FStar_Util.string_of_int row  in
                       let _0_849 = FStar_Util.string_of_int col  in
                       FStar_Util.print3
                         "No information found at %s:(%s, %s)\n" file _0_850
                         _0_849
                   | Some s -> FStar_Util.print1 "<info>%s</info>/n" s)
              | Pop msg ->
                  (pop env msg;
                   (let uu____1267 =
                      match stack with
                      | [] ->
                          (FStar_Util.print_error "too many pops";
                           FStar_All.exit (Prims.parse_int "1"))
                      | hd::tl -> (hd, tl)  in
                    match uu____1267 with
                    | ((env,curmod),stack) ->
                        (if
                           (FStar_List.length stack) = (FStar_List.length ts)
                         then cleanup env
                         else ();
                         go line_col filename stack curmod env ts)))
              | Push (lax,l,c) ->
                  let uu____1334 =
                    if (FStar_List.length stack) = (FStar_List.length ts)
                    then
                      let _0_851 = update_deps filename curmod stack env ts
                         in
                      (true, _0_851)
                    else (false, (stack, env, ts))  in
                  (match uu____1334 with
                   | (restore_cmd_line_options,(stack,env,ts)) ->
                       let stack = (env, curmod) :: stack  in
                       let env =
                         push env lax restore_cmd_line_options "#push"  in
                       go (l, c) filename stack curmod env ts)
              | Code (text,(ok,fail)) ->
                  let fail curmod env_mark =
                    report_fail ();
                    FStar_Util.print1 "%s\n" fail;
                    (let env = reset_mark env_mark  in
                     go line_col filename stack curmod env ts)
                     in
                  let env_mark = mark env  in
                  let frag =
                    {
                      FStar_Parser_ParseIt.frag_text = text;
                      FStar_Parser_ParseIt.frag_line = (Prims.fst line_col);
                      FStar_Parser_ParseIt.frag_col = (Prims.snd line_col)
                    }  in
                  let res = check_frag env_mark curmod frag  in
                  (match res with
                   | Some (curmod,env,n_errs) ->
                       if n_errs = (Prims.parse_int "0")
                       then
                         (FStar_Util.print1 "\n%s\n" ok;
                          (let env = commit_mark env  in
                           go line_col filename stack curmod env ts))
                       else fail curmod env_mark
                   | uu____1433 -> fail curmod env_mark)
  
let interactive_mode : Prims.string -> Prims.unit =
  fun filename  ->
    (let uu____1445 = FStar_Option.isSome (FStar_Options.codegen ())  in
     if uu____1445
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____1447 = deps_of_our_file filename  in
     match uu____1447 with
     | (filenames,maybe_intf) ->
         let env = tc_prims ()  in
         let uu____1461 = tc_deps None [] env filenames []  in
         (match uu____1461 with
          | (stack,env,ts) ->
              let uu____1476 =
                match maybe_intf with
                | Some intf ->
                    let frag =
                      let _0_852 = FStar_Util.file_get_contents intf  in
                      {
                        FStar_Parser_ParseIt.frag_text = _0_852;
                        FStar_Parser_ParseIt.frag_line =
                          (Prims.parse_int "0");
                        FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
                      }  in
                    let uu____1489 = check_frag env None frag  in
                    (match uu____1489 with
                     | Some (curmod,env,n_errs) ->
                         (if n_errs <> (Prims.parse_int "0")
                          then
                            (FStar_Util.print_warning
                               (FStar_Util.format1
                                  "Found the interface %s but it has errors!"
                                  intf);
                             FStar_All.exit (Prims.parse_int "1"))
                          else ();
                          FStar_Util.print_string
                            "Reminder: fst+fsti in interactive mode is unsound.\n";
                          (curmod, env))
                     | None  ->
                         (FStar_Util.print_warning
                            (FStar_Util.format1
                               "Found the interface %s but could not parse it first!"
                               intf);
                          FStar_All.exit (Prims.parse_int "1")))
                | None  -> (None, env)  in
              (match uu____1476 with
               | (initial_mod,env) ->
                   let uu____1545 =
                     (FStar_Options.record_hints ()) ||
                       (FStar_Options.use_hints ())
                      in
                   if uu____1545
                   then
                     let _0_853 = FStar_List.hd (FStar_Options.file_list ())
                        in
                     FStar_SMTEncoding_Solver.with_hints_db _0_853
                       (fun uu____1546  ->
                          go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                            filename stack initial_mod env ts)
                   else
                     go ((Prims.parse_int "1"), (Prims.parse_int "0"))
                       filename stack initial_mod env ts)))
  