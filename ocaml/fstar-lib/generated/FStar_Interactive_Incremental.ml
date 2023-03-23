open Prims
type fragment_progress =
  | FragmentStarted of FStar_Parser_AST.decl 
  | FragmentSuccess of (FStar_Parser_AST.decl *
  FStar_Parser_ParseIt.code_fragment * FStar_Interactive_Ide_Types.push_kind)
  
  | FragmentFailed of FStar_Parser_AST.decl 
  | FragmentError of FStar_Errors.issue Prims.list 
let (uu___is_FragmentStarted : fragment_progress -> Prims.bool) =
  fun projectee ->
    match projectee with | FragmentStarted _0 -> true | uu___ -> false
let (__proj__FragmentStarted__item___0 :
  fragment_progress -> FStar_Parser_AST.decl) =
  fun projectee -> match projectee with | FragmentStarted _0 -> _0
let (uu___is_FragmentSuccess : fragment_progress -> Prims.bool) =
  fun projectee ->
    match projectee with | FragmentSuccess _0 -> true | uu___ -> false
let (__proj__FragmentSuccess__item___0 :
  fragment_progress ->
    (FStar_Parser_AST.decl * FStar_Parser_ParseIt.code_fragment *
      FStar_Interactive_Ide_Types.push_kind))
  = fun projectee -> match projectee with | FragmentSuccess _0 -> _0
let (uu___is_FragmentFailed : fragment_progress -> Prims.bool) =
  fun projectee ->
    match projectee with | FragmentFailed _0 -> true | uu___ -> false
let (__proj__FragmentFailed__item___0 :
  fragment_progress -> FStar_Parser_AST.decl) =
  fun projectee -> match projectee with | FragmentFailed _0 -> _0
let (uu___is_FragmentError : fragment_progress -> Prims.bool) =
  fun projectee ->
    match projectee with | FragmentError _0 -> true | uu___ -> false
let (__proj__FragmentError__item___0 :
  fragment_progress -> FStar_Errors.issue Prims.list) =
  fun projectee -> match projectee with | FragmentError _0 -> _0
type qid = (Prims.string * Prims.int)
type 'a qst = qid -> ('a * qid)
let return : 'a . 'a -> 'a qst = fun x -> fun q -> (x, q)
let op_let_Bang : 'a 'b . 'a qst -> ('a -> 'b qst) -> 'b qst =
  fun f ->
    fun g ->
      fun q ->
        let uu___ = f q in
        match uu___ with | (x, q') -> let uu___1 = g x in uu___1 q'
let run_qst : 'a . 'a qst -> Prims.string -> 'a =
  fun f ->
    fun q ->
      let uu___ = f (q, Prims.int_zero) in FStar_Pervasives_Native.fst uu___
let rec map : 'a 'b . ('a -> 'b qst) -> 'a Prims.list -> 'b Prims.list qst =
  fun f ->
    fun l ->
      match l with
      | [] -> return []
      | hd::tl ->
          let uu___ = f hd in
          op_let_Bang uu___
            (fun hd1 ->
               let uu___1 = map f tl in
               op_let_Bang uu___1 (fun tl1 -> return (hd1 :: tl1)))
let (shift_qid : qid -> Prims.int -> (Prims.string * Prims.int)) =
  fun q ->
    fun i ->
      ((FStar_Pervasives_Native.fst q),
        ((FStar_Pervasives_Native.snd q) + i))
let (next_qid : qid qst) =
  fun q -> let q1 = shift_qid q Prims.int_one in (q1, q1)
let (get_qid : qid qst) = fun q -> (q, q)
let (as_query :
  FStar_Interactive_Ide_Types.query' -> FStar_Interactive_Ide_Types.query qst)
  =
  fun q ->
    op_let_Bang next_qid
      (fun uu___ ->
         match uu___ with
         | (qid_prefix, i) ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_Compiler_Util.string_of_int i in
                   Prims.op_Hat "." uu___4 in
                 Prims.op_Hat qid_prefix uu___3 in
               {
                 FStar_Interactive_Ide_Types.qq = q;
                 FStar_Interactive_Ide_Types.qid = uu___2
               } in
             return uu___1)
let (dump_symbols_for_lid :
  FStar_Ident.lident -> FStar_Interactive_Ide_Types.query qst) =
  fun l ->
    let r = FStar_Ident.range_of_lid l in
    let start_pos = FStar_Compiler_Range.start_of_range r in
    let end_pos = FStar_Compiler_Range.end_of_range r in
    let start_line = FStar_Compiler_Range.line_of_pos start_pos in
    let start_col = FStar_Compiler_Range.col_of_pos start_pos in
    let end_line = FStar_Compiler_Range.line_of_pos end_pos in
    let end_col = FStar_Compiler_Range.col_of_pos end_pos in
    let position = ("<input>", start_line, start_col) in
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Ident.string_of_lid l in
        (uu___2, FStar_Interactive_Ide_Types.LKCode,
          (FStar_Pervasives_Native.Some position),
          ["type"; "documentation"; "defined-at"],
          (FStar_Pervasives_Native.Some
             (FStar_Compiler_Util.JsonAssoc
                [("fname", (FStar_Compiler_Util.JsonStr "<input>"));
                ("beg",
                  (FStar_Compiler_Util.JsonList
                     [FStar_Compiler_Util.JsonInt start_line;
                     FStar_Compiler_Util.JsonInt start_col]));
                ("end",
                  (FStar_Compiler_Util.JsonList
                     [FStar_Compiler_Util.JsonInt end_line;
                     FStar_Compiler_Util.JsonInt end_col]))]))) in
      FStar_Interactive_Ide_Types.Lookup uu___1 in
    as_query uu___
let (dump_symbols :
  FStar_Parser_AST.decl -> FStar_Interactive_Ide_Types.query Prims.list qst)
  =
  fun d ->
    let ls = FStar_Parser_AST_Util.lidents_of_decl d in
    map dump_symbols_for_lid ls
let (push_decl :
  FStar_Interactive_Ide_Types.push_kind ->
    Prims.bool ->
      (fragment_progress -> unit) ->
        (FStar_Parser_AST.decl * FStar_Parser_ParseIt.code_fragment) ->
          FStar_Interactive_Ide_Types.query Prims.list qst)
  =
  fun push_kind ->
    fun with_symbols ->
      fun write_full_buffer_fragment_progress ->
        fun ds ->
          let uu___ = ds in
          match uu___ with
          | (d, s) ->
              let pq =
                let uu___1 =
                  let uu___2 =
                    FStar_Compiler_Range.start_of_range
                      d.FStar_Parser_AST.drange in
                  FStar_Compiler_Range.line_of_pos uu___2 in
                let uu___2 =
                  let uu___3 =
                    FStar_Compiler_Range.start_of_range
                      d.FStar_Parser_AST.drange in
                  FStar_Compiler_Range.col_of_pos uu___3 in
                {
                  FStar_Interactive_Ide_Types.push_kind = push_kind;
                  FStar_Interactive_Ide_Types.push_line = uu___1;
                  FStar_Interactive_Ide_Types.push_column = uu___2;
                  FStar_Interactive_Ide_Types.push_peek_only = false;
                  FStar_Interactive_Ide_Types.push_code_or_decl =
                    (FStar_Pervasives.Inr ds)
                } in
              let progress st =
                write_full_buffer_fragment_progress (FragmentStarted d);
                ((FStar_Interactive_Ide_Types.QueryOK, []),
                  (FStar_Pervasives.Inl st)) in
              let uu___1 =
                as_query (FStar_Interactive_Ide_Types.Callback progress) in
              op_let_Bang uu___1
                (fun cb ->
                   let uu___2 =
                     as_query (FStar_Interactive_Ide_Types.Push pq) in
                   op_let_Bang uu___2
                     (fun push ->
                        if with_symbols
                        then
                          let uu___3 = dump_symbols d in
                          op_let_Bang uu___3
                            (fun lookups ->
                               return
                                 (FStar_Compiler_List.op_At [cb; push]
                                    lookups))
                        else return [cb; push]))
let (push_decls :
  FStar_Interactive_Ide_Types.push_kind ->
    Prims.bool ->
      (fragment_progress -> unit) ->
        (FStar_Parser_AST.decl * FStar_Parser_ParseIt.code_fragment)
          Prims.list -> FStar_Interactive_Ide_Types.query Prims.list qst)
  =
  fun push_kind ->
    fun with_symbols ->
      fun write_full_buffer_fragment_progress ->
        fun ds ->
          let uu___ =
            map
              (push_decl push_kind with_symbols
                 write_full_buffer_fragment_progress) ds in
          op_let_Bang uu___
            (fun qs -> return (FStar_Compiler_List.flatten qs))
let (pop_entries :
  FStar_Interactive_Ide_Types.repl_stack_entry_t Prims.list ->
    FStar_Interactive_Ide_Types.query Prims.list qst)
  = fun e -> map (fun uu___ -> as_query FStar_Interactive_Ide_Types.Pop) e
let repl_task :
  'uuuuu 'uuuuu1 'uuuuu2 . ('uuuuu * ('uuuuu1 * 'uuuuu2)) -> 'uuuuu1 =
  fun uu___ -> match uu___ with | (uu___1, (p, uu___2)) -> p
let (inspect_repl_stack :
  FStar_Interactive_Ide_Types.repl_stack_t ->
    (FStar_Parser_AST.decl * FStar_Parser_ParseIt.code_fragment) Prims.list
      ->
      FStar_Interactive_Ide_Types.push_kind ->
        Prims.bool ->
          (fragment_progress -> unit) ->
            FStar_Interactive_Ide_Types.query Prims.list qst)
  =
  fun s ->
    fun ds ->
      fun push_kind ->
        fun with_symbols ->
          fun write_full_buffer_fragment_progress ->
            let entries = FStar_Compiler_List.rev s in
            let push_decls1 =
              push_decls push_kind with_symbols
                write_full_buffer_fragment_progress in
            let uu___ =
              FStar_Compiler_Util.prefix_until
                (fun uu___1 ->
                   match uu___1 with
                   | (uu___2,
                      (FStar_Interactive_Ide_Types.PushFragment uu___3,
                       uu___4)) -> true
                   | uu___2 -> false) entries in
            match uu___ with
            | FStar_Pervasives_Native.None ->
                let uu___1 = push_decls1 ds in
                op_let_Bang uu___1 (fun ds1 -> return ds1)
            | FStar_Pervasives_Native.Some (prefix, first_push, rest) ->
                let entries1 = first_push :: rest in
                let repl_task1 uu___1 =
                  match uu___1 with | (uu___2, (p, uu___3)) -> p in
                let rec matching_prefix entries2 ds1 =
                  match (entries2, ds1) with
                  | ([], []) -> return []
                  | (e::entries3, d::ds2) ->
                      (match repl_task1 e with
                       | FStar_Interactive_Ide_Types.Noop ->
                           matching_prefix entries3 (d :: ds2)
                       | FStar_Interactive_Ide_Types.PushFragment
                           (FStar_Pervasives.Inl frag, uu___1) ->
                           let uu___2 = pop_entries (e :: entries3) in
                           op_let_Bang uu___2
                             (fun pops ->
                                let uu___3 = push_decls1 (d :: ds2) in
                                op_let_Bang uu___3
                                  (fun pushes ->
                                     return
                                       (FStar_Compiler_List.op_At pops pushes)))
                       | FStar_Interactive_Ide_Types.PushFragment
                           (FStar_Pervasives.Inr d', pk) ->
                           let uu___1 =
                             FStar_Parser_AST_Util.eq_decl
                               (FStar_Pervasives_Native.fst d) d' in
                           if uu___1
                           then
                             let uu___2 = d in
                             (match uu___2 with
                              | (d1, s1) ->
                                  (write_full_buffer_fragment_progress
                                     (FragmentSuccess (d1, s1, pk));
                                   matching_prefix entries3 ds2))
                           else
                             (let uu___3 = pop_entries (e :: entries3) in
                              op_let_Bang uu___3
                                (fun pops ->
                                   let uu___4 = push_decls1 (d :: ds2) in
                                   op_let_Bang uu___4
                                     (fun pushes ->
                                        return
                                          (FStar_Compiler_List.op_At pops
                                             pushes)))))
                  | ([], ds2) ->
                      let uu___1 = push_decls1 ds2 in
                      op_let_Bang uu___1 (fun pushes -> return pushes)
                  | (es, []) ->
                      let uu___1 = pop_entries es in
                      op_let_Bang uu___1 (fun pops -> return pops) in
                matching_prefix entries1 ds
let reload_deps :
  'uuuuu 'uuuuu1 .
    ('uuuuu * (FStar_Interactive_Ide_Types.repl_task * 'uuuuu1)) Prims.list
      -> FStar_Interactive_Ide_Types.query Prims.list qst
  =
  fun repl_stack ->
    let pop_until_deps entries =
      let uu___ =
        FStar_Compiler_Util.prefix_until
          (fun e ->
             match repl_task e with
             | FStar_Interactive_Ide_Types.PushFragment uu___1 -> false
             | FStar_Interactive_Ide_Types.Noop -> false
             | uu___1 -> true) entries in
      match uu___ with
      | FStar_Pervasives_Native.None -> return []
      | FStar_Pervasives_Native.Some (prefix, uu___1, uu___2) ->
          let uu___3 = as_query FStar_Interactive_Ide_Types.Pop in
          op_let_Bang uu___3
            (fun pop ->
               let uu___4 =
                 FStar_Compiler_List.map (fun uu___5 -> pop) prefix in
               return uu___4) in
    pop_until_deps repl_stack
let (parse_code : Prims.string -> FStar_Parser_ParseIt.parse_result) =
  fun code ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_Compiler_Range.file_of_range
            FStar_Interactive_Ide_Types.initial_range in
        let uu___3 =
          let uu___4 =
            FStar_Compiler_Range.start_of_range
              FStar_Interactive_Ide_Types.initial_range in
          FStar_Compiler_Range.line_of_pos uu___4 in
        let uu___4 =
          let uu___5 =
            FStar_Compiler_Range.start_of_range
              FStar_Interactive_Ide_Types.initial_range in
          FStar_Compiler_Range.col_of_pos uu___5 in
        {
          FStar_Parser_ParseIt.frag_fname = uu___2;
          FStar_Parser_ParseIt.frag_text = code;
          FStar_Parser_ParseIt.frag_line = uu___3;
          FStar_Parser_ParseIt.frag_col = uu___4
        } in
      FStar_Parser_ParseIt.Incremental uu___1 in
    FStar_Parser_ParseIt.parse uu___
let (syntax_issue :
  (FStar_Errors_Codes.raw_error * Prims.string * FStar_Compiler_Range.range)
    -> FStar_Errors.issue)
  =
  fun uu___ ->
    match uu___ with
    | (raw_error, msg, range) ->
        let uu___1 = FStar_Errors.lookup raw_error in
        (match uu___1 with
         | (uu___2, uu___3, num) ->
             let issue =
               {
                 FStar_Errors.issue_msg = msg;
                 FStar_Errors.issue_level = FStar_Errors.EError;
                 FStar_Errors.issue_range =
                   (FStar_Pervasives_Native.Some range);
                 FStar_Errors.issue_number =
                   (FStar_Pervasives_Native.Some num);
                 FStar_Errors.issue_ctx = []
               } in
             issue)
let (run_full_buffer :
  FStar_Interactive_Ide_Types.repl_state ->
    Prims.string ->
      Prims.string ->
        FStar_Interactive_Ide_Types.full_buffer_request_kind ->
          (fragment_progress -> unit) ->
            FStar_Interactive_Ide_Types.query Prims.list)
  =
  fun st ->
    fun qid1 ->
      fun code ->
        fun request_type ->
          fun write_full_buffer_fragment_progress ->
            let parse_result = parse_code code in
            let log_syntax_issues err =
              match err with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some err1 ->
                  let issue = syntax_issue err1 in
                  write_full_buffer_fragment_progress (FragmentError [issue]) in
            let filter_decls decls =
              match request_type with
              | FStar_Interactive_Ide_Types.VerifyToPosition
                  (uu___, line, _col) ->
                  FStar_Compiler_List.filter
                    (fun uu___1 ->
                       match uu___1 with
                       | (d, uu___2) ->
                           let start =
                             FStar_Compiler_Range.start_of_range
                               d.FStar_Parser_AST.drange in
                           let start_line =
                             FStar_Compiler_Range.line_of_pos start in
                           start_line <= line) decls
              | FStar_Interactive_Ide_Types.LaxToPosition (uu___, line, _col)
                  ->
                  FStar_Compiler_List.filter
                    (fun uu___1 ->
                       match uu___1 with
                       | (d, uu___2) ->
                           let start =
                             FStar_Compiler_Range.start_of_range
                               d.FStar_Parser_AST.drange in
                           let start_line =
                             FStar_Compiler_Range.line_of_pos start in
                           start_line <= line) decls
              | uu___ -> decls in
            let with_symbols =
              request_type =
                FStar_Interactive_Ide_Types.FullBufferWithSymbols in
            let qs =
              match parse_result with
              | FStar_Parser_ParseIt.IncrementalFragment
                  (decls, uu___, err_opt) ->
                  (match (request_type, decls) with
                   | (FStar_Interactive_Ide_Types.ReloadDeps, d::uu___1) ->
                       let uu___2 =
                         let uu___3 =
                           let uu___4 =
                             FStar_Compiler_Effect.op_Bang
                               FStar_Interactive_PushHelper.repl_stack in
                           reload_deps uu___4 in
                         op_let_Bang uu___3
                           (fun queries ->
                              let uu___4 =
                                push_decl
                                  FStar_Interactive_Ide_Types.FullCheck
                                  with_symbols
                                  write_full_buffer_fragment_progress d in
                              op_let_Bang uu___4
                                (fun push_mod ->
                                   return
                                     (FStar_Compiler_List.op_At queries
                                        push_mod))) in
                       run_qst uu___2 qid1
                   | uu___1 ->
                       let decls1 = filter_decls decls in
                       let push_kind =
                         match request_type with
                         | FStar_Interactive_Ide_Types.LaxToPosition uu___2
                             -> FStar_Interactive_Ide_Types.LaxCheck
                         | FStar_Interactive_Ide_Types.FullBufferWithSymbols
                             -> FStar_Interactive_Ide_Types.LaxCheck
                         | uu___2 -> FStar_Interactive_Ide_Types.FullCheck in
                       let queries =
                         let uu___2 =
                           let uu___3 =
                             FStar_Compiler_Effect.op_Bang
                               FStar_Interactive_PushHelper.repl_stack in
                           inspect_repl_stack uu___3 decls1 push_kind
                             with_symbols write_full_buffer_fragment_progress in
                         run_qst uu___2 qid1 in
                       (if request_type = FStar_Interactive_Ide_Types.Full
                        then log_syntax_issues err_opt
                        else ();
                        (let uu___4 = FStar_Options.debug_any () in
                         if uu___4
                         then
                           let uu___5 =
                             let uu___6 =
                               FStar_Compiler_List.map
                                 FStar_Interactive_Ide_Types.query_to_string
                                 queries in
                             FStar_String.concat "\n" uu___6 in
                           FStar_Compiler_Util.print1
                             "Generating queries\n%s\n" uu___5
                         else ());
                        if request_type <> FStar_Interactive_Ide_Types.Cache
                        then queries
                        else []))
              | FStar_Parser_ParseIt.ParseError err ->
                  (if request_type = FStar_Interactive_Ide_Types.Full
                   then log_syntax_issues (FStar_Pervasives_Native.Some err)
                   else ();
                   [])
              | uu___ -> failwith "Unexpected parse result" in
            qs
let (format_code :
  FStar_Interactive_Ide_Types.repl_state ->
    Prims.string ->
      (Prims.string, FStar_Errors.issue Prims.list) FStar_Pervasives.either)
  =
  fun st ->
    fun code ->
      let parse_result = parse_code code in
      match parse_result with
      | FStar_Parser_ParseIt.IncrementalFragment
          (decls, uu___, FStar_Pervasives_Native.None) ->
          let doc_to_string doc =
            FStar_Pprint.pretty_string
              (FStar_Compiler_Util.float_of_string "1.0")
              (Prims.of_int (100)) doc in
          let formatted_code =
            let uu___1 =
              FStar_Compiler_List.map
                (fun uu___2 ->
                   match uu___2 with
                   | (d, uu___3) ->
                       let uu___4 =
                         FStar_Parser_ToDocument.decl_to_document d in
                       doc_to_string uu___4) decls in
            FStar_Compiler_Effect.op_Bar_Greater uu___1
              (FStar_String.concat "\n\n") in
          FStar_Pervasives.Inl formatted_code
      | FStar_Parser_ParseIt.IncrementalFragment
          (uu___, uu___1, FStar_Pervasives_Native.Some err) ->
          let uu___2 = let uu___3 = syntax_issue err in [uu___3] in
          FStar_Pervasives.Inr uu___2
      | FStar_Parser_ParseIt.ParseError err ->
          let uu___ = let uu___1 = syntax_issue err in [uu___1] in
          FStar_Pervasives.Inr uu___
      | uu___ -> failwith "Unexpected parse result"