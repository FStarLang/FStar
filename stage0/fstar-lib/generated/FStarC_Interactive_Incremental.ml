open Prims
type fragment_progress =
  | FullBufferStarted 
  | FragmentStarted of FStarC_Parser_AST.decl 
  | FragmentSuccess of (FStarC_Parser_AST.decl *
  FStarC_Parser_ParseIt.code_fragment *
  FStarC_Interactive_Ide_Types.push_kind) 
  | FragmentFailed of FStarC_Parser_AST.decl 
  | FragmentError of FStarC_Errors.issue Prims.list 
  | FullBufferFinished 
let (uu___is_FullBufferStarted : fragment_progress -> Prims.bool) =
  fun projectee ->
    match projectee with | FullBufferStarted -> true | uu___ -> false
let (uu___is_FragmentStarted : fragment_progress -> Prims.bool) =
  fun projectee ->
    match projectee with | FragmentStarted _0 -> true | uu___ -> false
let (__proj__FragmentStarted__item___0 :
  fragment_progress -> FStarC_Parser_AST.decl) =
  fun projectee -> match projectee with | FragmentStarted _0 -> _0
let (uu___is_FragmentSuccess : fragment_progress -> Prims.bool) =
  fun projectee ->
    match projectee with | FragmentSuccess _0 -> true | uu___ -> false
let (__proj__FragmentSuccess__item___0 :
  fragment_progress ->
    (FStarC_Parser_AST.decl * FStarC_Parser_ParseIt.code_fragment *
      FStarC_Interactive_Ide_Types.push_kind))
  = fun projectee -> match projectee with | FragmentSuccess _0 -> _0
let (uu___is_FragmentFailed : fragment_progress -> Prims.bool) =
  fun projectee ->
    match projectee with | FragmentFailed _0 -> true | uu___ -> false
let (__proj__FragmentFailed__item___0 :
  fragment_progress -> FStarC_Parser_AST.decl) =
  fun projectee -> match projectee with | FragmentFailed _0 -> _0
let (uu___is_FragmentError : fragment_progress -> Prims.bool) =
  fun projectee ->
    match projectee with | FragmentError _0 -> true | uu___ -> false
let (__proj__FragmentError__item___0 :
  fragment_progress -> FStarC_Errors.issue Prims.list) =
  fun projectee -> match projectee with | FragmentError _0 -> _0
let (uu___is_FullBufferFinished : fragment_progress -> Prims.bool) =
  fun projectee ->
    match projectee with | FullBufferFinished -> true | uu___ -> false
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
  FStarC_Interactive_Ide_Types.query' ->
    FStarC_Interactive_Ide_Types.query qst)
  =
  fun q ->
    op_let_Bang next_qid
      (fun uu___ ->
         match uu___ with
         | (qid_prefix, i) ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Compiler_Util.string_of_int i in
                   Prims.strcat "." uu___4 in
                 Prims.strcat qid_prefix uu___3 in
               {
                 FStarC_Interactive_Ide_Types.qq = q;
                 FStarC_Interactive_Ide_Types.qid = uu___2
               } in
             return uu___1)
let (dump_symbols_for_lid :
  FStarC_Ident.lident -> FStarC_Interactive_Ide_Types.query qst) =
  fun l ->
    let r = FStarC_Ident.range_of_lid l in
    let start_pos = FStarC_Compiler_Range_Ops.start_of_range r in
    let end_pos = FStarC_Compiler_Range_Ops.end_of_range r in
    let start_line = FStarC_Compiler_Range_Ops.line_of_pos start_pos in
    let start_col = FStarC_Compiler_Range_Ops.col_of_pos start_pos in
    let end_line = FStarC_Compiler_Range_Ops.line_of_pos end_pos in
    let end_col = FStarC_Compiler_Range_Ops.col_of_pos end_pos in
    let position = ("<input>", start_line, start_col) in
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Ident.string_of_lid l in
        (uu___2, FStarC_Interactive_Ide_Types.LKCode,
          (FStar_Pervasives_Native.Some position),
          ["type"; "documentation"; "defined-at"],
          (FStar_Pervasives_Native.Some
             (FStarC_Json.JsonAssoc
                [("fname", (FStarC_Json.JsonStr "<input>"));
                ("beg",
                  (FStarC_Json.JsonList
                     [FStarC_Json.JsonInt start_line;
                     FStarC_Json.JsonInt start_col]));
                ("end",
                  (FStarC_Json.JsonList
                     [FStarC_Json.JsonInt end_line;
                     FStarC_Json.JsonInt end_col]))]))) in
      FStarC_Interactive_Ide_Types.Lookup uu___1 in
    as_query uu___
let (dump_symbols :
  FStarC_Parser_AST.decl -> FStarC_Interactive_Ide_Types.query Prims.list qst)
  =
  fun d ->
    let ls = FStarC_Parser_AST_Util.lidents_of_decl d in
    map dump_symbols_for_lid ls
let (push_decl :
  FStarC_Interactive_Ide_Types.push_kind ->
    Prims.bool ->
      (fragment_progress -> unit) ->
        (FStarC_Parser_AST.decl * FStarC_Parser_ParseIt.code_fragment) ->
          FStarC_Interactive_Ide_Types.query Prims.list qst)
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
                    FStarC_Compiler_Range_Ops.start_of_range
                      d.FStarC_Parser_AST.drange in
                  FStarC_Compiler_Range_Ops.line_of_pos uu___2 in
                let uu___2 =
                  let uu___3 =
                    FStarC_Compiler_Range_Ops.start_of_range
                      d.FStarC_Parser_AST.drange in
                  FStarC_Compiler_Range_Ops.col_of_pos uu___3 in
                {
                  FStarC_Interactive_Ide_Types.push_kind = push_kind;
                  FStarC_Interactive_Ide_Types.push_line = uu___1;
                  FStarC_Interactive_Ide_Types.push_column = uu___2;
                  FStarC_Interactive_Ide_Types.push_peek_only = false;
                  FStarC_Interactive_Ide_Types.push_code_or_decl =
                    (FStar_Pervasives.Inr ds)
                } in
              let progress st =
                write_full_buffer_fragment_progress (FragmentStarted d);
                ((FStarC_Interactive_Ide_Types.QueryOK, []),
                  (FStar_Pervasives.Inl st)) in
              let uu___1 =
                as_query (FStarC_Interactive_Ide_Types.Callback progress) in
              op_let_Bang uu___1
                (fun cb ->
                   let uu___2 =
                     as_query (FStarC_Interactive_Ide_Types.Push pq) in
                   op_let_Bang uu___2
                     (fun push ->
                        if with_symbols
                        then
                          let uu___3 = dump_symbols d in
                          op_let_Bang uu___3
                            (fun lookups ->
                               return
                                 (FStarC_Compiler_List.op_At [cb; push]
                                    lookups))
                        else return [cb; push]))
let (push_decls :
  FStarC_Interactive_Ide_Types.push_kind ->
    Prims.bool ->
      (fragment_progress -> unit) ->
        (FStarC_Parser_AST.decl * FStarC_Parser_ParseIt.code_fragment)
          Prims.list -> FStarC_Interactive_Ide_Types.query Prims.list qst)
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
            (fun qs -> return (FStarC_Compiler_List.flatten qs))
let (pop_entries :
  FStarC_Interactive_Ide_Types.repl_stack_entry_t Prims.list ->
    FStarC_Interactive_Ide_Types.query Prims.list qst)
  = fun e -> map (fun uu___ -> as_query FStarC_Interactive_Ide_Types.Pop) e
let repl_task :
  'uuuuu 'uuuuu1 'uuuuu2 . ('uuuuu * ('uuuuu1 * 'uuuuu2)) -> 'uuuuu1 =
  fun uu___ -> match uu___ with | (uu___1, (p, uu___2)) -> p
let (inspect_repl_stack :
  FStarC_Interactive_Ide_Types.repl_stack_t ->
    (FStarC_Parser_AST.decl * FStarC_Parser_ParseIt.code_fragment) Prims.list
      ->
      FStarC_Interactive_Ide_Types.push_kind ->
        Prims.bool ->
          (fragment_progress -> unit) ->
            (FStarC_Interactive_Ide_Types.query Prims.list * FStarC_Json.json
              Prims.list) qst)
  =
  fun s ->
    fun ds ->
      fun push_kind ->
        fun with_symbols ->
          fun write_full_buffer_fragment_progress ->
            let entries = FStarC_Compiler_List.rev s in
            let push_decls1 =
              push_decls push_kind with_symbols
                write_full_buffer_fragment_progress in
            let uu___ =
              FStarC_Compiler_Util.prefix_until
                (fun uu___1 ->
                   match uu___1 with
                   | (uu___2,
                      (FStarC_Interactive_Ide_Types.PushFragment uu___3,
                       uu___4)) -> true
                   | uu___2 -> false) entries in
            match uu___ with
            | FStar_Pervasives_Native.None ->
                let uu___1 = push_decls1 ds in
                op_let_Bang uu___1 (fun ds1 -> return (ds1, []))
            | FStar_Pervasives_Native.Some (prefix, first_push, rest) ->
                let entries1 = first_push :: rest in
                let repl_task1 uu___1 =
                  match uu___1 with | (uu___2, (p, uu___3)) -> p in
                let rec matching_prefix accum lookups entries2 ds1 =
                  match (entries2, ds1) with
                  | ([], []) -> return (lookups, accum)
                  | (e::entries3, d::ds2) ->
                      (match repl_task1 e with
                       | FStarC_Interactive_Ide_Types.Noop ->
                           matching_prefix accum lookups entries3 (d :: ds2)
                       | FStarC_Interactive_Ide_Types.PushFragment
                           (FStar_Pervasives.Inl frag, uu___1, uu___2) ->
                           let uu___3 = pop_entries (e :: entries3) in
                           op_let_Bang uu___3
                             (fun pops ->
                                let uu___4 = push_decls1 (d :: ds2) in
                                op_let_Bang uu___4
                                  (fun pushes ->
                                     return
                                       ((FStarC_Compiler_List.op_At lookups
                                           (FStarC_Compiler_List.op_At pops
                                              pushes)), accum)))
                       | FStarC_Interactive_Ide_Types.PushFragment
                           (FStar_Pervasives.Inr d', pk, issues) ->
                           let uu___1 =
                             FStarC_Parser_AST_Util.eq_decl
                               (FStar_Pervasives_Native.fst d) d' in
                           if uu___1
                           then
                             let uu___2 = d in
                             (match uu___2 with
                              | (d1, s1) ->
                                  (write_full_buffer_fragment_progress
                                     (FragmentSuccess (d1, s1, pk));
                                   if with_symbols
                                   then
                                     (let uu___4 = dump_symbols d1 in
                                      op_let_Bang uu___4
                                        (fun lookups' ->
                                           matching_prefix
                                             (FStarC_Compiler_List.op_At
                                                issues accum)
                                             (FStarC_Compiler_List.op_At
                                                lookups' lookups) entries3
                                             ds2))
                                   else
                                     matching_prefix
                                       (FStarC_Compiler_List.op_At issues
                                          accum) lookups entries3 ds2))
                           else
                             (let uu___3 = pop_entries (e :: entries3) in
                              op_let_Bang uu___3
                                (fun pops ->
                                   let uu___4 = push_decls1 (d :: ds2) in
                                   op_let_Bang uu___4
                                     (fun pushes ->
                                        return
                                          ((FStarC_Compiler_List.op_At pops
                                              (FStarC_Compiler_List.op_At
                                                 lookups pushes)), accum)))))
                  | ([], ds2) ->
                      let uu___1 = push_decls1 ds2 in
                      op_let_Bang uu___1
                        (fun pushes ->
                           return
                             ((FStarC_Compiler_List.op_At lookups pushes),
                               accum))
                  | (es, []) ->
                      let uu___1 = pop_entries es in
                      op_let_Bang uu___1
                        (fun pops ->
                           return
                             ((FStarC_Compiler_List.op_At lookups pops),
                               accum)) in
                matching_prefix [] [] entries1 ds
let reload_deps :
  'uuuuu 'uuuuu1 .
    ('uuuuu * (FStarC_Interactive_Ide_Types.repl_task * 'uuuuu1)) Prims.list
      -> FStarC_Interactive_Ide_Types.query Prims.list qst
  =
  fun repl_stack ->
    let pop_until_deps entries =
      let uu___ =
        FStarC_Compiler_Util.prefix_until
          (fun e ->
             match repl_task e with
             | FStarC_Interactive_Ide_Types.PushFragment uu___1 -> false
             | FStarC_Interactive_Ide_Types.Noop -> false
             | uu___1 -> true) entries in
      match uu___ with
      | FStar_Pervasives_Native.None -> return []
      | FStar_Pervasives_Native.Some (prefix, uu___1, uu___2) ->
          let uu___3 = as_query FStarC_Interactive_Ide_Types.Pop in
          op_let_Bang uu___3
            (fun pop ->
               let uu___4 =
                 FStarC_Compiler_List.map (fun uu___5 -> pop) prefix in
               return uu___4) in
    pop_until_deps repl_stack
let (parse_code :
  FStarC_Parser_ParseIt.lang_opts ->
    Prims.string -> FStarC_Parser_ParseIt.parse_result)
  =
  fun lang ->
    fun code ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Compiler_Range_Ops.file_of_range
              FStarC_Interactive_Ide_Types.initial_range in
          let uu___3 =
            let uu___4 =
              FStarC_Compiler_Range_Ops.start_of_range
                FStarC_Interactive_Ide_Types.initial_range in
            FStarC_Compiler_Range_Ops.line_of_pos uu___4 in
          let uu___4 =
            let uu___5 =
              FStarC_Compiler_Range_Ops.start_of_range
                FStarC_Interactive_Ide_Types.initial_range in
            FStarC_Compiler_Range_Ops.col_of_pos uu___5 in
          {
            FStarC_Parser_ParseIt.frag_fname = uu___2;
            FStarC_Parser_ParseIt.frag_text = code;
            FStarC_Parser_ParseIt.frag_line = uu___3;
            FStarC_Parser_ParseIt.frag_col = uu___4
          } in
        FStarC_Parser_ParseIt.Incremental uu___1 in
      FStarC_Parser_ParseIt.parse lang uu___
let (syntax_issue :
  (FStarC_Errors_Codes.error_code * FStarC_Errors_Msg.error_message *
    FStarC_Compiler_Range_Type.range) -> FStarC_Errors.issue)
  =
  fun uu___ ->
    match uu___ with
    | (raw_error, msg, range) ->
        let uu___1 = FStarC_Errors.lookup raw_error in
        (match uu___1 with
         | (uu___2, uu___3, num) ->
             let issue =
               {
                 FStarC_Errors.issue_msg = msg;
                 FStarC_Errors.issue_level = FStarC_Errors.EError;
                 FStarC_Errors.issue_range =
                   (FStar_Pervasives_Native.Some range);
                 FStarC_Errors.issue_number =
                   (FStar_Pervasives_Native.Some num);
                 FStarC_Errors.issue_ctx = []
               } in
             issue)
let (run_full_buffer :
  FStarC_Interactive_Ide_Types.repl_state ->
    Prims.string ->
      Prims.string ->
        FStarC_Interactive_Ide_Types.full_buffer_request_kind ->
          Prims.bool ->
            (fragment_progress -> unit) ->
              (FStarC_Interactive_Ide_Types.query Prims.list *
                FStarC_Json.json Prims.list))
  =
  fun st ->
    fun qid1 ->
      fun code ->
        fun request_type ->
          fun with_symbols ->
            fun write_full_buffer_fragment_progress ->
              let parse_result = parse_code FStar_Pervasives_Native.None code in
              let log_syntax_issues err =
                match err with
                | FStar_Pervasives_Native.None -> ()
                | FStar_Pervasives_Native.Some err1 ->
                    let issue = syntax_issue err1 in
                    write_full_buffer_fragment_progress
                      (FragmentError [issue]) in
              let filter_decls decls =
                match request_type with
                | FStarC_Interactive_Ide_Types.VerifyToPosition
                    (uu___, line, _col) ->
                    FStarC_Compiler_List.filter
                      (fun uu___1 ->
                         match uu___1 with
                         | (d, uu___2) ->
                             let start =
                               FStarC_Compiler_Range_Ops.start_of_range
                                 d.FStarC_Parser_AST.drange in
                             let start_line =
                               FStarC_Compiler_Range_Ops.line_of_pos start in
                             start_line <= line) decls
                | FStarC_Interactive_Ide_Types.LaxToPosition
                    (uu___, line, _col) ->
                    FStarC_Compiler_List.filter
                      (fun uu___1 ->
                         match uu___1 with
                         | (d, uu___2) ->
                             let start =
                               FStarC_Compiler_Range_Ops.start_of_range
                                 d.FStarC_Parser_AST.drange in
                             let start_line =
                               FStarC_Compiler_Range_Ops.line_of_pos start in
                             start_line <= line) decls
                | uu___ -> decls in
              let qs =
                match parse_result with
                | FStarC_Parser_ParseIt.IncrementalFragment
                    (decls, uu___, err_opt) ->
                    ((let uu___2 =
                        FStarC_Compiler_Util.string_of_int
                          (FStarC_Compiler_List.length decls) in
                      FStarC_Compiler_Util.print1 "Parsed %s declarations\n"
                        uu___2);
                     (match (request_type, decls) with
                      | (FStarC_Interactive_Ide_Types.ReloadDeps, d::uu___2)
                          ->
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                FStarC_Compiler_Effect.op_Bang
                                  FStarC_Interactive_PushHelper.repl_stack in
                              reload_deps uu___5 in
                            op_let_Bang uu___4
                              (fun queries ->
                                 let uu___5 =
                                   push_decl
                                     FStarC_Interactive_Ide_Types.FullCheck
                                     with_symbols
                                     write_full_buffer_fragment_progress d in
                                 op_let_Bang uu___5
                                   (fun push_mod ->
                                      return
                                        ((FStarC_Compiler_List.op_At queries
                                            push_mod), []))) in
                          run_qst uu___3 qid1
                      | uu___2 ->
                          let decls1 = filter_decls decls in
                          let push_kind =
                            match request_type with
                            | FStarC_Interactive_Ide_Types.LaxToPosition
                                uu___3 ->
                                FStarC_Interactive_Ide_Types.LaxCheck
                            | FStarC_Interactive_Ide_Types.Lax ->
                                FStarC_Interactive_Ide_Types.LaxCheck
                            | uu___3 ->
                                FStarC_Interactive_Ide_Types.FullCheck in
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                FStarC_Compiler_Effect.op_Bang
                                  FStarC_Interactive_PushHelper.repl_stack in
                              inspect_repl_stack uu___5 decls1 push_kind
                                with_symbols
                                write_full_buffer_fragment_progress in
                            run_qst uu___4 qid1 in
                          (match uu___3 with
                           | (queries, issues) ->
                               (if
                                  request_type <>
                                    FStarC_Interactive_Ide_Types.Cache
                                then log_syntax_issues err_opt
                                else ();
                                (let uu___6 = FStarC_Compiler_Debug.any () in
                                 if uu___6
                                 then
                                   let uu___7 =
                                     let uu___8 =
                                       FStarC_Compiler_List.map
                                         FStarC_Interactive_Ide_Types.query_to_string
                                         queries in
                                     FStarC_Compiler_String.concat "\n"
                                       uu___8 in
                                   FStarC_Compiler_Util.print1
                                     "Generating queries\n%s\n" uu___7
                                 else ());
                                if
                                  request_type <>
                                    FStarC_Interactive_Ide_Types.Cache
                                then (queries, issues)
                                else ([], issues)))))
                | FStarC_Parser_ParseIt.ParseError err ->
                    (if request_type = FStarC_Interactive_Ide_Types.Full
                     then
                       log_syntax_issues (FStar_Pervasives_Native.Some err)
                     else ();
                     ([], []))
                | uu___ -> failwith "Unexpected parse result" in
              qs
let (format_code :
  FStarC_Interactive_Ide_Types.repl_state ->
    Prims.string ->
      (Prims.string, FStarC_Errors.issue Prims.list) FStar_Pervasives.either)
  =
  fun st ->
    fun code ->
      let maybe_lang =
        match st.FStarC_Interactive_Ide_Types.repl_lang with
        | [] -> FStar_Pervasives_Native.None
        | { FStarC_Parser_AST.d = FStarC_Parser_AST.UseLangDecls l;
            FStarC_Parser_AST.drange = uu___;
            FStarC_Parser_AST.quals = uu___1;
            FStarC_Parser_AST.attrs = uu___2;
            FStarC_Parser_AST.interleaved = uu___3;_}::uu___4 ->
            FStar_Pervasives_Native.Some l in
      let parse_result = parse_code maybe_lang code in
      match parse_result with
      | FStarC_Parser_ParseIt.IncrementalFragment
          (decls, comments, FStar_Pervasives_Native.None) ->
          let doc_to_string doc =
            FStarC_Pprint.pretty_string
              (FStarC_Compiler_Util.float_of_string "1.0")
              (Prims.of_int (100)) doc in
          let uu___ =
            FStarC_Compiler_List.fold_left
              (fun uu___1 ->
                 fun uu___2 ->
                   match (uu___1, uu___2) with
                   | ((out, comments1), (d, uu___3)) ->
                       let uu___4 =
                         FStarC_Parser_ToDocument.decl_with_comments_to_document
                           d comments1 in
                       (match uu___4 with
                        | (doc, comments2) ->
                            let uu___5 =
                              let uu___6 = doc_to_string doc in uu___6 :: out in
                            (uu___5, comments2)))
              ([], (FStarC_Compiler_List.rev comments)) decls in
          (match uu___ with
           | (formatted_code_rev, leftover_comments) ->
               let code1 =
                 FStarC_Compiler_String.concat "\n\n"
                   (FStarC_Compiler_List.rev formatted_code_rev) in
               let formatted_code =
                 match leftover_comments with
                 | [] -> code1
                 | uu___1 ->
                     let doc =
                       FStarC_Parser_ToDocument.comments_to_document
                         leftover_comments in
                     let uu___2 =
                       let uu___3 = doc_to_string doc in
                       Prims.strcat "\n\n" uu___3 in
                     Prims.strcat code1 uu___2 in
               FStar_Pervasives.Inl formatted_code)
      | FStarC_Parser_ParseIt.IncrementalFragment
          (uu___, uu___1, FStar_Pervasives_Native.Some err) ->
          let uu___2 = let uu___3 = syntax_issue err in [uu___3] in
          FStar_Pervasives.Inr uu___2
      | FStarC_Parser_ParseIt.ParseError err ->
          let uu___ = let uu___1 = syntax_issue err in [uu___1] in
          FStar_Pervasives.Inr uu___
      | uu___ -> failwith "Unexpected parse result"