open Prims
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
let (push_decl :
  FStar_Parser_AST.decl -> FStar_Interactive_Ide_Types.query qst) =
  fun d ->
    let pq =
      let uu___ =
        let uu___1 =
          FStar_Compiler_Range.start_of_range d.FStar_Parser_AST.drange in
        FStar_Compiler_Range.line_of_pos uu___1 in
      let uu___1 =
        let uu___2 =
          FStar_Compiler_Range.start_of_range d.FStar_Parser_AST.drange in
        FStar_Compiler_Range.col_of_pos uu___2 in
      {
        FStar_Interactive_Ide_Types.push_kind =
          FStar_Interactive_PushHelper.FullCheck;
        FStar_Interactive_Ide_Types.push_line = uu___;
        FStar_Interactive_Ide_Types.push_column = uu___1;
        FStar_Interactive_Ide_Types.push_peek_only = false;
        FStar_Interactive_Ide_Types.push_code_or_decl =
          (FStar_Pervasives.Inr d)
      } in
    as_query (FStar_Interactive_Ide_Types.Push pq)
let (push_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Interactive_Ide_Types.query Prims.list qst)
  = fun ds -> map push_decl ds
let (pop_entries :
  FStar_Interactive_ReplState.repl_stack_entry_t Prims.list ->
    FStar_Interactive_Ide_Types.query Prims.list qst)
  = fun e -> map (fun uu___ -> as_query FStar_Interactive_Ide_Types.Pop) e
let (response_success :
  FStar_Parser_AST.decl -> FStar_Compiler_Util.json qst) =
  fun d ->
    op_let_Bang get_qid
      (fun uu___ ->
         match uu___ with
         | (q, uu___1) ->
             let contents =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Compiler_Range.json_of_def_range
                       d.FStar_Parser_AST.drange in
                   ("ranges", uu___4) in
                 [uu___3] in
               FStar_Compiler_Util.JsonAssoc uu___2 in
             return
               (FStar_Compiler_Util.JsonAssoc
                  [("kind", (FStar_Compiler_Util.JsonStr "response"));
                  ("query-id", (FStar_Compiler_Util.JsonStr q));
                  ("status", (FStar_Compiler_Util.JsonStr "success"));
                  ("contents", contents)]))
let (inspect_repl_stack :
  FStar_Interactive_ReplState.repl_stack_t ->
    FStar_Parser_AST.decl Prims.list ->
      ((FStar_Parser_AST.decl, FStar_Errors.issue Prims.list)
         FStar_Pervasives.either -> unit)
        -> FStar_Interactive_Ide_Types.query Prims.list qst)
  =
  fun s ->
    fun ds ->
      fun write_full_buffer_fragment_progress ->
        let entries = FStar_Compiler_List.rev s in
        let uu___ =
          FStar_Compiler_Util.prefix_until
            (fun uu___1 ->
               match uu___1 with
               | (uu___2,
                  (FStar_Interactive_ReplState.PushFragment uu___3, uu___4))
                   -> true
               | uu___2 -> false) entries in
        match uu___ with
        | FStar_Pervasives_Native.None ->
            let uu___1 = push_decls ds in
            op_let_Bang uu___1 (fun ds1 -> return ds1)
        | FStar_Pervasives_Native.Some (prefix, first_push, rest) ->
            let entries1 = first_push :: rest in
            let repl_task uu___1 =
              match uu___1 with | (uu___2, (p, uu___3)) -> p in
            let rec matching_prefix entries2 ds1 =
              match (entries2, ds1) with
              | ([], []) -> return []
              | (e::entries3, d::ds2) ->
                  (match repl_task e with
                   | FStar_Interactive_ReplState.Noop ->
                       matching_prefix entries3 (d :: ds2)
                   | FStar_Interactive_ReplState.PushFragment
                       (FStar_Pervasives.Inl frag) ->
                       let uu___1 = pop_entries (e :: entries3) in
                       op_let_Bang uu___1
                         (fun pops ->
                            let uu___2 = push_decls (d :: ds2) in
                            op_let_Bang uu___2
                              (fun pushes ->
                                 return
                                   (FStar_Compiler_List.op_At pops pushes)))
                   | FStar_Interactive_ReplState.PushFragment
                       (FStar_Pervasives.Inr d') ->
                       let uu___1 = FStar_Parser_AST_Comparison.eq_decl d d' in
                       if uu___1
                       then
                         (write_full_buffer_fragment_progress
                            (FStar_Pervasives.Inl d);
                          matching_prefix entries3 ds2)
                       else
                         (let uu___3 = pop_entries (e :: entries3) in
                          op_let_Bang uu___3
                            (fun pops ->
                               let uu___4 = push_decls (d :: ds2) in
                               op_let_Bang uu___4
                                 (fun pushes ->
                                    return
                                      (FStar_Compiler_List.op_At pops pushes)))))
              | ([], ds2) ->
                  let uu___1 = push_decls ds2 in
                  op_let_Bang uu___1 (fun pushes -> return pushes)
              | (es, []) ->
                  let uu___1 = pop_entries es in
                  op_let_Bang uu___1 (fun pops -> return pops) in
            matching_prefix entries1 ds
let (run_full_buffer :
  FStar_Interactive_ReplState.repl_state ->
    Prims.string ->
      Prims.string ->
        ((FStar_Parser_AST.decl, FStar_Errors.issue Prims.list)
           FStar_Pervasives.either -> unit)
          -> FStar_Interactive_Ide_Types.query Prims.list)
  =
  fun st ->
    fun qid1 ->
      fun code ->
        fun write_full_buffer_fragment_progress ->
          let parse_result =
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
            FStar_Parser_ParseIt.parse uu___ in
          let log_syntax_issues err =
            match err with
            | FStar_Pervasives_Native.None -> ()
            | FStar_Pervasives_Native.Some (raw_error, msg, range) ->
                let uu___ = FStar_Errors.lookup raw_error in
                (match uu___ with
                 | (uu___1, uu___2, num) ->
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
                     write_full_buffer_fragment_progress
                       (FStar_Pervasives.Inr [issue])) in
          let qs =
            match parse_result with
            | FStar_Parser_ParseIt.IncrementalFragment
                (decls, uu___, err_opt) ->
                let queries =
                  let uu___1 =
                    let uu___2 =
                      FStar_Compiler_Effect.op_Bang
                        FStar_Interactive_PushHelper.repl_stack in
                    inspect_repl_stack uu___2 decls
                      write_full_buffer_fragment_progress in
                  run_qst uu___1 qid1 in
                (log_syntax_issues err_opt;
                 (let uu___3 = FStar_Options.debug_any () in
                  if uu___3
                  then
                    let uu___4 =
                      let uu___5 =
                        FStar_Compiler_List.map
                          FStar_Interactive_Ide_Types.query_to_string queries in
                      FStar_String.concat "\n" uu___5 in
                    FStar_Compiler_Util.print1 "Generating queries\n%s\n"
                      uu___4
                  else ());
                 queries)
            | FStar_Parser_ParseIt.ParseError err ->
                (log_syntax_issues (FStar_Pervasives_Native.Some err); [])
            | uu___ -> failwith "Unexpected parse result" in
          qs