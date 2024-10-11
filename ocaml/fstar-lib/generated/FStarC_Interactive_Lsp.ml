open Prims
let (unpack_lsp_query :
  (Prims.string * FStarC_Json.json) Prims.list ->
    FStarC_Interactive_JsonHelper.lsp_query)
  =
  fun r ->
    let qid =
      let uu___ = FStarC_Interactive_JsonHelper.try_assoc "id" r in
      FStarC_Compiler_Util.map_option
        FStarC_Interactive_JsonHelper.js_str_int uu___ in
    try
      (fun uu___ ->
         match () with
         | () ->
             let method1 =
               let uu___1 = FStarC_Interactive_JsonHelper.assoc "method" r in
               FStarC_Interactive_JsonHelper.js_str uu___1 in
             let uu___1 =
               match method1 with
               | "initialize" ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         FStarC_Interactive_JsonHelper.arg "processId" r in
                       FStarC_Interactive_JsonHelper.js_int uu___4 in
                     let uu___4 =
                       let uu___5 =
                         FStarC_Interactive_JsonHelper.arg "rootUri" r in
                       FStarC_Interactive_JsonHelper.js_str uu___5 in
                     (uu___3, uu___4) in
                   FStarC_Interactive_JsonHelper.Initialize uu___2
               | "initialized" -> FStarC_Interactive_JsonHelper.Initialized
               | "shutdown" -> FStarC_Interactive_JsonHelper.Shutdown
               | "exit" -> FStarC_Interactive_JsonHelper.Exit
               | "$/cancelRequest" ->
                   let uu___2 =
                     let uu___3 = FStarC_Interactive_JsonHelper.arg "id" r in
                     FStarC_Interactive_JsonHelper.js_str_int uu___3 in
                   FStarC_Interactive_JsonHelper.Cancel uu___2
               | "workspace/didChangeWorkspaceFolders" ->
                   let uu___2 =
                     let uu___3 = FStarC_Interactive_JsonHelper.arg "event" r in
                     FStarC_Interactive_JsonHelper.js_wsch_event uu___3 in
                   FStarC_Interactive_JsonHelper.FolderChange uu___2
               | "workspace/didChangeConfiguration" ->
                   FStarC_Interactive_JsonHelper.ChangeConfig
               | "workspace/didChangeWatchedFiles" ->
                   FStarC_Interactive_JsonHelper.ChangeWatch
               | "workspace/symbol" ->
                   let uu___2 =
                     let uu___3 = FStarC_Interactive_JsonHelper.arg "query" r in
                     FStarC_Interactive_JsonHelper.js_str uu___3 in
                   FStarC_Interactive_JsonHelper.Symbol uu___2
               | "workspace/executeCommand" ->
                   let uu___2 =
                     let uu___3 =
                       FStarC_Interactive_JsonHelper.arg "command" r in
                     FStarC_Interactive_JsonHelper.js_str uu___3 in
                   FStarC_Interactive_JsonHelper.ExecCommand uu___2
               | "textDocument/didOpen" ->
                   let uu___2 =
                     let uu___3 =
                       FStarC_Interactive_JsonHelper.arg "textDocument" r in
                     FStarC_Interactive_JsonHelper.js_txdoc_item uu___3 in
                   FStarC_Interactive_JsonHelper.DidOpen uu___2
               | "textDocument/didChange" ->
                   let uu___2 =
                     let uu___3 = FStarC_Interactive_JsonHelper.js_txdoc_id r in
                     let uu___4 =
                       let uu___5 =
                         FStarC_Interactive_JsonHelper.arg "contentChanges" r in
                       FStarC_Interactive_JsonHelper.js_contentch uu___5 in
                     (uu___3, uu___4) in
                   FStarC_Interactive_JsonHelper.DidChange uu___2
               | "textDocument/willSave" ->
                   let uu___2 = FStarC_Interactive_JsonHelper.js_txdoc_id r in
                   FStarC_Interactive_JsonHelper.WillSave uu___2
               | "textDocument/willSaveWaitUntil" ->
                   let uu___2 = FStarC_Interactive_JsonHelper.js_txdoc_id r in
                   FStarC_Interactive_JsonHelper.WillSaveWait uu___2
               | "textDocument/didSave" ->
                   let uu___2 =
                     let uu___3 = FStarC_Interactive_JsonHelper.js_txdoc_id r in
                     let uu___4 =
                       let uu___5 =
                         FStarC_Interactive_JsonHelper.arg "text" r in
                       FStarC_Interactive_JsonHelper.js_str uu___5 in
                     (uu___3, uu___4) in
                   FStarC_Interactive_JsonHelper.DidSave uu___2
               | "textDocument/didClose" ->
                   let uu___2 = FStarC_Interactive_JsonHelper.js_txdoc_id r in
                   FStarC_Interactive_JsonHelper.DidClose uu___2
               | "textDocument/completion" ->
                   let uu___2 =
                     let uu___3 =
                       FStarC_Interactive_JsonHelper.js_txdoc_pos r in
                     let uu___4 =
                       let uu___5 =
                         FStarC_Interactive_JsonHelper.arg "context" r in
                       FStarC_Interactive_JsonHelper.js_compl_context uu___5 in
                     (uu___3, uu___4) in
                   FStarC_Interactive_JsonHelper.Completion uu___2
               | "completionItem/resolve" ->
                   FStarC_Interactive_JsonHelper.Resolve
               | "textDocument/hover" ->
                   let uu___2 = FStarC_Interactive_JsonHelper.js_txdoc_pos r in
                   FStarC_Interactive_JsonHelper.Hover uu___2
               | "textDocument/signatureHelp" ->
                   let uu___2 = FStarC_Interactive_JsonHelper.js_txdoc_pos r in
                   FStarC_Interactive_JsonHelper.SignatureHelp uu___2
               | "textDocument/declaration" ->
                   let uu___2 = FStarC_Interactive_JsonHelper.js_txdoc_pos r in
                   FStarC_Interactive_JsonHelper.Declaration uu___2
               | "textDocument/definition" ->
                   let uu___2 = FStarC_Interactive_JsonHelper.js_txdoc_pos r in
                   FStarC_Interactive_JsonHelper.Definition uu___2
               | "textDocument/typeDefinition" ->
                   let uu___2 = FStarC_Interactive_JsonHelper.js_txdoc_pos r in
                   FStarC_Interactive_JsonHelper.TypeDefinition uu___2
               | "textDocument/implementation" ->
                   let uu___2 = FStarC_Interactive_JsonHelper.js_txdoc_pos r in
                   FStarC_Interactive_JsonHelper.Implementation uu___2
               | "textDocument/references" ->
                   FStarC_Interactive_JsonHelper.References
               | "textDocument/documentHighlight" ->
                   let uu___2 = FStarC_Interactive_JsonHelper.js_txdoc_pos r in
                   FStarC_Interactive_JsonHelper.DocumentHighlight uu___2
               | "textDocument/documentSymbol" ->
                   FStarC_Interactive_JsonHelper.DocumentSymbol
               | "textDocument/codeAction" ->
                   FStarC_Interactive_JsonHelper.CodeAction
               | "textDocument/codeLens" ->
                   FStarC_Interactive_JsonHelper.CodeLens
               | "codeLens/resolve" ->
                   FStarC_Interactive_JsonHelper.CodeLensResolve
               | "textDocument/documentLink" ->
                   FStarC_Interactive_JsonHelper.DocumentLink
               | "documentLink/resolve" ->
                   FStarC_Interactive_JsonHelper.DocumentLinkResolve
               | "textDocument/documentColor" ->
                   FStarC_Interactive_JsonHelper.DocumentColor
               | "textDocument/colorPresentation" ->
                   FStarC_Interactive_JsonHelper.ColorPresentation
               | "textDocument/formatting" ->
                   FStarC_Interactive_JsonHelper.Formatting
               | "textDocument/rangeFormatting" ->
                   FStarC_Interactive_JsonHelper.RangeFormatting
               | "textDocument/onTypeFormatting" ->
                   FStarC_Interactive_JsonHelper.TypeFormatting
               | "textDocument/rename" ->
                   FStarC_Interactive_JsonHelper.Rename
               | "textDocument/prepareRename" ->
                   let uu___2 = FStarC_Interactive_JsonHelper.js_txdoc_pos r in
                   FStarC_Interactive_JsonHelper.PrepareRename uu___2
               | "textDocument/foldingRange" ->
                   FStarC_Interactive_JsonHelper.FoldingRange
               | m ->
                   let uu___2 =
                     FStarC_Compiler_Util.format1 "Unknown method '%s'" m in
                   FStarC_Interactive_JsonHelper.BadProtocolMsg uu___2 in
             {
               FStarC_Interactive_JsonHelper.query_id = qid;
               FStarC_Interactive_JsonHelper.q = uu___1
             }) ()
    with
    | FStarC_Interactive_JsonHelper.MissingKey msg ->
        {
          FStarC_Interactive_JsonHelper.query_id = qid;
          FStarC_Interactive_JsonHelper.q =
            (FStarC_Interactive_JsonHelper.BadProtocolMsg msg)
        }
    | FStarC_Interactive_JsonHelper.UnexpectedJsonType (expected, got) ->
        FStarC_Interactive_JsonHelper.wrap_jsfail qid expected got
let (deserialize_lsp_query :
  FStarC_Json.json -> FStarC_Interactive_JsonHelper.lsp_query) =
  fun js_query ->
    try
      (fun uu___ ->
         match () with
         | () ->
             let uu___1 = FStarC_Interactive_JsonHelper.js_assoc js_query in
             unpack_lsp_query uu___1) ()
    with
    | FStarC_Interactive_JsonHelper.UnexpectedJsonType (expected, got) ->
        FStarC_Interactive_JsonHelper.wrap_jsfail
          FStar_Pervasives_Native.None expected got
let (parse_lsp_query :
  Prims.string -> FStarC_Interactive_JsonHelper.lsp_query) =
  fun query_str ->
    let uu___1 = FStarC_Json.json_of_string query_str in
    match uu___1 with
    | FStar_Pervasives_Native.None ->
        {
          FStarC_Interactive_JsonHelper.query_id =
            FStar_Pervasives_Native.None;
          FStarC_Interactive_JsonHelper.q =
            (FStarC_Interactive_JsonHelper.BadProtocolMsg
               "Json parsing failed")
        }
    | FStar_Pervasives_Native.Some request -> deserialize_lsp_query request
let (repl_state_init :
  Prims.string -> FStarC_Interactive_Ide_Types.repl_state) =
  fun fname ->
    let intial_range =
      let uu___ =
        FStarC_Compiler_Range_Type.mk_pos Prims.int_one Prims.int_zero in
      let uu___1 =
        FStarC_Compiler_Range_Type.mk_pos Prims.int_one Prims.int_zero in
      FStarC_Compiler_Range_Type.mk_range fname uu___ uu___1 in
    let env = FStarC_Universal.init_env FStarC_Parser_Dep.empty_deps in
    let env1 = FStarC_TypeChecker_Env.set_range env intial_range in
    let uu___ = FStarC_Compiler_Util.open_stdin () in
    {
      FStarC_Interactive_Ide_Types.repl_line = Prims.int_one;
      FStarC_Interactive_Ide_Types.repl_column = Prims.int_zero;
      FStarC_Interactive_Ide_Types.repl_fname = fname;
      FStarC_Interactive_Ide_Types.repl_deps_stack = [];
      FStarC_Interactive_Ide_Types.repl_curmod = FStar_Pervasives_Native.None;
      FStarC_Interactive_Ide_Types.repl_env = env1;
      FStarC_Interactive_Ide_Types.repl_stdin = uu___;
      FStarC_Interactive_Ide_Types.repl_names =
        FStarC_Interactive_CompletionTable.empty;
      FStarC_Interactive_Ide_Types.repl_buffered_input_queries = [];
      FStarC_Interactive_Ide_Types.repl_lang = []
    }
type optresponse =
  FStarC_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option
type either_gst_exit =
  (FStarC_Interactive_Ide_Types.grepl_state, Prims.int)
    FStar_Pervasives.either
let (invoke_full_lax :
  FStarC_Interactive_Ide_Types.grepl_state ->
    Prims.string ->
      Prims.string -> Prims.bool -> (optresponse * either_gst_exit))
  =
  fun gst ->
    fun fname ->
      fun text ->
        fun force ->
          let aux uu___ =
            FStarC_Parser_ParseIt.add_vfs_entry fname text;
            (let uu___2 =
               let uu___3 = repl_state_init fname in
               FStarC_Interactive_PushHelper.full_lax text uu___3 in
             match uu___2 with
             | (diag, st') ->
                 let repls =
                   FStarC_Compiler_Util.psmap_add
                     gst.FStarC_Interactive_Ide_Types.grepl_repls fname st' in
                 let diag1 =
                   if FStarC_Compiler_Util.is_some diag
                   then diag
                   else
                     (let uu___4 =
                        FStarC_Interactive_JsonHelper.js_diag_clear fname in
                      FStar_Pervasives_Native.Some uu___4) in
                 (diag1,
                   (FStar_Pervasives.Inl
                      {
                        FStarC_Interactive_Ide_Types.grepl_repls = repls;
                        FStarC_Interactive_Ide_Types.grepl_stdin =
                          (gst.FStarC_Interactive_Ide_Types.grepl_stdin)
                      }))) in
          let uu___ =
            FStarC_Compiler_Util.psmap_try_find
              gst.FStarC_Interactive_Ide_Types.grepl_repls fname in
          match uu___ with
          | FStar_Pervasives_Native.Some uu___1 ->
              if force
              then aux ()
              else (FStar_Pervasives_Native.None, (FStar_Pervasives.Inl gst))
          | FStar_Pervasives_Native.None -> aux ()
let (run_query :
  FStarC_Interactive_Ide_Types.grepl_state ->
    FStarC_Interactive_JsonHelper.lquery -> (optresponse * either_gst_exit))
  =
  fun gst ->
    fun q ->
      match q with
      | FStarC_Interactive_JsonHelper.Initialize (uu___, uu___1) ->
          let uu___2 =
            FStarC_Interactive_JsonHelper.resultResponse
              FStarC_Interactive_JsonHelper.js_servcap in
          (uu___2, (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.Initialized ->
          (FStar_Pervasives_Native.None, (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.Shutdown ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.Exit ->
          (FStar_Pervasives_Native.None,
            (FStar_Pervasives.Inr Prims.int_zero))
      | FStarC_Interactive_JsonHelper.Cancel id ->
          (FStar_Pervasives_Native.None, (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.FolderChange evt ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.ChangeConfig ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.ChangeWatch ->
          (FStar_Pervasives_Native.None, (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.Symbol sym ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.ExecCommand cmd ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.DidOpen
          { FStarC_Interactive_JsonHelper.fname = f;
            FStarC_Interactive_JsonHelper.langId = uu___;
            FStarC_Interactive_JsonHelper.version = uu___1;
            FStarC_Interactive_JsonHelper.text = t;_}
          -> invoke_full_lax gst f t false
      | FStarC_Interactive_JsonHelper.DidChange (txid, content) ->
          (FStarC_Parser_ParseIt.add_vfs_entry txid content;
           (FStar_Pervasives_Native.None, (FStar_Pervasives.Inl gst)))
      | FStarC_Interactive_JsonHelper.WillSave txid ->
          (FStar_Pervasives_Native.None, (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.WillSaveWait txid ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.DidSave (f, t) ->
          invoke_full_lax gst f t true
      | FStarC_Interactive_JsonHelper.DidClose txid ->
          (FStar_Pervasives_Native.None, (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.Completion (txpos, ctx) ->
          let uu___ =
            FStarC_Compiler_Util.psmap_try_find
              gst.FStarC_Interactive_Ide_Types.grepl_repls
              txpos.FStarC_Interactive_JsonHelper.path in
          (match uu___ with
           | FStar_Pervasives_Native.Some st ->
               let uu___1 =
                 FStarC_Interactive_QueryHelper.complookup st txpos in
               (uu___1, (FStar_Pervasives.Inl gst))
           | FStar_Pervasives_Native.None ->
               (FStarC_Interactive_JsonHelper.nullResponse,
                 (FStar_Pervasives.Inl gst)))
      | FStarC_Interactive_JsonHelper.Resolve ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.Hover txpos ->
          let uu___ =
            FStarC_Compiler_Util.psmap_try_find
              gst.FStarC_Interactive_Ide_Types.grepl_repls
              txpos.FStarC_Interactive_JsonHelper.path in
          (match uu___ with
           | FStar_Pervasives_Native.Some st ->
               let uu___1 =
                 FStarC_Interactive_QueryHelper.hoverlookup
                   st.FStarC_Interactive_Ide_Types.repl_env txpos in
               (uu___1, (FStar_Pervasives.Inl gst))
           | FStar_Pervasives_Native.None ->
               (FStarC_Interactive_JsonHelper.nullResponse,
                 (FStar_Pervasives.Inl gst)))
      | FStarC_Interactive_JsonHelper.SignatureHelp txpos ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.Declaration txpos ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.Definition txpos ->
          let uu___ =
            FStarC_Compiler_Util.psmap_try_find
              gst.FStarC_Interactive_Ide_Types.grepl_repls
              txpos.FStarC_Interactive_JsonHelper.path in
          (match uu___ with
           | FStar_Pervasives_Native.Some st ->
               let uu___1 =
                 FStarC_Interactive_QueryHelper.deflookup
                   st.FStarC_Interactive_Ide_Types.repl_env txpos in
               (uu___1, (FStar_Pervasives.Inl gst))
           | FStar_Pervasives_Native.None ->
               (FStarC_Interactive_JsonHelper.nullResponse,
                 (FStar_Pervasives.Inl gst)))
      | FStarC_Interactive_JsonHelper.TypeDefinition txpos ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.Implementation txpos ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.References ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.DocumentHighlight txpos ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.DocumentSymbol ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.CodeAction ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.CodeLens ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.CodeLensResolve ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.DocumentLink ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.DocumentLinkResolve ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.DocumentColor ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.ColorPresentation ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.Formatting ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.RangeFormatting ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.TypeFormatting ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.Rename ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.PrepareRename txpos ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.FoldingRange ->
          (FStarC_Interactive_JsonHelper.nullResponse,
            (FStar_Pervasives.Inl gst))
      | FStarC_Interactive_JsonHelper.BadProtocolMsg msg ->
          let uu___ =
            let uu___1 =
              FStarC_Interactive_JsonHelper.js_resperr
                FStarC_Interactive_JsonHelper.MethodNotFound msg in
            FStarC_Interactive_JsonHelper.errorResponse uu___1 in
          (uu___, (FStar_Pervasives.Inl gst))
let rec (parse_header_len :
  FStarC_Compiler_Util.stream_reader -> Prims.int -> Prims.int) =
  fun stream ->
    fun len ->
      let uu___ = FStarC_Compiler_Util.read_line stream in
      match uu___ with
      | FStar_Pervasives_Native.Some s ->
          if FStarC_Compiler_Util.starts_with s "Content-Length: "
          then
            let uu___1 =
              let uu___2 =
                FStarC_Compiler_Util.substring_from s (Prims.of_int (16)) in
              FStarC_Compiler_Util.safe_int_of_string uu___2 in
            (match uu___1 with
             | FStar_Pervasives_Native.Some new_len ->
                 parse_header_len stream new_len
             | FStar_Pervasives_Native.None ->
                 FStarC_Compiler_Effect.raise
                   FStarC_Interactive_JsonHelper.MalformedHeader)
          else
            if FStarC_Compiler_Util.starts_with s "Content-Type: "
            then parse_header_len stream len
            else
              if s = ""
              then len
              else
                FStarC_Compiler_Effect.raise
                  FStarC_Interactive_JsonHelper.MalformedHeader
      | FStar_Pervasives_Native.None ->
          FStarC_Compiler_Effect.raise
            FStarC_Interactive_JsonHelper.InputExhausted
let rec (read_lsp_query :
  FStarC_Compiler_Util.stream_reader ->
    FStarC_Interactive_JsonHelper.lsp_query)
  =
  fun stream ->
    try
      (fun uu___ ->
         match () with
         | () ->
             let n = parse_header_len stream Prims.int_zero in
             let uu___1 = FStarC_Compiler_Util.nread stream n in
             (match uu___1 with
              | FStar_Pervasives_Native.Some s -> parse_lsp_query s
              | FStar_Pervasives_Native.None ->
                  let uu___2 =
                    let uu___3 = FStarC_Compiler_Util.string_of_int n in
                    FStarC_Compiler_Util.format1 "Could not read %s bytes"
                      uu___3 in
                  FStarC_Interactive_JsonHelper.wrap_content_szerr uu___2))
        ()
    with
    | FStarC_Interactive_JsonHelper.MalformedHeader ->
        (FStarC_Compiler_Util.print_error "[E] Malformed Content Header\n";
         read_lsp_query stream)
    | FStarC_Interactive_JsonHelper.InputExhausted -> read_lsp_query stream
let rec (go : FStarC_Interactive_Ide_Types.grepl_state -> Prims.int) =
  fun gst ->
    let query = read_lsp_query gst.FStarC_Interactive_Ide_Types.grepl_stdin in
    let uu___ = run_query gst query.FStarC_Interactive_JsonHelper.q in
    match uu___ with
    | (r, state_opt) ->
        ((match r with
          | FStar_Pervasives_Native.Some response ->
              let response' =
                FStarC_Interactive_JsonHelper.json_of_response
                  query.FStarC_Interactive_JsonHelper.query_id response in
              FStarC_Interactive_JsonHelper.write_jsonrpc response'
          | FStar_Pervasives_Native.None -> ());
         (match state_opt with
          | FStar_Pervasives.Inl gst' -> go gst'
          | FStar_Pervasives.Inr exitcode -> exitcode))
let (start_server : unit -> unit) =
  fun uu___ ->
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Compiler_Util.psmap_empty () in
        let uu___4 = FStarC_Compiler_Util.open_stdin () in
        {
          FStarC_Interactive_Ide_Types.grepl_repls = uu___3;
          FStarC_Interactive_Ide_Types.grepl_stdin = uu___4
        } in
      go uu___2 in
    FStarC_Compiler_Effect.exit uu___1