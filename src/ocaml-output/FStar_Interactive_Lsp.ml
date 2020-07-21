open Prims
let (unpack_lsp_query :
  (Prims.string * FStar_Util.json) Prims.list ->
    FStar_Interactive_JsonHelper.lsp_query)
  =
  fun r ->
    let qid =
      let uu____20 = FStar_Interactive_JsonHelper.try_assoc "id" r in
      FStar_All.pipe_right uu____20
        (FStar_Util.map_option FStar_Interactive_JsonHelper.js_str_int) in
    try
      (fun uu___3_30 ->
         match () with
         | () ->
             let method1 =
               let uu____32 = FStar_Interactive_JsonHelper.assoc "method" r in
               FStar_All.pipe_right uu____32
                 FStar_Interactive_JsonHelper.js_str in
             let uu____33 =
               match method1 with
               | "initialize" ->
                   let uu____34 =
                     let uu____39 =
                       let uu____40 =
                         FStar_Interactive_JsonHelper.arg "processId" r in
                       FStar_All.pipe_right uu____40
                         FStar_Interactive_JsonHelper.js_int in
                     let uu____41 =
                       let uu____42 =
                         FStar_Interactive_JsonHelper.arg "rootUri" r in
                       FStar_All.pipe_right uu____42
                         FStar_Interactive_JsonHelper.js_str in
                     (uu____39, uu____41) in
                   FStar_Interactive_JsonHelper.Initialize uu____34
               | "initialized" -> FStar_Interactive_JsonHelper.Initialized
               | "shutdown" -> FStar_Interactive_JsonHelper.Shutdown
               | "exit" -> FStar_Interactive_JsonHelper.Exit
               | "$/cancelRequest" ->
                   let uu____43 =
                     let uu____44 = FStar_Interactive_JsonHelper.arg "id" r in
                     FStar_All.pipe_right uu____44
                       FStar_Interactive_JsonHelper.js_str_int in
                   FStar_Interactive_JsonHelper.Cancel uu____43
               | "workspace/didChangeWorkspaceFolders" ->
                   let uu____45 =
                     let uu____46 =
                       FStar_Interactive_JsonHelper.arg "event" r in
                     FStar_All.pipe_right uu____46
                       FStar_Interactive_JsonHelper.js_wsch_event in
                   FStar_Interactive_JsonHelper.FolderChange uu____45
               | "workspace/didChangeConfiguration" ->
                   FStar_Interactive_JsonHelper.ChangeConfig
               | "workspace/didChangeWatchedFiles" ->
                   FStar_Interactive_JsonHelper.ChangeWatch
               | "workspace/symbol" ->
                   let uu____47 =
                     let uu____48 =
                       FStar_Interactive_JsonHelper.arg "query" r in
                     FStar_All.pipe_right uu____48
                       FStar_Interactive_JsonHelper.js_str in
                   FStar_Interactive_JsonHelper.Symbol uu____47
               | "workspace/executeCommand" ->
                   let uu____49 =
                     let uu____50 =
                       FStar_Interactive_JsonHelper.arg "command" r in
                     FStar_All.pipe_right uu____50
                       FStar_Interactive_JsonHelper.js_str in
                   FStar_Interactive_JsonHelper.ExecCommand uu____49
               | "textDocument/didOpen" ->
                   let uu____51 =
                     let uu____52 =
                       FStar_Interactive_JsonHelper.arg "textDocument" r in
                     FStar_All.pipe_right uu____52
                       FStar_Interactive_JsonHelper.js_txdoc_item in
                   FStar_Interactive_JsonHelper.DidOpen uu____51
               | "textDocument/didChange" ->
                   let uu____53 =
                     let uu____58 =
                       FStar_Interactive_JsonHelper.js_txdoc_id r in
                     let uu____59 =
                       let uu____60 =
                         FStar_Interactive_JsonHelper.arg "contentChanges" r in
                       FStar_All.pipe_right uu____60
                         FStar_Interactive_JsonHelper.js_contentch in
                     (uu____58, uu____59) in
                   FStar_Interactive_JsonHelper.DidChange uu____53
               | "textDocument/willSave" ->
                   let uu____61 = FStar_Interactive_JsonHelper.js_txdoc_id r in
                   FStar_Interactive_JsonHelper.WillSave uu____61
               | "textDocument/willSaveWaitUntil" ->
                   let uu____62 = FStar_Interactive_JsonHelper.js_txdoc_id r in
                   FStar_Interactive_JsonHelper.WillSaveWait uu____62
               | "textDocument/didSave" ->
                   let uu____63 =
                     let uu____68 =
                       FStar_Interactive_JsonHelper.js_txdoc_id r in
                     let uu____69 =
                       let uu____70 =
                         FStar_Interactive_JsonHelper.arg "text" r in
                       FStar_All.pipe_right uu____70
                         FStar_Interactive_JsonHelper.js_str in
                     (uu____68, uu____69) in
                   FStar_Interactive_JsonHelper.DidSave uu____63
               | "textDocument/didClose" ->
                   let uu____71 = FStar_Interactive_JsonHelper.js_txdoc_id r in
                   FStar_Interactive_JsonHelper.DidClose uu____71
               | "textDocument/completion" ->
                   let uu____72 =
                     let uu____77 =
                       FStar_Interactive_JsonHelper.js_txdoc_pos r in
                     let uu____78 =
                       let uu____79 =
                         FStar_Interactive_JsonHelper.arg "context" r in
                       FStar_All.pipe_right uu____79
                         FStar_Interactive_JsonHelper.js_compl_context in
                     (uu____77, uu____78) in
                   FStar_Interactive_JsonHelper.Completion uu____72
               | "completionItem/resolve" ->
                   FStar_Interactive_JsonHelper.Resolve
               | "textDocument/hover" ->
                   let uu____80 = FStar_Interactive_JsonHelper.js_txdoc_pos r in
                   FStar_Interactive_JsonHelper.Hover uu____80
               | "textDocument/signatureHelp" ->
                   let uu____81 = FStar_Interactive_JsonHelper.js_txdoc_pos r in
                   FStar_Interactive_JsonHelper.SignatureHelp uu____81
               | "textDocument/declaration" ->
                   let uu____82 = FStar_Interactive_JsonHelper.js_txdoc_pos r in
                   FStar_Interactive_JsonHelper.Declaration uu____82
               | "textDocument/definition" ->
                   let uu____83 = FStar_Interactive_JsonHelper.js_txdoc_pos r in
                   FStar_Interactive_JsonHelper.Definition uu____83
               | "textDocument/typeDefinition" ->
                   let uu____84 = FStar_Interactive_JsonHelper.js_txdoc_pos r in
                   FStar_Interactive_JsonHelper.TypeDefinition uu____84
               | "textDocument/implementation" ->
                   let uu____85 = FStar_Interactive_JsonHelper.js_txdoc_pos r in
                   FStar_Interactive_JsonHelper.Implementation uu____85
               | "textDocument/references" ->
                   FStar_Interactive_JsonHelper.References
               | "textDocument/documentHighlight" ->
                   let uu____86 = FStar_Interactive_JsonHelper.js_txdoc_pos r in
                   FStar_Interactive_JsonHelper.DocumentHighlight uu____86
               | "textDocument/documentSymbol" ->
                   FStar_Interactive_JsonHelper.DocumentSymbol
               | "textDocument/codeAction" ->
                   FStar_Interactive_JsonHelper.CodeAction
               | "textDocument/codeLens" ->
                   FStar_Interactive_JsonHelper.CodeLens
               | "codeLens/resolve" ->
                   FStar_Interactive_JsonHelper.CodeLensResolve
               | "textDocument/documentLink" ->
                   FStar_Interactive_JsonHelper.DocumentLink
               | "documentLink/resolve" ->
                   FStar_Interactive_JsonHelper.DocumentLinkResolve
               | "textDocument/documentColor" ->
                   FStar_Interactive_JsonHelper.DocumentColor
               | "textDocument/colorPresentation" ->
                   FStar_Interactive_JsonHelper.ColorPresentation
               | "textDocument/formatting" ->
                   FStar_Interactive_JsonHelper.Formatting
               | "textDocument/rangeFormatting" ->
                   FStar_Interactive_JsonHelper.RangeFormatting
               | "textDocument/onTypeFormatting" ->
                   FStar_Interactive_JsonHelper.TypeFormatting
               | "textDocument/rename" -> FStar_Interactive_JsonHelper.Rename
               | "textDocument/prepareRename" ->
                   let uu____87 = FStar_Interactive_JsonHelper.js_txdoc_pos r in
                   FStar_Interactive_JsonHelper.PrepareRename uu____87
               | "textDocument/foldingRange" ->
                   FStar_Interactive_JsonHelper.FoldingRange
               | m ->
                   let uu____89 = FStar_Util.format1 "Unknown method '%s'" m in
                   FStar_Interactive_JsonHelper.BadProtocolMsg uu____89 in
             {
               FStar_Interactive_JsonHelper.query_id = qid;
               FStar_Interactive_JsonHelper.q = uu____33
             }) ()
    with
    | FStar_Interactive_JsonHelper.MissingKey msg ->
        {
          FStar_Interactive_JsonHelper.query_id = qid;
          FStar_Interactive_JsonHelper.q =
            (FStar_Interactive_JsonHelper.BadProtocolMsg msg)
        }
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected, got) ->
        FStar_Interactive_JsonHelper.wrap_jsfail qid expected got
let (deserialize_lsp_query :
  FStar_Util.json -> FStar_Interactive_JsonHelper.lsp_query) =
  fun js_query ->
    try
      (fun uu___57_103 ->
         match () with
         | () ->
             let uu____104 =
               FStar_All.pipe_right js_query
                 FStar_Interactive_JsonHelper.js_assoc in
             unpack_lsp_query uu____104) ()
    with
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected, got) ->
        FStar_Interactive_JsonHelper.wrap_jsfail FStar_Pervasives_Native.None
          expected got
let (parse_lsp_query :
  Prims.string -> FStar_Interactive_JsonHelper.lsp_query) =
  fun query_str ->
    let uu____129 = FStar_Util.json_of_string query_str in
    match uu____129 with
    | FStar_Pervasives_Native.None ->
        {
          FStar_Interactive_JsonHelper.query_id =
            FStar_Pervasives_Native.None;
          FStar_Interactive_JsonHelper.q =
            (FStar_Interactive_JsonHelper.BadProtocolMsg
               "Json parsing failed")
        }
    | FStar_Pervasives_Native.Some request -> deserialize_lsp_query request
let (repl_state_init :
  Prims.string -> FStar_Interactive_JsonHelper.repl_state) =
  fun fname ->
    let intial_range =
      let uu____139 = FStar_Range.mk_pos Prims.int_one Prims.int_zero in
      let uu____140 = FStar_Range.mk_pos Prims.int_one Prims.int_zero in
      FStar_Range.mk_range fname uu____139 uu____140 in
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps in
    let env1 = FStar_TypeChecker_Env.set_range env intial_range in
    let uu____143 = FStar_Util.open_stdin () in
    {
      FStar_Interactive_JsonHelper.repl_line = Prims.int_one;
      FStar_Interactive_JsonHelper.repl_column = Prims.int_zero;
      FStar_Interactive_JsonHelper.repl_fname = fname;
      FStar_Interactive_JsonHelper.repl_deps_stack = [];
      FStar_Interactive_JsonHelper.repl_curmod = FStar_Pervasives_Native.None;
      FStar_Interactive_JsonHelper.repl_env = env1;
      FStar_Interactive_JsonHelper.repl_stdin = uu____143;
      FStar_Interactive_JsonHelper.repl_names =
        FStar_Interactive_CompletionTable.empty
    }
type optresponse =
  FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option
type either_gst_exit =
  (FStar_Interactive_JsonHelper.grepl_state, Prims.int) FStar_Util.either
let (invoke_full_lax :
  FStar_Interactive_JsonHelper.grepl_state ->
    Prims.string ->
      Prims.string -> Prims.bool -> (optresponse * either_gst_exit))
  =
  fun gst ->
    fun fname ->
      fun text ->
        fun force ->
          let aux uu____201 =
            FStar_Parser_ParseIt.add_vfs_entry fname text;
            (let uu____203 =
               let uu____210 = repl_state_init fname in
               FStar_Interactive_PushHelper.full_lax text uu____210 in
             match uu____203 with
             | (diag, st') ->
                 let repls =
                   FStar_Util.psmap_add
                     gst.FStar_Interactive_JsonHelper.grepl_repls fname st' in
                 let diag1 =
                   if FStar_Util.is_some diag
                   then diag
                   else
                     (let uu____236 =
                        FStar_Interactive_JsonHelper.js_diag_clear fname in
                      FStar_Pervasives_Native.Some uu____236) in
                 (diag1,
                   (FStar_Util.Inl
                      (let uu___88_244 = gst in
                       {
                         FStar_Interactive_JsonHelper.grepl_repls = repls;
                         FStar_Interactive_JsonHelper.grepl_stdin =
                           (uu___88_244.FStar_Interactive_JsonHelper.grepl_stdin)
                       })))) in
          let uu____245 =
            FStar_Util.psmap_try_find
              gst.FStar_Interactive_JsonHelper.grepl_repls fname in
          match uu____245 with
          | FStar_Pervasives_Native.Some uu____252 ->
              if force
              then aux ()
              else (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
          | FStar_Pervasives_Native.None -> aux ()
let (run_query :
  FStar_Interactive_JsonHelper.grepl_state ->
    FStar_Interactive_JsonHelper.lquery -> (optresponse * either_gst_exit))
  =
  fun gst ->
    fun q ->
      match q with
      | FStar_Interactive_JsonHelper.Initialize (uu____276, uu____277) ->
          let uu____278 =
            FStar_Interactive_JsonHelper.resultResponse
              FStar_Interactive_JsonHelper.js_servcap in
          (uu____278, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Initialized ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Shutdown ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Exit ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inr Prims.int_zero))
      | FStar_Interactive_JsonHelper.Cancel id ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.FolderChange evt ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.ChangeConfig ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.ChangeWatch ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Symbol sym ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.ExecCommand cmd ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DidOpen
          { FStar_Interactive_JsonHelper.fname = f;
            FStar_Interactive_JsonHelper.langId = uu____284;
            FStar_Interactive_JsonHelper.version = uu____285;
            FStar_Interactive_JsonHelper.text = t;_}
          -> invoke_full_lax gst f t false
      | FStar_Interactive_JsonHelper.DidChange (txid, content) ->
          (FStar_Parser_ParseIt.add_vfs_entry txid content;
           (FStar_Pervasives_Native.None, (FStar_Util.Inl gst)))
      | FStar_Interactive_JsonHelper.WillSave txid ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.WillSaveWait txid ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DidSave (f, t) ->
          invoke_full_lax gst f t true
      | FStar_Interactive_JsonHelper.DidClose txid ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Completion (txpos, ctx) ->
          let uu____297 =
            FStar_Util.psmap_try_find
              gst.FStar_Interactive_JsonHelper.grepl_repls
              txpos.FStar_Interactive_JsonHelper.path in
          (match uu____297 with
           | FStar_Pervasives_Native.Some st ->
               let uu____305 =
                 FStar_Interactive_QueryHelper.complookup st txpos in
               (uu____305, (FStar_Util.Inl gst))
           | FStar_Pervasives_Native.None ->
               (FStar_Interactive_JsonHelper.nullResponse,
                 (FStar_Util.Inl gst)))
      | FStar_Interactive_JsonHelper.Resolve ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Hover txpos ->
          let uu____307 =
            FStar_Util.psmap_try_find
              gst.FStar_Interactive_JsonHelper.grepl_repls
              txpos.FStar_Interactive_JsonHelper.path in
          (match uu____307 with
           | FStar_Pervasives_Native.Some st ->
               let uu____315 =
                 FStar_Interactive_QueryHelper.hoverlookup
                   st.FStar_Interactive_JsonHelper.repl_env txpos in
               (uu____315, (FStar_Util.Inl gst))
           | FStar_Pervasives_Native.None ->
               (FStar_Interactive_JsonHelper.nullResponse,
                 (FStar_Util.Inl gst)))
      | FStar_Interactive_JsonHelper.SignatureHelp txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Declaration txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Definition txpos ->
          let uu____319 =
            FStar_Util.psmap_try_find
              gst.FStar_Interactive_JsonHelper.grepl_repls
              txpos.FStar_Interactive_JsonHelper.path in
          (match uu____319 with
           | FStar_Pervasives_Native.Some st ->
               let uu____327 =
                 FStar_Interactive_QueryHelper.deflookup
                   st.FStar_Interactive_JsonHelper.repl_env txpos in
               (uu____327, (FStar_Util.Inl gst))
           | FStar_Pervasives_Native.None ->
               (FStar_Interactive_JsonHelper.nullResponse,
                 (FStar_Util.Inl gst)))
      | FStar_Interactive_JsonHelper.TypeDefinition txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Implementation txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.References ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DocumentHighlight txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DocumentSymbol ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.CodeAction ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.CodeLens ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.CodeLensResolve ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DocumentLink ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DocumentLinkResolve ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DocumentColor ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.ColorPresentation ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Formatting ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.RangeFormatting ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.TypeFormatting ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Rename ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.PrepareRename txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.FoldingRange ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.BadProtocolMsg msg ->
          let uu____333 =
            let uu____334 =
              FStar_Interactive_JsonHelper.js_resperr
                FStar_Interactive_JsonHelper.MethodNotFound msg in
            FStar_Interactive_JsonHelper.errorResponse uu____334 in
          (uu____333, (FStar_Util.Inl gst))
let rec (parse_header_len :
  FStar_Util.stream_reader -> Prims.int -> Prims.int) =
  fun stream ->
    fun len ->
      let uu____345 = FStar_Util.read_line stream in
      match uu____345 with
      | FStar_Pervasives_Native.Some s ->
          if FStar_Util.starts_with s "Content-Length: "
          then
            let uu____349 =
              let uu____350 = FStar_Util.substring_from s (Prims.of_int (16)) in
              FStar_Util.int_of_string uu____350 in
            parse_header_len stream uu____349
          else
            if FStar_Util.starts_with s "Content-Type: "
            then parse_header_len stream len
            else
              if s = ""
              then len
              else
                FStar_Exn.raise FStar_Interactive_JsonHelper.MalformedHeader
      | FStar_Pervasives_Native.None ->
          FStar_Exn.raise FStar_Interactive_JsonHelper.InputExhausted
let rec (read_lsp_query :
  FStar_Util.stream_reader -> FStar_Interactive_JsonHelper.lsp_query) =
  fun stream ->
    try
      (fun uu___190_363 ->
         match () with
         | () ->
             let n = parse_header_len stream Prims.int_zero in
             let uu____365 = FStar_Util.nread stream n in
             (match uu____365 with
              | FStar_Pervasives_Native.Some s -> parse_lsp_query s
              | FStar_Pervasives_Native.None ->
                  let uu____369 =
                    let uu____370 = FStar_Util.string_of_int n in
                    FStar_Util.format1 "Could not read %s bytes" uu____370 in
                  FStar_Interactive_JsonHelper.wrap_content_szerr uu____369))
        ()
    with
    | FStar_Interactive_JsonHelper.MalformedHeader ->
        (FStar_Util.print_error "[E] Malformed Content Header\n";
         read_lsp_query stream)
    | FStar_Interactive_JsonHelper.InputExhausted -> read_lsp_query stream
let rec (go : FStar_Interactive_JsonHelper.grepl_state -> Prims.int) =
  fun gst ->
    let query = read_lsp_query gst.FStar_Interactive_JsonHelper.grepl_stdin in
    let uu____381 = run_query gst query.FStar_Interactive_JsonHelper.q in
    match uu____381 with
    | (r, state_opt) ->
        ((match r with
          | FStar_Pervasives_Native.Some response ->
              let response' =
                FStar_Interactive_JsonHelper.json_of_response
                  query.FStar_Interactive_JsonHelper.query_id response in
              (if false
               then
                 (let uu____392 = FStar_Util.string_of_json response' in
                  FStar_Util.print1_error "<<< %s\n" uu____392)
               else ();
               FStar_Interactive_JsonHelper.write_jsonrpc response')
          | FStar_Pervasives_Native.None -> ());
         (match state_opt with
          | FStar_Util.Inl gst' -> go gst'
          | FStar_Util.Inr exitcode -> exitcode))
let (start_server : unit -> unit) =
  fun uu____400 ->
    let uu____401 =
      let uu____402 =
        let uu____403 = FStar_Util.psmap_empty () in
        let uu____406 = FStar_Util.open_stdin () in
        {
          FStar_Interactive_JsonHelper.grepl_repls = uu____403;
          FStar_Interactive_JsonHelper.grepl_stdin = uu____406
        } in
      go uu____402 in
    FStar_All.exit uu____401