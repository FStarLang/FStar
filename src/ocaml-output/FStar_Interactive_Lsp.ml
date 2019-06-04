open Prims
let (unpack_lsp_query :
  (Prims.string * FStar_Util.json) Prims.list -> FStar_JsonHelper.lsp_query)
  =
  fun r ->
    let qid =
      let uu____23 = FStar_JsonHelper.try_assoc "id" r in
      FStar_All.pipe_right uu____23
        (FStar_Util.map_option FStar_JsonHelper.js_str_int) in
    try
      (fun uu___3_36 ->
         match () with
         | () ->
             let method_37 =
               let uu____39 = FStar_JsonHelper.assoc "method" r in
               FStar_All.pipe_right uu____39 FStar_JsonHelper.js_str in
             let uu____42 =
               match method_37 with
               | "initialize" ->
                   let uu____44 =
                     let uu____51 =
                       let uu____53 = FStar_JsonHelper.arg "processId" r in
                       FStar_All.pipe_right uu____53 FStar_JsonHelper.js_int in
                     let uu____56 =
                       let uu____58 = FStar_JsonHelper.arg "rootUri" r in
                       FStar_All.pipe_right uu____58 FStar_JsonHelper.js_str in
                     (uu____51, uu____56) in
                   FStar_JsonHelper.Initialize uu____44
               | "initialized" -> FStar_JsonHelper.Initialized
               | "shutdown" -> FStar_JsonHelper.Shutdown
               | "exit" -> FStar_JsonHelper.Exit
               | "$/cancelRequest" ->
                   let uu____67 =
                     let uu____69 = FStar_JsonHelper.arg "id" r in
                     FStar_All.pipe_right uu____69
                       FStar_JsonHelper.js_str_int in
                   FStar_JsonHelper.Cancel uu____67
               | "workspace/didChangeWorkspaceFolders" ->
                   let uu____73 =
                     let uu____74 = FStar_JsonHelper.arg "event" r in
                     FStar_All.pipe_right uu____74
                       FStar_JsonHelper.js_wsch_event in
                   FStar_JsonHelper.FolderChange uu____73
               | "workspace/didChangeConfiguration" ->
                   FStar_JsonHelper.ChangeConfig
               | "workspace/didChangeWatchedFiles" ->
                   FStar_JsonHelper.ChangeWatch
               | "workspace/symbol" ->
                   let uu____79 =
                     let uu____81 = FStar_JsonHelper.arg "query" r in
                     FStar_All.pipe_right uu____81 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.Symbol uu____79
               | "workspace/executeCommand" ->
                   let uu____85 =
                     let uu____87 = FStar_JsonHelper.arg "command" r in
                     FStar_All.pipe_right uu____87 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.ExecCommand uu____85
               | "textDocument/didOpen" ->
                   let uu____91 =
                     let uu____92 = FStar_JsonHelper.arg "textDocument" r in
                     FStar_All.pipe_right uu____92
                       FStar_JsonHelper.js_txdoc_item in
                   FStar_JsonHelper.DidOpen uu____91
               | "textDocument/didChange" ->
                   let uu____95 =
                     let uu____102 = FStar_JsonHelper.js_txdoc_id r in
                     let uu____104 =
                       let uu____106 =
                         FStar_JsonHelper.arg "contentChanges" r in
                       FStar_All.pipe_right uu____106
                         FStar_JsonHelper.js_contentch in
                     (uu____102, uu____104) in
                   FStar_JsonHelper.DidChange uu____95
               | "textDocument/willSave" ->
                   let uu____112 = FStar_JsonHelper.js_txdoc_id r in
                   FStar_JsonHelper.WillSave uu____112
               | "textDocument/willSaveWaitUntil" ->
                   let uu____115 = FStar_JsonHelper.js_txdoc_id r in
                   FStar_JsonHelper.WillSaveWait uu____115
               | "textDocument/didSave" ->
                   let uu____118 =
                     let uu____125 = FStar_JsonHelper.js_txdoc_id r in
                     let uu____127 =
                       let uu____129 = FStar_JsonHelper.arg "text" r in
                       FStar_All.pipe_right uu____129 FStar_JsonHelper.js_str in
                     (uu____125, uu____127) in
                   FStar_JsonHelper.DidSave uu____118
               | "textDocument/didClose" ->
                   let uu____135 = FStar_JsonHelper.js_txdoc_id r in
                   FStar_JsonHelper.DidClose uu____135
               | "textDocument/completion" ->
                   let uu____138 =
                     let uu____143 = FStar_JsonHelper.js_txdoc_pos r in
                     let uu____144 =
                       let uu____145 = FStar_JsonHelper.arg "context" r in
                       FStar_All.pipe_right uu____145
                         FStar_JsonHelper.js_compl_context in
                     (uu____143, uu____144) in
                   FStar_JsonHelper.Completion uu____138
               | "completionItem/resolve" -> FStar_JsonHelper.Resolve
               | "textDocument/hover" ->
                   let uu____149 = FStar_JsonHelper.js_txdoc_pos r in
                   FStar_JsonHelper.Hover uu____149
               | "textDocument/signatureHelp" ->
                   let uu____151 = FStar_JsonHelper.js_txdoc_pos r in
                   FStar_JsonHelper.SignatureHelp uu____151
               | "textDocument/declaration" ->
                   let uu____153 = FStar_JsonHelper.js_txdoc_pos r in
                   FStar_JsonHelper.Declaration uu____153
               | "textDocument/definition" ->
                   let uu____155 = FStar_JsonHelper.js_txdoc_pos r in
                   FStar_JsonHelper.Definition uu____155
               | "textDocument/typeDefinition" ->
                   let uu____157 = FStar_JsonHelper.js_txdoc_pos r in
                   FStar_JsonHelper.TypeDefinition uu____157
               | "textDocument/implementation" ->
                   let uu____159 = FStar_JsonHelper.js_txdoc_pos r in
                   FStar_JsonHelper.Implementation uu____159
               | "textDocument/references" -> FStar_JsonHelper.References
               | "textDocument/documentHighlight" ->
                   let uu____162 = FStar_JsonHelper.js_txdoc_pos r in
                   FStar_JsonHelper.DocumentHighlight uu____162
               | "textDocument/documentSymbol" ->
                   FStar_JsonHelper.DocumentSymbol
               | "textDocument/codeAction" -> FStar_JsonHelper.CodeAction
               | "textDocument/codeLens" -> FStar_JsonHelper.CodeLens
               | "codeLens/resolve" -> FStar_JsonHelper.CodeLensResolve
               | "textDocument/documentLink" -> FStar_JsonHelper.DocumentLink
               | "documentLink/resolve" ->
                   FStar_JsonHelper.DocumentLinkResolve
               | "textDocument/documentColor" ->
                   FStar_JsonHelper.DocumentColor
               | "textDocument/colorPresentation" ->
                   FStar_JsonHelper.ColorPresentation
               | "textDocument/formatting" -> FStar_JsonHelper.Formatting
               | "textDocument/rangeFormatting" ->
                   FStar_JsonHelper.RangeFormatting
               | "textDocument/onTypeFormatting" ->
                   FStar_JsonHelper.TypeFormatting
               | "textDocument/rename" -> FStar_JsonHelper.Rename
               | "textDocument/prepareRename" ->
                   let uu____176 = FStar_JsonHelper.js_txdoc_pos r in
                   FStar_JsonHelper.PrepareRename uu____176
               | "textDocument/foldingRange" -> FStar_JsonHelper.FoldingRange
               | m ->
                   let uu____180 = FStar_Util.format1 "Unknown method '%s'" m in
                   FStar_JsonHelper.BadProtocolMsg uu____180 in
             { FStar_JsonHelper.query_id = qid; FStar_JsonHelper.q = uu____42
             }) ()
    with
    | FStar_JsonHelper.MissingKey msg ->
        {
          FStar_JsonHelper.query_id = qid;
          FStar_JsonHelper.q = (FStar_JsonHelper.BadProtocolMsg msg)
        }
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        FStar_JsonHelper.wrap_jsfail qid expected got
let (deserialize_lsp_query : FStar_Util.json -> FStar_JsonHelper.lsp_query) =
  fun js_query ->
    try
      (fun uu___57_200 ->
         match () with
         | () ->
             let uu____201 =
               FStar_All.pipe_right js_query FStar_JsonHelper.js_assoc in
             unpack_lsp_query uu____201) ()
    with
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        FStar_JsonHelper.wrap_jsfail FStar_Pervasives_Native.None expected
          got
let (parse_lsp_query : Prims.string -> FStar_JsonHelper.lsp_query) =
  fun query_str ->
    FStar_Util.print1_error ">>> %s\n" query_str;
    (let uu____235 = FStar_Util.json_of_string query_str in
     match uu____235 with
     | FStar_Pervasives_Native.None ->
         {
           FStar_JsonHelper.query_id = FStar_Pervasives_Native.None;
           FStar_JsonHelper.q =
             (FStar_JsonHelper.BadProtocolMsg "Json parsing failed")
         }
     | FStar_Pervasives_Native.Some request -> deserialize_lsp_query request)
let (repl_state_init : Prims.string -> FStar_JsonHelper.repl_state) =
  fun fname ->
    let intial_range =
      let uu____250 =
        FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
      let uu____253 =
        FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
      FStar_Range.mk_range fname uu____250 uu____253 in
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps in
    let env1 = FStar_TypeChecker_Env.set_range env intial_range in
    let uu____258 = FStar_Util.open_stdin () in
    {
      FStar_JsonHelper.repl_line = (Prims.parse_int "1");
      FStar_JsonHelper.repl_column = (Prims.parse_int "0");
      FStar_JsonHelper.repl_fname = fname;
      FStar_JsonHelper.repl_deps_stack = [];
      FStar_JsonHelper.repl_curmod = FStar_Pervasives_Native.None;
      FStar_JsonHelper.repl_env = env1;
      FStar_JsonHelper.repl_stdin = uu____258;
      FStar_JsonHelper.repl_names = FStar_Interactive_CompletionTable.empty
    }
type optresponse = FStar_JsonHelper.assoct FStar_Pervasives_Native.option
type either_gst_exit =
  (FStar_JsonHelper.grepl_state, Prims.int) FStar_Util.either
let (run_query :
  FStar_JsonHelper.grepl_state ->
    FStar_JsonHelper.lquery -> (optresponse * either_gst_exit))
  =
  fun gst ->
    fun q ->
      match q with
      | FStar_JsonHelper.Initialize (pid, rootUri) ->
          let uu____301 =
            FStar_JsonHelper.resultResponse FStar_JsonHelper.js_servcap in
          (uu____301, (FStar_Util.Inl gst))
      | FStar_JsonHelper.Initialized ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_JsonHelper.Shutdown ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.Exit ->
          (FStar_Pervasives_Native.None,
            (FStar_Util.Inr (Prims.parse_int "0")))
      | FStar_JsonHelper.Cancel id1 ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_JsonHelper.FolderChange evt ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.ChangeConfig ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.ChangeWatch ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_JsonHelper.Symbol sym ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.ExecCommand cmd ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.DidOpen
          { FStar_JsonHelper.fname = p; FStar_JsonHelper.langId = uu____321;
            FStar_JsonHelper.version = uu____322;
            FStar_JsonHelper.text = t;_}
          ->
          let uu____328 =
            FStar_Util.psmap_try_find gst.FStar_JsonHelper.grepl_repls p in
          (match uu____328 with
           | FStar_Pervasives_Native.Some uu____335 ->
               (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
           | FStar_Pervasives_Native.None ->
               (FStar_Parser_ParseIt.add_vfs_entry p t;
                (let uu____338 =
                   let uu____345 = repl_state_init p in
                   FStar_PushHelper.full_lax t uu____345 in
                 match uu____338 with
                 | (diag1, st') ->
                     let repls =
                       FStar_Util.psmap_add gst.FStar_JsonHelper.grepl_repls
                         p st' in
                     (diag1,
                       (FStar_Util.Inl
                          (let uu___107_361 = gst in
                           {
                             FStar_JsonHelper.grepl_repls = repls;
                             FStar_JsonHelper.grepl_stdin =
                               (uu___107_361.FStar_JsonHelper.grepl_stdin)
                           }))))))
      | FStar_JsonHelper.DidChange (txid, content) ->
          (FStar_Parser_ParseIt.add_vfs_entry txid content;
           (FStar_Pervasives_Native.None, (FStar_Util.Inl gst)))
      | FStar_JsonHelper.WillSave txid ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_JsonHelper.WillSaveWait txid ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.DidSave (txid, content) ->
          (FStar_Parser_ParseIt.add_vfs_entry txid content;
           (FStar_Pervasives_Native.None, (FStar_Util.Inl gst)))
      | FStar_JsonHelper.DidClose txid ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_JsonHelper.Completion (txpos, ctx) ->
          let uu____389 =
            FStar_Util.psmap_try_find gst.FStar_JsonHelper.grepl_repls
              txpos.FStar_JsonHelper.path in
          (match uu____389 with
           | FStar_Pervasives_Native.Some st ->
               let uu____397 = FStar_QueryHelper.complookup st txpos in
               (uu____397, (FStar_Util.Inl gst))
           | FStar_Pervasives_Native.None ->
               (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst)))
      | FStar_JsonHelper.Resolve ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.Hover txpos ->
          let uu____402 =
            FStar_Util.psmap_try_find gst.FStar_JsonHelper.grepl_repls
              txpos.FStar_JsonHelper.path in
          (match uu____402 with
           | FStar_Pervasives_Native.Some st ->
               let uu____410 =
                 FStar_QueryHelper.hoverlookup st.FStar_JsonHelper.repl_env
                   txpos in
               (uu____410, (FStar_Util.Inl gst))
           | FStar_Pervasives_Native.None ->
               (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst)))
      | FStar_JsonHelper.SignatureHelp txpos ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.Declaration txpos ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.Definition txpos ->
          let uu____418 =
            FStar_Util.psmap_try_find gst.FStar_JsonHelper.grepl_repls
              txpos.FStar_JsonHelper.path in
          (match uu____418 with
           | FStar_Pervasives_Native.Some st ->
               let uu____426 =
                 FStar_QueryHelper.deflookup st.FStar_JsonHelper.repl_env
                   txpos in
               (uu____426, (FStar_Util.Inl gst))
           | FStar_Pervasives_Native.None ->
               (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst)))
      | FStar_JsonHelper.TypeDefinition txpos ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.Implementation txpos ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.References ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.DocumentHighlight txpos ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.DocumentSymbol ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.CodeAction ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.CodeLens ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.CodeLensResolve ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.DocumentLink ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.DocumentLinkResolve ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.DocumentColor ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.ColorPresentation ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.Formatting ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.RangeFormatting ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.TypeFormatting ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.Rename ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.PrepareRename txpos ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.FoldingRange ->
          (FStar_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_JsonHelper.BadProtocolMsg msg ->
          let uu____453 =
            let uu____454 =
              FStar_JsonHelper.js_resperr FStar_JsonHelper.MethodNotFound msg in
            FStar_JsonHelper.errorResponse uu____454 in
          (uu____453, (FStar_Util.Inl gst))
let rec (parse_header_len :
  FStar_Util.stream_reader -> Prims.int -> Prims.int) =
  fun stream ->
    fun len ->
      let uu____471 = FStar_Util.read_line stream in
      match uu____471 with
      | FStar_Pervasives_Native.Some s ->
          if FStar_Util.starts_with s "Content-Length: "
          then
            let uu____482 =
              let uu____484 =
                FStar_Util.substring_from s (Prims.parse_int "16") in
              FStar_Util.int_of_string uu____484 in
            parse_header_len stream uu____482
          else
            if FStar_Util.starts_with s "Content-Type: "
            then parse_header_len stream len
            else
              if s = ""
              then len
              else FStar_Exn.raise FStar_JsonHelper.MalformedHeader
      | FStar_Pervasives_Native.None ->
          FStar_Exn.raise FStar_JsonHelper.InputExhausted
let rec (read_lsp_query :
  FStar_Util.stream_reader -> FStar_JsonHelper.lsp_query) =
  fun stream ->
    try
      (fun uu___181_513 ->
         match () with
         | () ->
             let n1 = parse_header_len stream (Prims.parse_int "0") in
             let uu____517 = FStar_Util.nread stream n1 in
             (match uu____517 with
              | FStar_Pervasives_Native.Some s -> parse_lsp_query s
              | FStar_Pervasives_Native.None ->
                  let uu____525 =
                    let uu____527 = FStar_Util.string_of_int n1 in
                    FStar_Util.format1 "Could not read %s bytes" uu____527 in
                  FStar_JsonHelper.wrap_content_szerr uu____525)) ()
    with
    | FStar_JsonHelper.MalformedHeader ->
        (FStar_Util.print_error "[E] Malformed Content Header\n";
         read_lsp_query stream)
    | FStar_JsonHelper.InputExhausted -> read_lsp_query stream
let rec (go : FStar_JsonHelper.grepl_state -> Prims.int) =
  fun gst ->
    let query = read_lsp_query gst.FStar_JsonHelper.grepl_stdin in
    let uu____544 = run_query gst query.FStar_JsonHelper.q in
    match uu____544 with
    | (r, state_opt) ->
        ((match r with
          | FStar_Pervasives_Native.Some response ->
              let response' =
                FStar_JsonHelper.json_of_response
                  query.FStar_JsonHelper.query_id response in
              ((let uu____556 = FStar_Util.string_of_json response' in
                FStar_Util.print1_error "<<< %s\n" uu____556);
               FStar_JsonHelper.write_jsonrpc response')
          | FStar_Pervasives_Native.None -> ());
         (match state_opt with
          | FStar_Util.Inl gst' -> go gst'
          | FStar_Util.Inr exitcode -> exitcode))
let (start_server : unit -> unit) =
  fun uu____570 ->
    let uu____571 =
      let uu____573 =
        let uu____574 = FStar_Util.psmap_empty () in
        let uu____577 = FStar_Util.open_stdin () in
        {
          FStar_JsonHelper.grepl_repls = uu____574;
          FStar_JsonHelper.grepl_stdin = uu____577
        } in
      go uu____573 in
    FStar_All.exit uu____571