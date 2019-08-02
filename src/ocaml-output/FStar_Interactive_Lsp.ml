open Prims
let (unpack_lsp_query :
  (Prims.string * FStar_Util.json) Prims.list ->
    FStar_Interactive_JsonHelper.lsp_query)
  =
  fun r  ->
    let qid =
      let uu____23 = FStar_Interactive_JsonHelper.try_assoc "id" r  in
      FStar_All.pipe_right uu____23
        (FStar_Util.map_option FStar_Interactive_JsonHelper.js_str_int)
       in
    try
      (fun uu___3_36  ->
         match () with
         | () ->
             let method_37 =
               let uu____39 = FStar_Interactive_JsonHelper.assoc "method" r
                  in
               FStar_All.pipe_right uu____39
                 FStar_Interactive_JsonHelper.js_str
                in
             let uu____42 =
               match method_37 with
               | "initialize" ->
                   let uu____44 =
                     let uu____51 =
                       let uu____53 =
                         FStar_Interactive_JsonHelper.arg "processId" r  in
                       FStar_All.pipe_right uu____53
                         FStar_Interactive_JsonHelper.js_int
                        in
                     let uu____56 =
                       let uu____58 =
                         FStar_Interactive_JsonHelper.arg "rootUri" r  in
                       FStar_All.pipe_right uu____58
                         FStar_Interactive_JsonHelper.js_str
                        in
                     (uu____51, uu____56)  in
                   FStar_Interactive_JsonHelper.Initialize uu____44
               | "initialized" -> FStar_Interactive_JsonHelper.Initialized
               | "shutdown" -> FStar_Interactive_JsonHelper.Shutdown
               | "exit" -> FStar_Interactive_JsonHelper.Exit
               | "$/cancelRequest" ->
                   let uu____67 =
                     let uu____69 = FStar_Interactive_JsonHelper.arg "id" r
                        in
                     FStar_All.pipe_right uu____69
                       FStar_Interactive_JsonHelper.js_str_int
                      in
                   FStar_Interactive_JsonHelper.Cancel uu____67
               | "workspace/didChangeWorkspaceFolders" ->
                   let uu____73 =
                     let uu____74 =
                       FStar_Interactive_JsonHelper.arg "event" r  in
                     FStar_All.pipe_right uu____74
                       FStar_Interactive_JsonHelper.js_wsch_event
                      in
                   FStar_Interactive_JsonHelper.FolderChange uu____73
               | "workspace/didChangeConfiguration" ->
                   FStar_Interactive_JsonHelper.ChangeConfig
               | "workspace/didChangeWatchedFiles" ->
                   FStar_Interactive_JsonHelper.ChangeWatch
               | "workspace/symbol" ->
                   let uu____79 =
                     let uu____81 =
                       FStar_Interactive_JsonHelper.arg "query" r  in
                     FStar_All.pipe_right uu____81
                       FStar_Interactive_JsonHelper.js_str
                      in
                   FStar_Interactive_JsonHelper.Symbol uu____79
               | "workspace/executeCommand" ->
                   let uu____85 =
                     let uu____87 =
                       FStar_Interactive_JsonHelper.arg "command" r  in
                     FStar_All.pipe_right uu____87
                       FStar_Interactive_JsonHelper.js_str
                      in
                   FStar_Interactive_JsonHelper.ExecCommand uu____85
               | "textDocument/didOpen" ->
                   let uu____91 =
                     let uu____92 =
                       FStar_Interactive_JsonHelper.arg "textDocument" r  in
                     FStar_All.pipe_right uu____92
                       FStar_Interactive_JsonHelper.js_txdoc_item
                      in
                   FStar_Interactive_JsonHelper.DidOpen uu____91
               | "textDocument/didChange" ->
                   let uu____95 =
                     let uu____102 =
                       FStar_Interactive_JsonHelper.js_txdoc_id r  in
                     let uu____104 =
                       let uu____106 =
                         FStar_Interactive_JsonHelper.arg "contentChanges" r
                          in
                       FStar_All.pipe_right uu____106
                         FStar_Interactive_JsonHelper.js_contentch
                        in
                     (uu____102, uu____104)  in
                   FStar_Interactive_JsonHelper.DidChange uu____95
               | "textDocument/willSave" ->
                   let uu____112 = FStar_Interactive_JsonHelper.js_txdoc_id r
                      in
                   FStar_Interactive_JsonHelper.WillSave uu____112
               | "textDocument/willSaveWaitUntil" ->
                   let uu____115 = FStar_Interactive_JsonHelper.js_txdoc_id r
                      in
                   FStar_Interactive_JsonHelper.WillSaveWait uu____115
               | "textDocument/didSave" ->
                   let uu____118 =
                     let uu____125 =
                       FStar_Interactive_JsonHelper.js_txdoc_id r  in
                     let uu____127 =
                       let uu____129 =
                         FStar_Interactive_JsonHelper.arg "text" r  in
                       FStar_All.pipe_right uu____129
                         FStar_Interactive_JsonHelper.js_str
                        in
                     (uu____125, uu____127)  in
                   FStar_Interactive_JsonHelper.DidSave uu____118
               | "textDocument/didClose" ->
                   let uu____135 = FStar_Interactive_JsonHelper.js_txdoc_id r
                      in
                   FStar_Interactive_JsonHelper.DidClose uu____135
               | "textDocument/completion" ->
                   let uu____138 =
                     let uu____143 =
                       FStar_Interactive_JsonHelper.js_txdoc_pos r  in
                     let uu____144 =
                       let uu____145 =
                         FStar_Interactive_JsonHelper.arg "context" r  in
                       FStar_All.pipe_right uu____145
                         FStar_Interactive_JsonHelper.js_compl_context
                        in
                     (uu____143, uu____144)  in
                   FStar_Interactive_JsonHelper.Completion uu____138
               | "completionItem/resolve" ->
                   FStar_Interactive_JsonHelper.Resolve
               | "textDocument/hover" ->
                   let uu____149 =
                     FStar_Interactive_JsonHelper.js_txdoc_pos r  in
                   FStar_Interactive_JsonHelper.Hover uu____149
               | "textDocument/signatureHelp" ->
                   let uu____151 =
                     FStar_Interactive_JsonHelper.js_txdoc_pos r  in
                   FStar_Interactive_JsonHelper.SignatureHelp uu____151
               | "textDocument/declaration" ->
                   let uu____153 =
                     FStar_Interactive_JsonHelper.js_txdoc_pos r  in
                   FStar_Interactive_JsonHelper.Declaration uu____153
               | "textDocument/definition" ->
                   let uu____155 =
                     FStar_Interactive_JsonHelper.js_txdoc_pos r  in
                   FStar_Interactive_JsonHelper.Definition uu____155
               | "textDocument/typeDefinition" ->
                   let uu____157 =
                     FStar_Interactive_JsonHelper.js_txdoc_pos r  in
                   FStar_Interactive_JsonHelper.TypeDefinition uu____157
               | "textDocument/implementation" ->
                   let uu____159 =
                     FStar_Interactive_JsonHelper.js_txdoc_pos r  in
                   FStar_Interactive_JsonHelper.Implementation uu____159
               | "textDocument/references" ->
                   FStar_Interactive_JsonHelper.References
               | "textDocument/documentHighlight" ->
                   let uu____162 =
                     FStar_Interactive_JsonHelper.js_txdoc_pos r  in
                   FStar_Interactive_JsonHelper.DocumentHighlight uu____162
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
                   let uu____176 =
                     FStar_Interactive_JsonHelper.js_txdoc_pos r  in
                   FStar_Interactive_JsonHelper.PrepareRename uu____176
               | "textDocument/foldingRange" ->
                   FStar_Interactive_JsonHelper.FoldingRange
               | m ->
                   let uu____180 = FStar_Util.format1 "Unknown method '%s'" m
                      in
                   FStar_Interactive_JsonHelper.BadProtocolMsg uu____180
                in
             {
               FStar_Interactive_JsonHelper.query_id = qid;
               FStar_Interactive_JsonHelper.q = uu____42
             }) ()
    with
    | FStar_Interactive_JsonHelper.MissingKey msg ->
        {
          FStar_Interactive_JsonHelper.query_id = qid;
          FStar_Interactive_JsonHelper.q =
            (FStar_Interactive_JsonHelper.BadProtocolMsg msg)
        }
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected,got) ->
        FStar_Interactive_JsonHelper.wrap_jsfail qid expected got
  
let (deserialize_lsp_query :
  FStar_Util.json -> FStar_Interactive_JsonHelper.lsp_query) =
  fun js_query  ->
    try
      (fun uu___57_200  ->
         match () with
         | () ->
             let uu____201 =
               FStar_All.pipe_right js_query
                 FStar_Interactive_JsonHelper.js_assoc
                in
             unpack_lsp_query uu____201) ()
    with
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected,got) ->
        FStar_Interactive_JsonHelper.wrap_jsfail FStar_Pervasives_Native.None
          expected got
  
let (parse_lsp_query :
  Prims.string -> FStar_Interactive_JsonHelper.lsp_query) =
  fun query_str  ->
    let uu____234 = FStar_Util.json_of_string query_str  in
    match uu____234 with
    | FStar_Pervasives_Native.None  ->
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
  fun fname  ->
    let intial_range =
      let uu____249 = FStar_Range.mk_pos Prims.int_one Prims.int_zero  in
      let uu____252 = FStar_Range.mk_pos Prims.int_one Prims.int_zero  in
      FStar_Range.mk_range fname uu____249 uu____252  in
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps  in
    let env1 = FStar_TypeChecker_Env.set_range env intial_range  in
    let uu____257 = FStar_Util.open_stdin ()  in
    {
      FStar_Interactive_JsonHelper.repl_line = Prims.int_one;
      FStar_Interactive_JsonHelper.repl_column = Prims.int_zero;
      FStar_Interactive_JsonHelper.repl_fname = fname;
      FStar_Interactive_JsonHelper.repl_deps_stack = [];
      FStar_Interactive_JsonHelper.repl_curmod = FStar_Pervasives_Native.None;
      FStar_Interactive_JsonHelper.repl_env = env1;
      FStar_Interactive_JsonHelper.repl_stdin = uu____257;
      FStar_Interactive_JsonHelper.repl_names =
        FStar_Interactive_CompletionTable.empty
    }
  
type optresponse =
  FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option
type either_gst_exit =
  (FStar_Interactive_JsonHelper.grepl_state,Prims.int) FStar_Util.either
let (invoke_full_lax :
  FStar_Interactive_JsonHelper.grepl_state ->
    Prims.string ->
      Prims.string -> Prims.bool -> (optresponse * either_gst_exit))
  =
  fun gst  ->
    fun fname  ->
      fun text  ->
        fun force  ->
          let aux uu____326 =
            FStar_Parser_ParseIt.add_vfs_entry fname text;
            (let uu____328 =
               let uu____335 = repl_state_init fname  in
               FStar_Interactive_PushHelper.full_lax text uu____335  in
             match uu____328 with
             | (diag1,st') ->
                 let repls =
                   FStar_Util.psmap_add
                     gst.FStar_Interactive_JsonHelper.grepl_repls fname st'
                    in
                 let diag2 =
                   if FStar_Util.is_some diag1
                   then diag1
                   else
                     (let uu____364 =
                        FStar_Interactive_JsonHelper.js_diag_clear fname  in
                      FStar_Pervasives_Native.Some uu____364)
                    in
                 (diag2,
                   (FStar_Util.Inl
                      (let uu___88_374 = gst  in
                       {
                         FStar_Interactive_JsonHelper.grepl_repls = repls;
                         FStar_Interactive_JsonHelper.grepl_stdin =
                           (uu___88_374.FStar_Interactive_JsonHelper.grepl_stdin)
                       }))))
             in
          let uu____375 =
            FStar_Util.psmap_try_find
              gst.FStar_Interactive_JsonHelper.grepl_repls fname
             in
          match uu____375 with
          | FStar_Pervasives_Native.Some uu____382 ->
              if force
              then aux ()
              else (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
          | FStar_Pervasives_Native.None  -> aux ()
  
let (run_query :
  FStar_Interactive_JsonHelper.grepl_state ->
    FStar_Interactive_JsonHelper.lquery -> (optresponse * either_gst_exit))
  =
  fun gst  ->
    fun q  ->
      match q with
      | FStar_Interactive_JsonHelper.Initialize (uu____410,uu____411) ->
          let uu____416 =
            FStar_Interactive_JsonHelper.resultResponse
              FStar_Interactive_JsonHelper.js_servcap
             in
          (uu____416, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Initialized  ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Shutdown  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Exit  ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inr Prims.int_zero))
      | FStar_Interactive_JsonHelper.Cancel id1 ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.FolderChange evt ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.ChangeConfig  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.ChangeWatch  ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Symbol sym ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.ExecCommand cmd ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DidOpen
          { FStar_Interactive_JsonHelper.fname = f;
            FStar_Interactive_JsonHelper.langId = uu____436;
            FStar_Interactive_JsonHelper.version = uu____437;
            FStar_Interactive_JsonHelper.text = t;_}
          -> invoke_full_lax gst f t false
      | FStar_Interactive_JsonHelper.DidChange (txid,content) ->
          (FStar_Parser_ParseIt.add_vfs_entry txid content;
           (FStar_Pervasives_Native.None, (FStar_Util.Inl gst)))
      | FStar_Interactive_JsonHelper.WillSave txid ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.WillSaveWait txid ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DidSave (f,t) ->
          invoke_full_lax gst f t true
      | FStar_Interactive_JsonHelper.DidClose txid ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Completion (txpos,ctx) ->
          let uu____470 =
            FStar_Util.psmap_try_find
              gst.FStar_Interactive_JsonHelper.grepl_repls
              txpos.FStar_Interactive_JsonHelper.path
             in
          (match uu____470 with
           | FStar_Pervasives_Native.Some st ->
               let uu____478 =
                 FStar_Interactive_QueryHelper.complookup st txpos  in
               (uu____478, (FStar_Util.Inl gst))
           | FStar_Pervasives_Native.None  ->
               (FStar_Interactive_JsonHelper.nullResponse,
                 (FStar_Util.Inl gst)))
      | FStar_Interactive_JsonHelper.Resolve  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Hover txpos ->
          let uu____483 =
            FStar_Util.psmap_try_find
              gst.FStar_Interactive_JsonHelper.grepl_repls
              txpos.FStar_Interactive_JsonHelper.path
             in
          (match uu____483 with
           | FStar_Pervasives_Native.Some st ->
               let uu____491 =
                 FStar_Interactive_QueryHelper.hoverlookup
                   st.FStar_Interactive_JsonHelper.repl_env txpos
                  in
               (uu____491, (FStar_Util.Inl gst))
           | FStar_Pervasives_Native.None  ->
               (FStar_Interactive_JsonHelper.nullResponse,
                 (FStar_Util.Inl gst)))
      | FStar_Interactive_JsonHelper.SignatureHelp txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Declaration txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Definition txpos ->
          let uu____499 =
            FStar_Util.psmap_try_find
              gst.FStar_Interactive_JsonHelper.grepl_repls
              txpos.FStar_Interactive_JsonHelper.path
             in
          (match uu____499 with
           | FStar_Pervasives_Native.Some st ->
               let uu____507 =
                 FStar_Interactive_QueryHelper.deflookup
                   st.FStar_Interactive_JsonHelper.repl_env txpos
                  in
               (uu____507, (FStar_Util.Inl gst))
           | FStar_Pervasives_Native.None  ->
               (FStar_Interactive_JsonHelper.nullResponse,
                 (FStar_Util.Inl gst)))
      | FStar_Interactive_JsonHelper.TypeDefinition txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Implementation txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.References  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DocumentHighlight txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DocumentSymbol  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.CodeAction  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.CodeLens  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.CodeLensResolve  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DocumentLink  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DocumentLinkResolve  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.DocumentColor  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.ColorPresentation  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Formatting  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.RangeFormatting  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.TypeFormatting  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.Rename  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.PrepareRename txpos ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.FoldingRange  ->
          (FStar_Interactive_JsonHelper.nullResponse, (FStar_Util.Inl gst))
      | FStar_Interactive_JsonHelper.BadProtocolMsg msg ->
          let uu____534 =
            let uu____535 =
              FStar_Interactive_JsonHelper.js_resperr
                FStar_Interactive_JsonHelper.MethodNotFound msg
               in
            FStar_Interactive_JsonHelper.errorResponse uu____535  in
          (uu____534, (FStar_Util.Inl gst))
  
let rec (parse_header_len :
  FStar_Util.stream_reader -> Prims.int -> Prims.int) =
  fun stream  ->
    fun len  ->
      let uu____552 = FStar_Util.read_line stream  in
      match uu____552 with
      | FStar_Pervasives_Native.Some s ->
          if FStar_Util.starts_with s "Content-Length: "
          then
            let uu____563 =
              let uu____565 = FStar_Util.substring_from s (Prims.of_int (16))
                 in
              FStar_Util.int_of_string uu____565  in
            parse_header_len stream uu____563
          else
            if FStar_Util.starts_with s "Content-Type: "
            then parse_header_len stream len
            else
              if s = ""
              then len
              else
                FStar_Exn.raise FStar_Interactive_JsonHelper.MalformedHeader
      | FStar_Pervasives_Native.None  ->
          FStar_Exn.raise FStar_Interactive_JsonHelper.InputExhausted
  
let rec (read_lsp_query :
  FStar_Util.stream_reader -> FStar_Interactive_JsonHelper.lsp_query) =
  fun stream  ->
    try
      (fun uu___190_594  ->
         match () with
         | () ->
             let n1 = parse_header_len stream Prims.int_zero  in
             let uu____598 = FStar_Util.nread stream n1  in
             (match uu____598 with
              | FStar_Pervasives_Native.Some s -> parse_lsp_query s
              | FStar_Pervasives_Native.None  ->
                  let uu____606 =
                    let uu____608 = FStar_Util.string_of_int n1  in
                    FStar_Util.format1 "Could not read %s bytes" uu____608
                     in
                  FStar_Interactive_JsonHelper.wrap_content_szerr uu____606))
        ()
    with
    | FStar_Interactive_JsonHelper.MalformedHeader  ->
        (FStar_Util.print_error "[E] Malformed Content Header\n";
         read_lsp_query stream)
    | FStar_Interactive_JsonHelper.InputExhausted  -> read_lsp_query stream
  
let rec (go : FStar_Interactive_JsonHelper.grepl_state -> Prims.int) =
  fun gst  ->
    let query = read_lsp_query gst.FStar_Interactive_JsonHelper.grepl_stdin
       in
    let uu____625 = run_query gst query.FStar_Interactive_JsonHelper.q  in
    match uu____625 with
    | (r,state_opt) ->
        ((match r with
          | FStar_Pervasives_Native.Some response ->
              let response' =
                FStar_Interactive_JsonHelper.json_of_response
                  query.FStar_Interactive_JsonHelper.query_id response
                 in
              (if false
               then
                 (let uu____639 = FStar_Util.string_of_json response'  in
                  FStar_Util.print1_error "<<< %s\n" uu____639)
               else ();
               FStar_Interactive_JsonHelper.write_jsonrpc response')
          | FStar_Pervasives_Native.None  -> ());
         (match state_opt with
          | FStar_Util.Inl gst' -> go gst'
          | FStar_Util.Inr exitcode -> exitcode))
  
let (start_server : unit -> unit) =
  fun uu____655  ->
    let uu____656 =
      let uu____658 =
        let uu____659 = FStar_Util.psmap_empty ()  in
        let uu____662 = FStar_Util.open_stdin ()  in
        {
          FStar_Interactive_JsonHelper.grepl_repls = uu____659;
          FStar_Interactive_JsonHelper.grepl_stdin = uu____662
        }  in
      go uu____658  in
    FStar_All.exit uu____656
  