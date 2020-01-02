
open Prims
open FStar_Pervasives

let unpack_lsp_query : (Prims.string * FStar_Util.json) Prims.list  ->  FStar_Interactive_JsonHelper.lsp_query = (fun r -> (

let qid = (

let uu____23 = (FStar_Interactive_JsonHelper.try_assoc "id" r)
in (FStar_All.pipe_right uu____23 (FStar_Util.map_option FStar_Interactive_JsonHelper.js_str_int)))
in (FStar_All.try_with (fun uu___3_36 -> (match (()) with
| () -> begin
(

let method_37 = (

let uu____39 = (FStar_Interactive_JsonHelper.assoc "method" r)
in (FStar_All.pipe_right uu____39 FStar_Interactive_JsonHelper.js_str))
in (

let uu____42 = (match (method_37) with
| "initialize" -> begin
(

let uu____44 = (

let uu____51 = (

let uu____53 = (FStar_Interactive_JsonHelper.arg "processId" r)
in (FStar_All.pipe_right uu____53 FStar_Interactive_JsonHelper.js_int))
in (

let uu____56 = (

let uu____58 = (FStar_Interactive_JsonHelper.arg "rootUri" r)
in (FStar_All.pipe_right uu____58 FStar_Interactive_JsonHelper.js_str))
in ((uu____51), (uu____56))))
in FStar_Interactive_JsonHelper.Initialize (uu____44))
end
| "initialized" -> begin
FStar_Interactive_JsonHelper.Initialized
end
| "shutdown" -> begin
FStar_Interactive_JsonHelper.Shutdown
end
| "exit" -> begin
FStar_Interactive_JsonHelper.Exit
end
| "$/cancelRequest" -> begin
(

let uu____67 = (

let uu____69 = (FStar_Interactive_JsonHelper.arg "id" r)
in (FStar_All.pipe_right uu____69 FStar_Interactive_JsonHelper.js_str_int))
in FStar_Interactive_JsonHelper.Cancel (uu____67))
end
| "workspace/didChangeWorkspaceFolders" -> begin
(

let uu____73 = (

let uu____74 = (FStar_Interactive_JsonHelper.arg "event" r)
in (FStar_All.pipe_right uu____74 FStar_Interactive_JsonHelper.js_wsch_event))
in FStar_Interactive_JsonHelper.FolderChange (uu____73))
end
| "workspace/didChangeConfiguration" -> begin
FStar_Interactive_JsonHelper.ChangeConfig
end
| "workspace/didChangeWatchedFiles" -> begin
FStar_Interactive_JsonHelper.ChangeWatch
end
| "workspace/symbol" -> begin
(

let uu____79 = (

let uu____81 = (FStar_Interactive_JsonHelper.arg "query" r)
in (FStar_All.pipe_right uu____81 FStar_Interactive_JsonHelper.js_str))
in FStar_Interactive_JsonHelper.Symbol (uu____79))
end
| "workspace/executeCommand" -> begin
(

let uu____85 = (

let uu____87 = (FStar_Interactive_JsonHelper.arg "command" r)
in (FStar_All.pipe_right uu____87 FStar_Interactive_JsonHelper.js_str))
in FStar_Interactive_JsonHelper.ExecCommand (uu____85))
end
| "textDocument/didOpen" -> begin
(

let uu____91 = (

let uu____92 = (FStar_Interactive_JsonHelper.arg "textDocument" r)
in (FStar_All.pipe_right uu____92 FStar_Interactive_JsonHelper.js_txdoc_item))
in FStar_Interactive_JsonHelper.DidOpen (uu____91))
end
| "textDocument/didChange" -> begin
(

let uu____95 = (

let uu____102 = (FStar_Interactive_JsonHelper.js_txdoc_id r)
in (

let uu____104 = (

let uu____106 = (FStar_Interactive_JsonHelper.arg "contentChanges" r)
in (FStar_All.pipe_right uu____106 FStar_Interactive_JsonHelper.js_contentch))
in ((uu____102), (uu____104))))
in FStar_Interactive_JsonHelper.DidChange (uu____95))
end
| "textDocument/willSave" -> begin
(

let uu____112 = (FStar_Interactive_JsonHelper.js_txdoc_id r)
in FStar_Interactive_JsonHelper.WillSave (uu____112))
end
| "textDocument/willSaveWaitUntil" -> begin
(

let uu____115 = (FStar_Interactive_JsonHelper.js_txdoc_id r)
in FStar_Interactive_JsonHelper.WillSaveWait (uu____115))
end
| "textDocument/didSave" -> begin
(

let uu____118 = (

let uu____125 = (FStar_Interactive_JsonHelper.js_txdoc_id r)
in (

let uu____127 = (

let uu____129 = (FStar_Interactive_JsonHelper.arg "text" r)
in (FStar_All.pipe_right uu____129 FStar_Interactive_JsonHelper.js_str))
in ((uu____125), (uu____127))))
in FStar_Interactive_JsonHelper.DidSave (uu____118))
end
| "textDocument/didClose" -> begin
(

let uu____135 = (FStar_Interactive_JsonHelper.js_txdoc_id r)
in FStar_Interactive_JsonHelper.DidClose (uu____135))
end
| "textDocument/completion" -> begin
(

let uu____138 = (

let uu____143 = (FStar_Interactive_JsonHelper.js_txdoc_pos r)
in (

let uu____144 = (

let uu____145 = (FStar_Interactive_JsonHelper.arg "context" r)
in (FStar_All.pipe_right uu____145 FStar_Interactive_JsonHelper.js_compl_context))
in ((uu____143), (uu____144))))
in FStar_Interactive_JsonHelper.Completion (uu____138))
end
| "completionItem/resolve" -> begin
FStar_Interactive_JsonHelper.Resolve
end
| "textDocument/hover" -> begin
(

let uu____149 = (FStar_Interactive_JsonHelper.js_txdoc_pos r)
in FStar_Interactive_JsonHelper.Hover (uu____149))
end
| "textDocument/signatureHelp" -> begin
(

let uu____151 = (FStar_Interactive_JsonHelper.js_txdoc_pos r)
in FStar_Interactive_JsonHelper.SignatureHelp (uu____151))
end
| "textDocument/declaration" -> begin
(

let uu____153 = (FStar_Interactive_JsonHelper.js_txdoc_pos r)
in FStar_Interactive_JsonHelper.Declaration (uu____153))
end
| "textDocument/definition" -> begin
(

let uu____155 = (FStar_Interactive_JsonHelper.js_txdoc_pos r)
in FStar_Interactive_JsonHelper.Definition (uu____155))
end
| "textDocument/typeDefinition" -> begin
(

let uu____157 = (FStar_Interactive_JsonHelper.js_txdoc_pos r)
in FStar_Interactive_JsonHelper.TypeDefinition (uu____157))
end
| "textDocument/implementation" -> begin
(

let uu____159 = (FStar_Interactive_JsonHelper.js_txdoc_pos r)
in FStar_Interactive_JsonHelper.Implementation (uu____159))
end
| "textDocument/references" -> begin
FStar_Interactive_JsonHelper.References
end
| "textDocument/documentHighlight" -> begin
(

let uu____162 = (FStar_Interactive_JsonHelper.js_txdoc_pos r)
in FStar_Interactive_JsonHelper.DocumentHighlight (uu____162))
end
| "textDocument/documentSymbol" -> begin
FStar_Interactive_JsonHelper.DocumentSymbol
end
| "textDocument/codeAction" -> begin
FStar_Interactive_JsonHelper.CodeAction
end
| "textDocument/codeLens" -> begin
FStar_Interactive_JsonHelper.CodeLens
end
| "codeLens/resolve" -> begin
FStar_Interactive_JsonHelper.CodeLensResolve
end
| "textDocument/documentLink" -> begin
FStar_Interactive_JsonHelper.DocumentLink
end
| "documentLink/resolve" -> begin
FStar_Interactive_JsonHelper.DocumentLinkResolve
end
| "textDocument/documentColor" -> begin
FStar_Interactive_JsonHelper.DocumentColor
end
| "textDocument/colorPresentation" -> begin
FStar_Interactive_JsonHelper.ColorPresentation
end
| "textDocument/formatting" -> begin
FStar_Interactive_JsonHelper.Formatting
end
| "textDocument/rangeFormatting" -> begin
FStar_Interactive_JsonHelper.RangeFormatting
end
| "textDocument/onTypeFormatting" -> begin
FStar_Interactive_JsonHelper.TypeFormatting
end
| "textDocument/rename" -> begin
FStar_Interactive_JsonHelper.Rename
end
| "textDocument/prepareRename" -> begin
(

let uu____176 = (FStar_Interactive_JsonHelper.js_txdoc_pos r)
in FStar_Interactive_JsonHelper.PrepareRename (uu____176))
end
| "textDocument/foldingRange" -> begin
FStar_Interactive_JsonHelper.FoldingRange
end
| m -> begin
(

let uu____180 = (FStar_Util.format1 "Unknown method \'%s\'" m)
in FStar_Interactive_JsonHelper.BadProtocolMsg (uu____180))
end)
in {FStar_Interactive_JsonHelper.query_id = qid; FStar_Interactive_JsonHelper.q = uu____42}))
end)) (fun uu___2_185 -> (match (uu___2_185) with
| FStar_Interactive_JsonHelper.MissingKey (msg) -> begin
{FStar_Interactive_JsonHelper.query_id = qid; FStar_Interactive_JsonHelper.q = FStar_Interactive_JsonHelper.BadProtocolMsg (msg)}
end
| FStar_Interactive_JsonHelper.UnexpectedJsonType (expected, got) -> begin
(FStar_Interactive_JsonHelper.wrap_jsfail qid expected got)
end)))))


let deserialize_lsp_query : FStar_Util.json  ->  FStar_Interactive_JsonHelper.lsp_query = (fun js_query -> (FStar_All.try_with (fun uu___57_200 -> (match (()) with
| () -> begin
(

let uu____201 = (FStar_All.pipe_right js_query FStar_Interactive_JsonHelper.js_assoc)
in (unpack_lsp_query uu____201))
end)) (fun uu___56_219 -> (match (uu___56_219) with
| FStar_Interactive_JsonHelper.UnexpectedJsonType (expected, got) -> begin
(FStar_Interactive_JsonHelper.wrap_jsfail FStar_Pervasives_Native.None expected got)
end))))


let parse_lsp_query : Prims.string  ->  FStar_Interactive_JsonHelper.lsp_query = (fun query_str -> (

let uu____234 = (FStar_Util.json_of_string query_str)
in (match (uu____234) with
| FStar_Pervasives_Native.None -> begin
{FStar_Interactive_JsonHelper.query_id = FStar_Pervasives_Native.None; FStar_Interactive_JsonHelper.q = FStar_Interactive_JsonHelper.BadProtocolMsg ("Json parsing failed")}
end
| FStar_Pervasives_Native.Some (request) -> begin
(deserialize_lsp_query request)
end)))


let repl_state_init : Prims.string  ->  FStar_Interactive_JsonHelper.repl_state = (fun fname -> (

let intial_range = (

let uu____249 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____252 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range fname uu____249 uu____252)))
in (

let env = (FStar_Universal.init_env FStar_Parser_Dep.empty_deps)
in (

let env1 = (FStar_TypeChecker_Env.set_range env intial_range)
in (

let uu____257 = (FStar_Util.open_stdin ())
in {FStar_Interactive_JsonHelper.repl_line = (Prims.parse_int "1"); FStar_Interactive_JsonHelper.repl_column = (Prims.parse_int "0"); FStar_Interactive_JsonHelper.repl_fname = fname; FStar_Interactive_JsonHelper.repl_deps_stack = []; FStar_Interactive_JsonHelper.repl_curmod = FStar_Pervasives_Native.None; FStar_Interactive_JsonHelper.repl_env = env1; FStar_Interactive_JsonHelper.repl_stdin = uu____257; FStar_Interactive_JsonHelper.repl_names = FStar_Interactive_CompletionTable.empty})))))


type optresponse =
FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option


type either_gst_exit =
(FStar_Interactive_JsonHelper.grepl_state, Prims.int) FStar_Util.either


let invoke_full_lax : FStar_Interactive_JsonHelper.grepl_state  ->  Prims.string  ->  Prims.string  ->  Prims.bool  ->  (optresponse * either_gst_exit) = (fun gst fname text force1 -> (

let aux = (fun uu____326 -> ((FStar_Parser_ParseIt.add_vfs_entry fname text);
(

let uu____328 = (

let uu____335 = (repl_state_init fname)
in (FStar_Interactive_PushHelper.full_lax text uu____335))
in (match (uu____328) with
| (diag1, st') -> begin
(

let repls = (FStar_Util.psmap_add gst.FStar_Interactive_JsonHelper.grepl_repls fname st')
in (

let diag2 = (match ((FStar_Util.is_some diag1)) with
| true -> begin
diag1
end
| uu____362 -> begin
(

let uu____364 = (FStar_Interactive_JsonHelper.js_diag_clear fname)
in FStar_Pervasives_Native.Some (uu____364))
end)
in ((diag2), (FStar_Util.Inl ((

let uu___88_374 = gst
in {FStar_Interactive_JsonHelper.grepl_repls = repls; FStar_Interactive_JsonHelper.grepl_stdin = uu___88_374.FStar_Interactive_JsonHelper.grepl_stdin}))))))
end));
))
in (

let uu____375 = (FStar_Util.psmap_try_find gst.FStar_Interactive_JsonHelper.grepl_repls fname)
in (match (uu____375) with
| FStar_Pervasives_Native.Some (uu____382) -> begin
(match (force1) with
| true -> begin
(aux ())
end
| uu____388 -> begin
((FStar_Pervasives_Native.None), (FStar_Util.Inl (gst)))
end)
end
| FStar_Pervasives_Native.None -> begin
(aux ())
end))))


let run_query : FStar_Interactive_JsonHelper.grepl_state  ->  FStar_Interactive_JsonHelper.lquery  ->  (optresponse * either_gst_exit) = (fun gst q -> (match (q) with
| FStar_Interactive_JsonHelper.Initialize (uu____410, uu____411) -> begin
(

let uu____416 = (FStar_Interactive_JsonHelper.resultResponse FStar_Interactive_JsonHelper.js_servcap)
in ((uu____416), (FStar_Util.Inl (gst))))
end
| FStar_Interactive_JsonHelper.Initialized -> begin
((FStar_Pervasives_Native.None), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.Shutdown -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.Exit -> begin
((FStar_Pervasives_Native.None), (FStar_Util.Inr ((Prims.parse_int "0"))))
end
| FStar_Interactive_JsonHelper.Cancel (id1) -> begin
((FStar_Pervasives_Native.None), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.FolderChange (evt) -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.ChangeConfig -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.ChangeWatch -> begin
((FStar_Pervasives_Native.None), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.Symbol (sym) -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.ExecCommand (cmd) -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.DidOpen ({FStar_Interactive_JsonHelper.fname = f; FStar_Interactive_JsonHelper.langId = uu____436; FStar_Interactive_JsonHelper.version = uu____437; FStar_Interactive_JsonHelper.text = t}) -> begin
(invoke_full_lax gst f t false)
end
| FStar_Interactive_JsonHelper.DidChange (txid, content) -> begin
((FStar_Parser_ParseIt.add_vfs_entry txid content);
((FStar_Pervasives_Native.None), (FStar_Util.Inl (gst)));
)
end
| FStar_Interactive_JsonHelper.WillSave (txid) -> begin
((FStar_Pervasives_Native.None), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.WillSaveWait (txid) -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.DidSave (f, t) -> begin
(invoke_full_lax gst f t true)
end
| FStar_Interactive_JsonHelper.DidClose (txid) -> begin
((FStar_Pervasives_Native.None), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.Completion (txpos, ctx) -> begin
(

let uu____470 = (FStar_Util.psmap_try_find gst.FStar_Interactive_JsonHelper.grepl_repls txpos.FStar_Interactive_JsonHelper.path)
in (match (uu____470) with
| FStar_Pervasives_Native.Some (st) -> begin
(

let uu____478 = (FStar_Interactive_QueryHelper.complookup st txpos)
in ((uu____478), (FStar_Util.Inl (gst))))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end))
end
| FStar_Interactive_JsonHelper.Resolve -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.Hover (txpos) -> begin
(

let uu____483 = (FStar_Util.psmap_try_find gst.FStar_Interactive_JsonHelper.grepl_repls txpos.FStar_Interactive_JsonHelper.path)
in (match (uu____483) with
| FStar_Pervasives_Native.Some (st) -> begin
(

let uu____491 = (FStar_Interactive_QueryHelper.hoverlookup st.FStar_Interactive_JsonHelper.repl_env txpos)
in ((uu____491), (FStar_Util.Inl (gst))))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end))
end
| FStar_Interactive_JsonHelper.SignatureHelp (txpos) -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.Declaration (txpos) -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.Definition (txpos) -> begin
(

let uu____499 = (FStar_Util.psmap_try_find gst.FStar_Interactive_JsonHelper.grepl_repls txpos.FStar_Interactive_JsonHelper.path)
in (match (uu____499) with
| FStar_Pervasives_Native.Some (st) -> begin
(

let uu____507 = (FStar_Interactive_QueryHelper.deflookup st.FStar_Interactive_JsonHelper.repl_env txpos)
in ((uu____507), (FStar_Util.Inl (gst))))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end))
end
| FStar_Interactive_JsonHelper.TypeDefinition (txpos) -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.Implementation (txpos) -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.References -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.DocumentHighlight (txpos) -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.DocumentSymbol -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.CodeAction -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.CodeLens -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.CodeLensResolve -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.DocumentLink -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.DocumentLinkResolve -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.DocumentColor -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.ColorPresentation -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.Formatting -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.RangeFormatting -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.TypeFormatting -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.Rename -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.PrepareRename (txpos) -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.FoldingRange -> begin
((FStar_Interactive_JsonHelper.nullResponse), (FStar_Util.Inl (gst)))
end
| FStar_Interactive_JsonHelper.BadProtocolMsg (msg) -> begin
(

let uu____534 = (

let uu____535 = (FStar_Interactive_JsonHelper.js_resperr FStar_Interactive_JsonHelper.MethodNotFound msg)
in (FStar_Interactive_JsonHelper.errorResponse uu____535))
in ((uu____534), (FStar_Util.Inl (gst))))
end))


let rec parse_header_len : FStar_Util.stream_reader  ->  Prims.int  ->  Prims.int = (fun stream len -> (

let uu____552 = (FStar_Util.read_line stream)
in (match (uu____552) with
| FStar_Pervasives_Native.Some (s) -> begin
(match ((FStar_Util.starts_with s "Content-Length: ")) with
| true -> begin
(

let uu____563 = (

let uu____565 = (FStar_Util.substring_from s (Prims.parse_int "16"))
in (FStar_Util.int_of_string uu____565))
in (parse_header_len stream uu____563))
end
| uu____568 -> begin
(match ((FStar_Util.starts_with s "Content-Type: ")) with
| true -> begin
(parse_header_len stream len)
end
| uu____573 -> begin
(match ((Prims.op_Equality s "")) with
| true -> begin
len
end
| uu____579 -> begin
(FStar_Exn.raise FStar_Interactive_JsonHelper.MalformedHeader)
end)
end)
end)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise FStar_Interactive_JsonHelper.InputExhausted)
end)))


let rec read_lsp_query : FStar_Util.stream_reader  ->  FStar_Interactive_JsonHelper.lsp_query = (fun stream -> (FStar_All.try_with (fun uu___190_594 -> (match (()) with
| () -> begin
(

let n1 = (parse_header_len stream (Prims.parse_int "0"))
in (

let uu____598 = (FStar_Util.nread stream n1)
in (match (uu____598) with
| FStar_Pervasives_Native.Some (s) -> begin
(parse_lsp_query s)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____606 = (

let uu____608 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "Could not read %s bytes" uu____608))
in (FStar_Interactive_JsonHelper.wrap_content_szerr uu____606))
end)))
end)) (fun uu___189_613 -> (match (uu___189_613) with
| FStar_Interactive_JsonHelper.MalformedHeader -> begin
((FStar_Util.print_error "[E] Malformed Content Header\n");
(read_lsp_query stream);
)
end
| FStar_Interactive_JsonHelper.InputExhausted -> begin
(read_lsp_query stream)
end))))


let rec go : FStar_Interactive_JsonHelper.grepl_state  ->  Prims.int = (fun gst -> (

let query = (read_lsp_query gst.FStar_Interactive_JsonHelper.grepl_stdin)
in (

let uu____625 = (run_query gst query.FStar_Interactive_JsonHelper.q)
in (match (uu____625) with
| (r, state_opt) -> begin
((match (r) with
| FStar_Pervasives_Native.Some (response) -> begin
(

let response' = (FStar_Interactive_JsonHelper.json_of_response query.FStar_Interactive_JsonHelper.query_id response)
in ((match (false) with
| true -> begin
(

let uu____639 = (FStar_Util.string_of_json response')
in (FStar_Util.print1_error "<<< %s\n" uu____639))
end
| uu____642 -> begin
()
end);
(FStar_Interactive_JsonHelper.write_jsonrpc response');
))
end
| FStar_Pervasives_Native.None -> begin
()
end);
(match (state_opt) with
| FStar_Util.Inl (gst') -> begin
(go gst')
end
| FStar_Util.Inr (exitcode) -> begin
exitcode
end);
)
end))))


let start_server : unit  ->  unit = (fun uu____655 -> (

let uu____656 = (

let uu____658 = (

let uu____659 = (FStar_Util.psmap_empty ())
in (

let uu____662 = (FStar_Util.open_stdin ())
in {FStar_Interactive_JsonHelper.grepl_repls = uu____659; FStar_Interactive_JsonHelper.grepl_stdin = uu____662}))
in (go uu____658))
in (FStar_All.exit uu____656)))




