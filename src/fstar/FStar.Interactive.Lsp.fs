#light "off"
module FStar.Interactive.Lsp

open FStar
open FStar.All
open FStar.Errors
open FStar.Util
open FStar.JsonHelper

(* Request *)

// May throw, but is only called by branches that have a "params"
let arg k r = assoc k (assoc "params" r |> js_assoc)

// nothrow
let unpack_lsp_query (r : list<(string * json)>) : lsp_query =
  let qid = try_assoc "id" r |> Util.map_option js_str_int in // noexcept

  // If we make it this far, exceptions will come with qid info.
  // Wrap in `try` because all `js_*` functions and `assoc` throw
  try
    let method = assoc "method" r |> js_str in
    { query_id = qid;
      q = match method with
          | "initialize" -> Initialize (arg "processId" r |> js_int,
                                        arg "rootUri" r |> js_str)
          | "initialized" -> Initialized
          | "shutdown" -> Shutdown
          | "exit" -> Exit
          | "$/cancelRequest" -> Cancel (arg "id" r |> js_str)
          | "workspace/didChangeWorkspaceFolders" -> FolderChange
                                                     (arg "event" r |> js_wsch_event)
          | "workspace/didChangeConfiguration" -> ChangeConfig
          | "workspace/didChangeWatchedFiles" -> ChangeWatch
          | "workspace/symbol" -> Symbol (arg "query" r |> js_str)
          | "workspace/executeCommand" -> ExecCommand
                                          (arg "command" r |> js_str)
          | "textDocument/didOpen" -> DidOpen (arg "textDocument" r |> js_txdoc_item)
          | "textDocument/didChange" -> DidChange
          | "textDocument/willSave" -> WillSave (arg "textDocument" r |> js_str)
          | "textDocument/didSave" -> DidSave (arg "textDocument" r |> js_str)
          | "textDocument/didClose" -> DidClose (arg "textDocument" r |> js_str)
          | "textDocument/completion" -> Completion (arg "context" r |>
                                                     js_compl_context)
          | "completionItem/resolve" -> Resolve
          | "textDocument/hover" -> Hover
          | "textDocument/signatureHelp" -> SignatureHelp
          | "textDocument/declaration" -> Declaration
          | "textDocument/definition" -> Definition
          | "textDocument/implementation" -> Implementation
          | "textDocument/references" -> References
          | "textDocument/documentHighlight" -> DocumentHighlight
          | "textDocument/documentSymbol" -> DocumentSymbol
          | "textDocument/codeAction" -> CodeAction
          | "textDocument/codeLens" -> CodeLens
          | "textDocument/documentLink" -> DocumentLink
          | "textDocument/documentColor" -> DocumentColor
          | "textDocument/colorPresentation" -> ColorPresentation
          | "textDocument/formatting" -> Formatting
          | "textDocument/rangeFormatting" -> RangeFormatting
          | "textDocument/onTypeFormatting" -> TypeFormatting
          | "textDocument/rename" -> Rename
          | "textDocument/prepareRename" -> PrepareRename
          | "textDocument/foldingRange" -> FoldingRange
          | m -> BadProtocolMsg (Util.format1 "Unknown method '%s'" m) }
  with
  | MissingKey msg -> { query_id = qid; q = BadProtocolMsg msg }
  | UnexpectedJsonType (expected, got) -> wrap_jsfail qid expected got

let deserialize_lsp_query js_query : lsp_query =
  try
    unpack_lsp_query (js_query |> js_assoc)
  with
  // This is the only excpetion that js_assoc is allowed to throw
  | UnexpectedJsonType (expected, got) -> wrap_jsfail None expected got

let parse_lsp_query query_str : lsp_query =
  Util.print1_error ">>> %s\n" query_str;
  match Util.json_of_string query_str with
  | None -> { query_id = None; q = BadProtocolMsg "Json parsing failed" }
  | Some request -> deserialize_lsp_query request

(* Repl and response *)

let run_exit (st: repl_state) : int = if st.repl_last <> Shutdown then 1 else 0

let run_query (st: repl_state) (q: lquery) : optresponse * either_st_exit =
  match q with
  | Initialize (pid, rootUri) -> (Some (Inl js_servcap), Inl st)
  | Initialized -> (None, Inl st)
  | Shutdown -> (Some (Inl JsonNull), Inl st)
  | Exit -> (None, Inr (run_exit st))
  | Cancel id -> (Some (Inl JsonNull), Inl st)
  | FolderChange evt -> (Some (Inl JsonNull), Inl st)
  | ChangeConfig -> (Some (Inl JsonNull), Inl st)
  | ChangeWatch -> (Some (Inl JsonNull), Inl st)
  | Symbol sym -> (Some (Inl JsonNull), Inl st)
  | ExecCommand cmd -> (Some (Inl JsonNull), Inl st)
  | DidOpen item -> (Some (Inl JsonNull), Inl st)
  | DidChange -> (Some (Inl JsonNull), Inl st)
  | WillSave txid -> (Some (Inl JsonNull), Inl st)
  | DidSave txid -> (Some (Inl JsonNull), Inl st)
  | DidClose txid -> (Some (Inl JsonNull), Inl st)
  | Completion ctx -> (Some (Inl JsonNull), Inl st)
  | Resolve -> (Some (Inl JsonNull), Inl st)
  | Hover -> (Some (Inl JsonNull), Inl st)
  | SignatureHelp -> (Some (Inl JsonNull), Inl st)
  | Declaration -> (Some (Inl JsonNull), Inl st)
  | Definition -> (Some (Inl JsonNull), Inl st)
  | Implementation -> (Some (Inl JsonNull), Inl st)
  | References -> (Some (Inl JsonNull), Inl st)
  | DocumentHighlight -> (Some (Inl JsonNull), Inl st)
  | DocumentSymbol -> (Some (Inl JsonNull), Inl st)
  | CodeAction -> (Some (Inl JsonNull), Inl st)
  | CodeLens -> (Some (Inl JsonNull), Inl st)
  | DocumentLink -> (Some (Inl JsonNull), Inl st)
  | DocumentColor -> (Some (Inl JsonNull), Inl st)
  | ColorPresentation -> (Some (Inl JsonNull), Inl st)
  | Formatting -> (Some (Inl JsonNull), Inl st)
  | RangeFormatting -> (Some (Inl JsonNull), Inl st)
  | TypeFormatting -> (Some (Inl JsonNull), Inl st)
  | Rename -> (Some (Inl JsonNull), Inl st)
  | PrepareRename -> (Some (Inl JsonNull), Inl st)
  | FoldingRange -> (Some (Inl JsonNull), Inl st)
  | BadProtocolMsg msg -> (Some (Inr (js_resperr MethodNotFound msg)), Inl st)

// Raises exceptions, but all of them are caught
let rec parse_header_len (stream: stream_reader) (len: int): int =
  // Non-blocking read
  match Util.read_line stream with
  | Some s ->
    if Util.starts_with s "Content-Length: " then
      parse_header_len stream (Util.int_of_string (Util.substring_from s 16))
    else if Util.starts_with s "Content-Type: " then
      parse_header_len stream len
    else if s = "" then
      len
    else
      raise MalformedHeader
  | None -> raise InputExhausted

let rec read_lsp_query (stream: stream_reader) : lsp_query =
  try
    let n = parse_header_len stream 0 in
    match Util.nread stream n with
    | Some s -> parse_lsp_query s
    | None -> wrap_content_szerr (Util.format1 "Could not read %s bytes" (Util.string_of_int n))
  with
  // At no cost should the server go down
  | MalformedHeader -> Util.print_error "[E] Malformed Content Header\n"; read_lsp_query stream
  | InputExhausted -> read_lsp_query stream

let rec go (st: repl_state) : int =
  let query = read_lsp_query st.repl_stdin in
  let r, state_opt = run_query st query.q in
  (match r with
   | Some response -> (let response' = json_of_response query.query_id response in
                       Util.print1_error "<<< %s\n" (Util.string_of_json response');
                       write_jsonrpc response')
   | None -> (Util.print_error "<<< ()\n")); // Don't respond
  match state_opt with
  | Inl st' -> go st'
  | Inr exitcode -> exitcode

// The initial REPL state specifies Exit as the last message received,
// without loss of generality
let initial_repl_state : repl_state =
  { repl_line = 1; repl_column = 0; repl_stdin = open_stdin ();
    repl_last = Exit; repl_names = CompletionTable.empty }

let start_server () : unit = exit (go initial_repl_state)
