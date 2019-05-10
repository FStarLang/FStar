#light "off"
module FStar.Interactive.Lsp

open FStar
open FStar.All
open FStar.Errors
open FStar.Util
open FStar.JsonHelper

module CTable = FStar.Interactive.CompletionTable

(* Request *)

// May throw, but is only called by branches that have a "params"
let arg k r = assoc k (assoc "params" r |> js_assoc)

let unpack_lsp_query json : lsp_query =
  // Exceptions for these two are caught at `deserialize_lsp_query`
  let r = json |> js_assoc in
  let qid = assoc "id" r |> js_str in

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
    unpack_lsp_query js_query
  with
  // If `unpack_lsp_query` throws, it does so without qid
  | InvalidQuery msg -> { query_id = "?"; q = BadProtocolMsg msg }
  | UnexpectedJsonType (expected, got) -> wrap_jsfail "?" expected got

let parse_lsp_query query_str : lsp_query =
  match Util.json_of_string query_str with
  | None -> { query_id = "?"; q = BadProtocolMsg "Json parsing failed" }
  | Some request -> deserialize_lsp_query request

(* Repl and response *)

type repl_state = { repl_line: int; repl_column: int; repl_stdin: stream_reader;
                    repl_last: lquery; repl_names: CTable.table }

let run_exit (st: repl_state) : int = if st.repl_last <> Shutdown then 1 else 0

let run_query (st: repl_state) (q: lquery) : either<json, json> * either<repl_state, int> =
  match q with
  | Initialize (pid, rootUri) -> (Inl JsonNull, Inl st)
  | Initialized -> (Inl JsonNull, Inl st)
  | Shutdown -> (Inl JsonNull, Inl st)
  | Exit -> (Inl JsonNull, Inr (run_exit st))
  | Cancel id -> (Inl JsonNull, Inl st)
  | FolderChange evt -> (Inl JsonNull, Inl st)
  | ChangeConfig -> (Inl JsonNull, Inl st)
  | ChangeWatch -> (Inl JsonNull, Inl st)
  | Symbol sym -> (Inl JsonNull, Inl st)
  | ExecCommand cmd -> (Inl JsonNull, Inl st)
  | DidOpen item -> (Inl JsonNull, Inl st)
  | DidChange -> (Inl JsonNull, Inl st)
  | WillSave txid -> (Inl JsonNull, Inl st)
  | DidSave txid -> (Inl JsonNull, Inl st)
  | DidClose txid -> (Inl JsonNull, Inl st)
  | Completion ctx -> (Inl JsonNull, Inl st)
  | Resolve -> (Inl JsonNull, Inl st)
  | Hover -> (Inl JsonNull, Inl st)
  | SignatureHelp -> (Inl JsonNull, Inl st)
  | Declaration -> (Inl JsonNull, Inl st)
  | Definition -> (Inl JsonNull, Inl st)
  | Implementation -> (Inl JsonNull, Inl st)
  | References -> (Inl JsonNull, Inl st)
  | DocumentHighlight -> (Inl JsonNull, Inl st)
  | DocumentSymbol -> (Inl JsonNull, Inl st)
  | CodeAction -> (Inl JsonNull, Inl st)
  | CodeLens -> (Inl JsonNull, Inl st)
  | DocumentLink -> (Inl JsonNull, Inl st)
  | DocumentColor -> (Inl JsonNull, Inl st)
  | ColorPresentation -> (Inl JsonNull, Inl st)
  | Formatting -> (Inl JsonNull, Inl st)
  | RangeFormatting -> (Inl JsonNull, Inl st)
  | TypeFormatting -> (Inl JsonNull, Inl st)
  | Rename -> (Inl JsonNull, Inl st)
  | PrepareRename -> (Inl JsonNull, Inl st)
  | FoldingRange -> (Inl JsonNull, Inl st)
  | BadProtocolMsg msg -> (Inr (js_resperr MethodNotFound msg), Inl st)

let json_of_response (qid: string) response =
  let qid = JsonStr qid in
  match response with
  | Inl result -> JsonAssoc [("id", qid); ("result", result)]
  | Inr err -> JsonAssoc [("id", qid); ("error", err)]

let read_lsp_query (stream: stream_reader) : lsp_query =
  match Util.read_line stream with
  | None -> exit 0
  | Some line -> parse_lsp_query line

let rec go (st: repl_state) : int =
  let query = read_lsp_query st.repl_stdin in
  let response, state_opt = run_query st query.q in
  write_json (json_of_response query.query_id response);
  match state_opt with
  | Inl st' -> go st'
  | Inr exitcode -> exitcode

// The initial REPL state specifies Exit as the last message received,
// without loss of generality
let initial_repl_state : repl_state =
  { repl_line = 1; repl_column = 0; repl_stdin = open_stdin ();
    repl_last = Exit; repl_names = CompletionTable.empty }

let start_server () : unit = exit (go initial_repl_state)
