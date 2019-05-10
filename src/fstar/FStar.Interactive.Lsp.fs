#light "off"
module FStar.Interactive.Lsp

open FStar
open FStar.All
open FStar.Errors
open FStar.Util
open FStar.JsonHelper

module CTable = FStar.Interactive.CompletionTable

(* Request *)

let unpack_lsp_query json : lsp_query =
  // Exceptions for these two are caught at `deserialize_lsp_query`
  let request = json |> js_assoc in
  let qid = assoc "id" request |> js_str in

  // If we make it this far, exceptions will come with qid info.
  // Wrap in `try` because all `js_*` functions and `assoc` throw
  try
    let method = assoc "method" request |> js_str in
    let p = assoc "params" request |> js_assoc in
    let arg k = assoc k p in
    { query_id = qid;
      q = match method with
          | "initialize" -> Initialize (arg "processId" |> js_int,
                                        arg "rootUri" |> js_str)
          | "initialized" -> Initialized
          | "shutdown" -> Shutdown
          | "exit" -> Exit
          | "$/cancelRequest" -> Cancel (arg "id" |> js_str)
          | "workspace/didChangeWorkspaceFolders" -> FolderChange
                                                     (arg "event" |> js_wsch_event)
          | "workspace/didChangeConfiguration" -> ChangeConfig
          | "workspace/didChangeWatchedFiles" -> ChangeWatch
          | "workspace/symbol" -> Symbol (arg "query" |> js_str)
          | "workspace/executeCommand" -> ExecCommand
                                          (arg "command" |> js_str)
          | "textDocument/didOpen" -> DidOpen (arg "textDocument" |> js_txdoc_item)
          | "textDocument/didChange" -> DidChange
          | "textDocument/willSave" -> WillSave (arg "textDocument" |> js_str)
          | "textDocument/didSave" -> DidSave (arg "textDocument" |> js_str)
          | "textDocument/didClose" -> DidClose (arg "textDocument" |> js_str)
          | "textDocument/completion" -> Completion (arg "context" |>
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
  | InvalidQuery msg -> { query_id = qid; q = BadProtocolMsg msg }
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

type repl_state = { repl_line: int; repl_column: int;
                    repl_stdin: stream_reader;
                    repl_names: CTable.table }

let run_query (st: repl_state) (q: lquery) : either<json, json> * either<repl_state, int> =
  match q with
  | Initialize (pid, rootUri) -> (Inl JsonNull, Inr 0)
  | Initialized -> (Inl JsonNull, Inr 0)
  | Shutdown -> (Inl JsonNull, Inr 0)
  | Exit -> (Inl JsonNull, Inr 0)
  | Cancel id -> (Inl JsonNull, Inr 0)
  | FolderChange evt -> (Inl JsonNull, Inr 0)
  | ChangeConfig -> (Inl JsonNull, Inr 0)
  | ChangeWatch -> (Inl JsonNull, Inr 0)
  | Symbol sym -> (Inl JsonNull, Inr 0)
  | ExecCommand cmd -> (Inl JsonNull, Inr 0)
  | DidOpen item -> (Inl JsonNull, Inr 0)
  | DidChange -> (Inl JsonNull, Inr 0)
  | WillSave txid -> (Inl JsonNull, Inr 0)
  | DidSave txid -> (Inl JsonNull, Inr 0)
  | DidClose txid -> (Inl JsonNull, Inr 0)
  | Completion ctx -> (Inl JsonNull, Inr 0)
  | Resolve -> (Inl JsonNull, Inr 0)
  | Hover -> (Inl JsonNull, Inr 0)
  | SignatureHelp -> (Inl JsonNull, Inr 0)
  | Declaration -> (Inl JsonNull, Inr 0)
  | Definition -> (Inl JsonNull, Inr 0)
  | Implementation -> (Inl JsonNull, Inr 0)
  | References -> (Inl JsonNull, Inr 0)
  | DocumentHighlight -> (Inl JsonNull, Inr 0)
  | DocumentSymbol -> (Inl JsonNull, Inr 0)
  | CodeAction -> (Inl JsonNull, Inr 0)
  | CodeLens -> (Inl JsonNull, Inr 0)
  | DocumentLink -> (Inl JsonNull, Inr 0)
  | DocumentColor -> (Inl JsonNull, Inr 0)
  | ColorPresentation -> (Inl JsonNull, Inr 0)
  | Formatting -> (Inl JsonNull, Inr 0)
  | RangeFormatting -> (Inl JsonNull, Inr 0)
  | TypeFormatting -> (Inl JsonNull, Inr 0)
  | Rename -> (Inl JsonNull, Inr 0)
  | PrepareRename -> (Inl JsonNull, Inr 0)
  | FoldingRange -> (Inl JsonNull, Inr 0)
  | BadProtocolMsg msg -> (Inl JsonNull, Inr 0)

let json_of_response qid response =
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

let initial_repl_state : repl_state =
  { repl_line = 1; repl_column = 0; repl_stdin = open_stdin ();
    repl_names = CompletionTable.empty }

let start_server () : unit = exit (go initial_repl_state)
