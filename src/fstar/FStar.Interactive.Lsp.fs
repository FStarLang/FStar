#light "off"
module FStar.Interactive.Lsp

open FStar
open FStar.All
open FStar.Errors
open FStar.Util
open FStar.JsonHelper

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

let start_server () : unit = exit 0