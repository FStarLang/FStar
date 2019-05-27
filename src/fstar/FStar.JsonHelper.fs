(* Json helpers mainly for FStar.Interactive.Lsp; some sharing with *
 * FStar.Interactive.Ide                                            *)
#light "off"

module FStar.JsonHelper
open FStar
open FStar.Util
open FStar.Errors
open FStar.Exn
open FStar.Range
open FStar.TypeChecker.Env

module U = FStar.Util
module TcEnv = FStar.TypeChecker.Env
module CTable = FStar.Interactive.CompletionTable

let try_assoc (key: string) (d: list<(string * json)>) =
  U.map_option snd (U.try_find (fun (k, _) -> k = key) d)

// All exceptions are guaranteed to be caught in the LSP server implementation
exception MissingKey of string // Only in LSP
exception InvalidQuery of string // Only in IDE
exception UnexpectedJsonType of string * json
exception MalformedHeader
exception InputExhausted

// The definition in IDE is nested; this differs in not providing loc
let assoc key a =
  match try_assoc key a with
  | Some v -> v
  | None -> raise (MissingKey (U.format1 "Missing key [%s]" key))

let write_json (js: json) =
  U.print_raw (U.string_of_json js);
  U.print_raw "\n"

let write_jsonrpc (js: json) : unit =
  // TODO: utf-8 strings: byte buffers?
  let js_str = U.string_of_json js in
  let len = U.string_of_int (String.length js_str) in
  U.print_raw (U.format2 "Content-Length: %s\r\n\r\n%s" len js_str)

// Only used in IDE
let js_fail expected got =
  raise (UnexpectedJsonType (expected, got))

let js_int : json -> int = function
  | JsonInt i -> i
  | other -> js_fail "int" other
let js_str : json -> string = function
  | JsonStr s -> s
  | other -> js_fail "string" other
let js_list k = function
  | JsonList l -> List.map k l
  | other -> js_fail "list" other
let js_assoc : json -> list<(string * json)> = function
  | JsonAssoc a -> a
  | other -> js_fail "dictionary" other
let js_str_int : json -> int = function
  | JsonInt i -> i
  | JsonStr s -> U.int_of_string s
  | other -> js_fail "string or int" other

// May throw
let arg k r = assoc k (assoc "params" r |> js_assoc)

let uri_to_path u = if U.starts_with u "file://" then substring_from u 7 else u
let path_to_uri u = if U.starts_with u "file://" then u else U.format1 "file://%s" u

type completion_context = { trigger_kind: int; trigger_char: option<string> }

let js_compl_context : json -> completion_context = function
  | JsonAssoc a ->
    { trigger_kind = assoc "triggerKind" a |> js_int;
      trigger_char = try_assoc "triggerChar" a |> U.map_option js_str; }
  | other -> js_fail "dictionary" other

type txdoc_item = { fname: string; langId: string; version: int; text: string }

// May throw
let js_txdoc_item : json -> txdoc_item = function
  | JsonAssoc a ->
    let arg k = assoc k a in
    { fname = arg "uri" |> js_str;
      langId = arg "languageId" |> js_str;
      version = arg "version" |> js_int;
      text = arg "text" |> js_str }
  | other -> js_fail "dictionary" other

type txdoc_pos = { uri: string; line: int; col: int }

// May throw, argument is of the form { "textDocument" : {"uri" : ... } }
let js_txdoc_id (r: list<(string * json)>) : string =
  assoc "uri" (arg "textDocument" r |> js_assoc) |> js_str

// May throw; argument is of the form { "textDocument" : ...,
//                                      "position" : { "line" : ..., "character" : ... } }
let js_txdoc_pos (r: list<(string * json)>) : txdoc_pos =
  let pos = arg "position" r |> js_assoc in
  { uri = js_txdoc_id r;
    line = assoc "line" pos |> js_int;
    col = assoc "character" pos |> js_int }

type workspace_folder = { wk_uri: string; wk_name: string }
type wsch_event = { added: workspace_folder; removed: workspace_folder }

let js_wsch_event : json -> wsch_event = function
  | JsonAssoc a ->
      let added' = assoc "added" a |> js_assoc in
      let removed' = assoc "removed" a |> js_assoc in
      { added = { wk_uri = assoc "uri" added' |> js_str;
                  wk_name = assoc "name" added' |> js_str };
        removed = { wk_uri = assoc "uri" removed' |> js_str;
                    wk_name = assoc "name" removed' |> js_str } }
  | other -> js_fail "dictionary" other

(* Types of main query *)
type lquery =
| Initialize of int * string
| Initialized
| Shutdown
| Exit
| Cancel of string
| FolderChange of wsch_event
| ChangeConfig
| ChangeWatch
| Symbol of string
| ExecCommand of string
| DidOpen of txdoc_item
| DidChange
| WillSave of string
| WillSaveWait of string
| DidSave of string
| DidClose of string
| Completion of completion_context
| Resolve
| Hover of txdoc_pos
| SignatureHelp of txdoc_pos
| Declaration of txdoc_pos
| Definition of txdoc_pos
| TypeDefinition of txdoc_pos
| Implementation of txdoc_pos
| References
| DocumentHighlight of txdoc_pos
| DocumentSymbol
| CodeAction
| CodeLens
| CodeLensResolve
| DocumentLink
| DocumentLinkResolve
| DocumentColor
| ColorPresentation
| Formatting
| RangeFormatting
| TypeFormatting
| Rename
| PrepareRename of txdoc_pos
| FoldingRange
| BadProtocolMsg of string

type lsp_query = { query_id: option<int>; q: lquery }

(* Types concerning repl *)
type repl_depth_t = TcEnv.tcenv_depth_t * int
type optmod_t = option<Syntax.Syntax.modul>

type timed_fname =
  { tf_fname: string;
    tf_modtime: time }

(** Every snapshot pushed in the repl stack is annotated with one of these.  The
``LD``-prefixed (“Load Dependency”) onces are useful when loading or updating
dependencies, as they carry enough information to determine whether a dependency
is stale. **)
type repl_task =
  | LDInterleaved of timed_fname * timed_fname (* (interface * implementation) *)
  | LDSingle of timed_fname (* interface or implementation *)
  | LDInterfaceOfCurrentFile of timed_fname (* interface *)
  | PushFragment of Parser.ParseIt.input_frag (* code fragment *)
  | Noop (* Used by compute *)

type repl_state = { repl_line: int; repl_column: int; repl_fname: string;
                    repl_deps_stack: repl_stack_t;
                    repl_curmod: optmod_t;
                    repl_env: TcEnv.env;
                    repl_stdin: stream_reader;
                    repl_names: CTable.table }
and repl_stack_t = list<repl_stack_entry_t>
and repl_stack_entry_t = repl_depth_t * (repl_task * repl_state)

type grepl_state = smap<repl_state>

type optresponse = option<either<json, json>>
type either_st_exit = either<repl_state, int>

type error_code =
| ParseError
| InvalidRequest
| MethodNotFound
| InvalidParams
| InternalError
| ServerErrorStart
| ServerErrorEnd
| ServerNotInitialized
| UnknownErrorCode
| RequestCancelled
| ContentModified

let errorcode_to_int : error_code -> int = function
| ParseError -> -32700
| InvalidRequest -> -32600
| MethodNotFound -> -32601
| InvalidParams -> -32602
| InternalError -> -32603
| ServerErrorStart -> -32099
| ServerErrorEnd -> -32000
| ServerNotInitialized -> -32002
| UnknownErrorCode -> -32001
| RequestCancelled -> -32800
| ContentModified -> -32801

let json_debug = function
  | JsonNull -> "null"
  | JsonBool b -> U.format1 "bool (%s)" (if b then "true" else "false")
  | JsonInt i -> U.format1 "int (%s)" (U.string_of_int i)
  | JsonStr s -> U.format1 "string (%s)" s
  | JsonList _ -> "list (...)"
  | JsonAssoc _ -> "dictionary (...)"

// The IDE uses a slightly different variant (wrap_js_failure)
// because types differ (query' versus lsp_query)
let wrap_jsfail (qid : option<int>) expected got : lsp_query =
  { query_id = qid;
    q = BadProtocolMsg (U.format2 "JSON decoding failed: expected %s, got %s"
                        expected (json_debug got)) }

(* Helpers for constructing the response *)

let json_of_response (qid: option<int>) (response: either<json, json>) =
  let qid = match qid with
  | Some i -> JsonInt i
  | None -> JsonNull in
  match response with
  | Inl result -> JsonAssoc [("jsonrpc", JsonStr "2.0"); ("id", qid); ("result", result)]
  | Inr err -> JsonAssoc [("jsonrpc", JsonStr "2.0"); ("id", qid); ("error", err)]

let js_resperr (err: error_code) (msg: string) : json =
  JsonAssoc [("code", JsonInt (errorcode_to_int err)); ("message", JsonStr msg)]

let wrap_content_szerr (m: string): lsp_query = { query_id = None; q = BadProtocolMsg m }

let js_servcap : json =
  JsonAssoc [("capabilities",
              JsonAssoc [("textDocumentSync", JsonAssoc [("openClose", JsonBool true);
                                                         ("change", JsonInt 1);
                                                         ("willSave", JsonBool true);
                                                         ("willSaveWaitUntil", JsonBool false)]);
              ("hoverProvider", JsonBool true);
              ("completionProvider", JsonAssoc [("resolveProvider", JsonBool false)]);
              ("signatureHelpProvider", JsonAssoc []);
              ("definitionProvider", JsonBool true);
              ("typeDefinitionProvider", JsonBool false);
              ("implementationProvider", JsonBool false);
              ("referencesProvider", JsonBool false);
              ("documentSymbolProvider", JsonBool false);
              ("workspaceSymbolProvider", JsonBool false);
              ("codeActionProvider", JsonBool false)])]

// LSP uses zero-indexed line numbers while the F* typechecker uses 1-indexed ones;
// column numbers are zero-indexed in both
let js_pos (p: pos) : json = JsonAssoc [("line", JsonInt (line_of_pos p - 1));
                                        ("character", JsonInt (col_of_pos p))]

let js_loclink r =
  let s = JsonAssoc [("start", js_pos (start_of_range r)); ("end", js_pos (end_of_range r))] in
  JsonList [JsonAssoc [("targetUri", JsonStr (path_to_uri (file_of_range r)));
                       ("targetRange", s); ("targetSelectionRange", s)]]