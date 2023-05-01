(*
   Copyright 2019 and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(* Json helpers mainly for FStar.Interactive.Lsp; some sharing with *
 * FStar.Interactive.Ide                                            *)

module FStar.Interactive.JsonHelper
open FStar
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Compiler
open FStar.Compiler.Util
open FStar.Errors
open FStar.Compiler.Range
open FStar.Json
open FStar.TypeChecker.Env

module U = FStar.Compiler.Util
module PI = FStar.Parser.ParseIt
module TcEnv = FStar.TypeChecker.Env
module CTable = FStar.Interactive.CompletionTable

let try_assoc (key: string) (d: assoct) =
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
  U.print_raw (string_of_json js);
  U.print_raw "\n"

let write_jsonrpc (js: json) : unit =
  // TODO: utf-8 strings: byte buffers?
  let js_str = string_of_json js in
  let len = U.string_of_int (String.length js_str) in
  U.print_raw (U.format2 "Content-Length: %s\r\n\r\n%s" len js_str)

// Only used in IDE
let js_fail expected got =
  raise (UnexpectedJsonType (expected, got))

let js_int : json -> int = function
  | JsonInt i -> i
  | other -> js_fail "int" other
let js_bool : json -> bool = function
  | JsonBool b -> b
  | other -> js_fail "int" other
let js_str : json -> string = function
  | JsonStr s -> s
  | other -> js_fail "string" other
let js_list k = function
  | JsonList l -> List.map k l
  | other -> js_fail "list" other
let js_assoc : json -> assoct = function
  | JsonAssoc a -> a
  | other -> js_fail "dictionary" other
let js_str_int : json -> int = function
  | JsonInt i -> i
  | JsonStr s -> U.int_of_string s
  | other -> js_fail "string or int" other

// May throw
let arg k r = assoc k (assoc "params" r |> js_assoc)

// UNIX paths: file:///foo/bar corresponds to /foo/bar
//             01234567
//
// Windows paths: "file:///z%3A/foo corresponds to z:/foo
//                 0123456789                      012
let uri_to_path u = if U.substring u 9 3 = "%3A" then
                    U.format2 "%s:%s" (U.substring u 8 1) (U.substring_from u 12)
                    else U.substring_from u 7
let path_to_uri u = if U.char_at u 1 = ':' then
                    let rest = U.replace_char (U.substring_from u 2) '\\' '/' in
                    U.format2 "file:///%s%3A%s" (U.substring u 0 1) rest
                    else U.format1 "file://%s" u

let js_compl_context : json -> completion_context = function
  | JsonAssoc a ->
  { trigger_kind = assoc "triggerKind" a |> js_int;
    trigger_char = try_assoc "triggerChar" a |> U.map_option js_str; }
  | other -> js_fail "dictionary" other

// May throw
let js_txdoc_item : json -> txdoc_item = function
  | JsonAssoc a ->
  let arg k = assoc k a in
  { fname = uri_to_path (arg "uri" |> js_str);
    langId = arg "languageId" |> js_str;
    version = arg "version" |> js_int;
    text = arg "text" |> js_str }
  | other -> js_fail "dictionary" other

// May throw, argument is of the form { "textDocument" : {"uri" : ... } }
let js_txdoc_id (r: list (string * json)) : string =
  uri_to_path (assoc "uri" (arg "textDocument" r |> js_assoc) |> js_str)

// May throw; argument is of the form { "textDocument" : ...,
//                                      "position" : { "line" : ..., "character" : ... } }
let js_txdoc_pos (r: list (string * json)) : txdoc_pos =
  let pos = arg "position" r |> js_assoc in
  { path = js_txdoc_id r;
    line = assoc "line" pos |> js_int;
    col = assoc "character" pos |> js_int }

// May throw
let js_wsch_event : json -> wsch_event = function
  | JsonAssoc a ->
  let added' = assoc "added" a |> js_assoc in
  let removed' = assoc "removed" a |> js_assoc in
  { added = { wk_uri = assoc "uri" added' |> js_str;
              wk_name = assoc "name" added' |> js_str };
    removed = { wk_uri = assoc "uri" removed' |> js_str;
                wk_name = assoc "name" removed' |> js_str } }
  | other -> js_fail "dictionary" other

// May throw
let js_contentch : json -> string = function
  // List will have one item, and List.hd is guaranteed to work,
  // since we've specified that full text should be sent on change
  // in the capabilities
  | JsonList l -> List.hd (List.map (fun (JsonAssoc a) -> assoc "text" a |> js_str) l)
  | other -> js_fail "dictionary" other

type rng = { rng_start: int * int; rng_end: int * int }

// May throw
let js_rng : json -> rng = function
  | JsonAssoc a ->
  let st = assoc "start" a in
  let fin = assoc "end" a in
  let l = assoc "line" in
  let c = assoc "character" in
  { rng_start = l (st |> js_assoc) |> js_int, c (st |> js_assoc) |> js_int;
    rng_end = l (fin |> js_assoc) |> js_int, c (st |> js_assoc) |> js_int }
  | other -> js_fail "dictionary" other

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
let wrap_jsfail (qid : option int) expected got : lsp_query =
  { query_id = qid;
    q = BadProtocolMsg (U.format2 "JSON decoding failed: expected %s, got %s"
                        expected (json_debug got)) }

(* Helpers for constructing the response *)

// Trivial helpers
let resultResponse (r: json) : option assoct = Some [("result", r)]
let errorResponse (r: json) : option assoct = Some [("error", r)]

// When a response is expected, but we have nothing to say (used for unimplemented bits as well)
let nullResponse : option assoct = resultResponse JsonNull

let json_of_response (qid: option int) (response: assoct) : json =
  match qid with
  | Some i -> JsonAssoc ([("jsonrpc", JsonStr "2.0"); ("id", JsonInt i)] @ response)
  // In the case of a notification response, there is no query_id associated
  | None -> JsonAssoc ([("jsonrpc", JsonStr "2.0")] @ response)

let js_resperr (err: error_code) (msg: string) : json =
  JsonAssoc [("code", JsonInt (errorcode_to_int err)); ("message", JsonStr msg)]

let wrap_content_szerr (m: string): lsp_query = { query_id = None; q = BadProtocolMsg m }

let js_servcap : json =
  JsonAssoc [("capabilities",
              // Open, close, change, and save events will happen with full text sent;
              // change is required for auto-completions
              JsonAssoc [("textDocumentSync", JsonAssoc [
                ("openClose", JsonBool true);
                ("change", JsonInt 1);
                ("willSave", JsonBool false);
                ("willSaveWaitUntil", JsonBool false);
                ("save", JsonAssoc [("includeText", JsonBool true)])]);
              ("hoverProvider", JsonBool true);
              ("completionProvider", JsonAssoc []);
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

let js_range (r: Range.range) : json =
  JsonAssoc [("start", js_pos (start_of_range r)); ("end", js_pos (end_of_range r))]

// Used to report diagnostic, for example, when loading dependencies fails
let js_dummyrange : json =
  JsonAssoc [("start", JsonAssoc [("line", JsonInt 0); ("character", JsonInt 0);
             ("end", JsonAssoc [("line", JsonInt 0); ("character", JsonInt 0)])])]

let js_loclink (r: Range.range) : json =
  let s = js_range r in
  JsonList [JsonAssoc [("targetUri", JsonStr (path_to_uri (file_of_range r)));
                       ("targetRange", s); ("targetSelectionRange", s)]]

// Lines are 0-indexed in LSP, but 1-indexed in the F* Typechecker;
let pos_munge (pos: txdoc_pos) = (pos.path, pos.line + 1, pos.col)

let js_diag (fname: string) (msg: string) (r: option Range.range) : assoct =
  let r' = match r with
           | Some r -> js_range r
           | None -> js_dummyrange in
  // Unfortunately, the F* typechecker aborts on the very first diagnostic
  let ds = ("diagnostics", JsonList [JsonAssoc [("range", r'); ("message", JsonStr msg)]]) in
  [("method", JsonStr "textDocument/publishDiagnostics");
   ("params", JsonAssoc [("uri", JsonStr (path_to_uri fname)); ds])]

let js_diag_clear (fname: string) : assoct =
  [("method", JsonStr "textDocument/publishDiagnostics");
   ("params", JsonAssoc [("uri", JsonStr (path_to_uri fname)); ("diagnostics", JsonList [])])]

