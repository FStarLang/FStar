(*
   Copyright 2019 Microsoft Research

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

(* Json helpers mainly for FStarC.Interactive.Lsp; some sharing with *
 * FStarC.Interactive.Ide                                            *)

module FStarC.Interactive.JsonHelper
open FStarC
open FStarC.Errors
open FStarC.Json

// Type of an associative array
type assoct = list (string & json)

val try_assoc : string -> assoct -> option json // nothrow
val assoc : string -> assoct -> json // throw

// All exceptions are guaranteed to be caught in the LSP server implementation
exception MissingKey of string // Only in LSP
exception InvalidQuery of string // Only in IDE
exception UnexpectedJsonType of string & json
exception MalformedHeader
exception InputExhausted

val write_json : json -> unit // Only used in IDE
val write_jsonrpc : json -> unit // Only used in LSP
val js_fail : string -> json -> 'a

val js_int : json -> int
val js_bool : json -> bool
val js_str : json -> string
val js_list : (json -> 'a) -> json -> list 'a
val js_assoc : json -> assoct
val js_str_int : json -> int

val arg : string -> assoct -> json
val uri_to_path : string -> string

type completion_context = { trigger_kind: int; trigger_char: option string }
val js_compl_context : json -> completion_context

type txdoc_item = { fname: string; langId: string; version: int; text: string }
val js_txdoc_item : json -> txdoc_item

type txdoc_pos = { path: string; line: int; col: int }
val js_txdoc_id : assoct -> string
val js_txdoc_pos : assoct -> txdoc_pos

type workspace_folder = { wk_uri: string; wk_name: string }
type wsch_event = { added: workspace_folder; removed: workspace_folder }
val js_wsch_event : json -> wsch_event
val js_contentch : json -> string

type lquery =
| Initialize of int & string
| Initialized
| Shutdown
| Exit
| Cancel of int
| FolderChange of wsch_event
| ChangeConfig
| ChangeWatch
| Symbol of string
| ExecCommand of string
| DidOpen of txdoc_item
| DidChange of string & string
| WillSave of string
| WillSaveWait of string
| DidSave of string & string
| DidClose of string
| Completion of txdoc_pos & completion_context
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

type lsp_query = { query_id: option int; q: lquery }


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

// A lookup table for pretty-printing error codes
val errorcode_to_int : error_code -> int

// Another lookup table for pretty-printing JSON objects
val json_debug : json -> string

// Wrap an error-code along with a description of the error in a BadProtocolMsg
val wrap_jsfail : option int -> string -> json -> lsp_query

(* Helpers for constructing the response *)

// Used by run_query heavily
val resultResponse : json -> option assoct
val errorResponse : json -> option assoct
val nullResponse : option assoct

// Build JSON of a given response
val json_of_response : option int -> assoct -> json

// Given an error_code and a string describing the error, build a JSON error
val js_resperr : error_code -> string -> json

// Build an error corresponding to BadProtocolMsg
val wrap_content_szerr : string -> lsp_query

// Report on server capabilities
val js_servcap : json

// Create a JSON location link from a Range.t
val js_loclink : Range.t -> json

// Convert txdoc_pos into (filename, line, col)
val pos_munge : txdoc_pos -> string & int & int

// Build a JSON diagnostic
val js_diag : string -> string -> option Range.t -> assoct

// Build an empty JSON diagnostic; used for clearing diagnostic
val js_diag_clear : string -> assoct

