#light "off"

module FStar.JsonHelper
open FStar
open FStar.Util
open FStar.Errors
open FStar.Exn

val try_assoc : string -> list<(string * 'a)> -> option<'a>
val assoc : string -> list <(string * 'b)> -> 'b

// All exceptions are guaranteed to be caught in the LSP server implementation
exception MissingKey of string // Only in LSP
exception InvalidQuery of string // Only in IDE
exception UnexpectedJsonType of string * json

val write_json : json -> unit
val js_fail : string -> json -> 'a

val js_int : json -> int
val js_str : json -> string
val js_list : (json -> 'a) -> json -> list<'a>
val js_assoc : json -> list<(string * json)>
val js_str_int : json -> int

type completion_context = { trigger_kind: int; trigger_char: option<string> }
val js_compl_context : json -> completion_context

type txdoc_item = { uri: string; langId: string; version: int; text: string }
val js_txdoc_item : json -> txdoc_item

type workspace_folder = { uri: string; name: string }
type wsch_event = { added: workspace_folder; removed: workspace_folder }
val js_wsch_event : json -> wsch_event

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
| DidSave of string
| DidClose of string
| Completion of completion_context
| Resolve
| Hover
| SignatureHelp
| Declaration
| Definition
| Implementation
| References
| DocumentHighlight
| DocumentSymbol
| CodeAction
| CodeLens
| DocumentLink
| DocumentColor
| ColorPresentation
| Formatting
| RangeFormatting
| TypeFormatting
| Rename
| PrepareRename
| FoldingRange
| BadProtocolMsg of string

type lsp_query = { query_id: option<int>; q: lquery }

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

val errorcode_to_int : error_code -> int
val json_debug : json -> string
val wrap_jsfail : option<int> -> string -> json -> lsp_query
val js_resperr : error_code -> string -> json
