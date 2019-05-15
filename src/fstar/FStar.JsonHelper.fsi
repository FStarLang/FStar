(* Json helpers mainly for FStar.Interactive.Lsp; some sharing with *
 * FStar.Interactive.Ide                                            *)
#light "off"

module FStar.JsonHelper
open FStar
open FStar.Errors
open FStar.Util
open FStar.Exn
open FStar.Range

open FStar.TypeChecker.Env
module TcEnv = FStar.TypeChecker.Env
module CTable = FStar.Interactive.CompletionTable

val try_assoc : string -> list<(string * 'a)> -> option<'a> // nothrow
val assoc : string -> list <(string * 'a)> -> 'a // throw

// All exceptions are guaranteed to be caught in the LSP server implementation
exception MissingKey of string // Only in LSP
exception InvalidQuery of string // Only in IDE
exception UnexpectedJsonType of string * json
exception MalformedHeader
exception InputExhausted

val write_json : json -> unit // Only used in IDE
val write_jsonrpc : json -> unit // Only used in LSP
val js_fail : string -> json -> 'a

val js_int : json -> int
val js_str : json -> string
val js_list : (json -> 'a) -> json -> list<'a>
val js_assoc : json -> list<(string * json)>
val js_str_int : json -> int

val arg : string -> list<(string * json)> -> json
val uri_to_path : string -> string

type completion_context = { trigger_kind: int; trigger_char: option<string> }
val js_compl_context : json -> completion_context

type txdoc_item = { fname: string; langId: string; version: int; text: string }
val js_txdoc_item : json -> txdoc_item

type txdoc_pos = { uri: string; line: int; col: int }
val js_txdoc_id : list<(string * json)> -> string
val js_txdoc_pos : list<(string * json)> -> txdoc_pos

type workspace_folder = { wk_uri: string; wk_name: string }
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

type optresponse = option<either<json, json>> // Used to indicate (no|success|failure) response
type either_st_exit = either<repl_state, int> // repl_state is independent of exit_code

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

(* Helpers for constructing the response *)
val json_of_response : option<int> -> either<json, json> -> json
val js_resperr : error_code -> string -> json
val wrap_content_szerr : string -> lsp_query
val js_servcap : json
val js_range : Range.range -> json
