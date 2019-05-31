(* FStar.Interactive.Lsp needs to construct responses to various *
 * queries; this file collects helpers for them                  *)
#light "off"

module FStar.QueryHelper
open FStar.Range
open FStar.Util
open FStar.JsonHelper
open FStar.TypeChecker.Env

module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env

type position = string * int * int
type sl_reponse = { slr_name: string;
                    slr_def_range: option<Range.range>;
                    slr_typ: option<string>;
                    slr_doc: option<string>;
                    slr_def: option<string> }

// Parametrized, because we don't want to open modules unnecessarily
val term_to_string : TcEnv.env -> Syntax.Syntax.term -> string

// Shared by IDE and LSP
val symlookup : TcEnv.env -> string -> option<position> -> list<string> -> option<sl_reponse>

// Shared by IDE and LSP
val ck_completion : repl_state -> string -> json

// Used exclusively by LSP
val deflookup : TcEnv.env -> txdoc_pos -> either<json, json>
val hoverlookup : TcEnv.env -> txdoc_pos -> either<json, json>
val complookup : TcEnv.env -> txdoc_pos -> either<json, json>
