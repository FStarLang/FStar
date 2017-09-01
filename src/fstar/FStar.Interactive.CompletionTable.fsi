#light "off"
module FStar.Interactive.CompletionTable

type path_elem
type path = list<path_elem>
val matched_prefix_of_path_elem : path_elem -> option<string>

type query = list<string>

type ns_info = { ns_name: string;
                 ns_loaded: bool }
type mod_info = { mod_name: string;
                  mod_path: string;
                  mod_loaded: bool }

val mod_name : mod_info -> string // F# doesn't like md.CompletionTable.mod_name

type mod_symbol =
| Module of mod_info
| Namespace of ns_info

type lid_symbol = FStar.Ident.lid

type trie<'a>
type table

val empty : table
val insert : tbl:table -> host_query:query -> id:string -> c:lid_symbol -> table
val register_alias : tbl:table -> key:string -> host_query:query -> included_query:query -> table
val register_open : tbl:table -> is_module:bool -> host_query:query -> included_query:query -> table
val register_include : tbl:table -> host_query:query -> included_query:query -> table
val register_module_path : tbl:table -> loaded:bool -> mod_path:string -> mod_query:query -> table

val alist_of_ns_info : ns_info -> list<(string * FStar.Util.json)>
val alist_of_mod_info : mod_info -> list<(string * FStar.Util.json)>

type completion_result =
  { completion_match_length: int;
    completion_candidate: string;
    completion_annotation: string }
val json_of_completion_result : completion_result -> FStar.Util.json

val find_module_or_ns :
  tbl:table -> query:query -> option<mod_symbol>
val autocomplete_lid :
  tbl:table -> query:query -> list<completion_result>
val autocomplete_mod_or_ns :
  tbl:table -> query:query -> filter:((path * mod_symbol) -> option<(path * mod_symbol)>) -> list<completion_result>
