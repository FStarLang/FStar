#light "off"
module FStar.Interactive.CompletionTable

type path_elem
type path = list<path_elem>
val matched_prefix_of_path_elem : path_elem -> option<string>

type query = list<string>
type symbol =
| Module of bool
| Namespace of bool
| Lid of FStar.Ident.lid

type trie<'a>
type table = trie<symbol>

val empty : table
val insert : tbl:table -> host_query:query -> id:string -> c:symbol -> table
val register_alias : tbl:table -> key:string -> host_query:query -> included_query:query -> table
val register_open : tbl:table -> is_module:bool -> host_query:query -> included_query:query -> table
val register_include : tbl:table -> host_query:query -> included_query:query -> table
val register_module_path : tbl:table -> loaded:bool -> mod_query:query -> table

type completion_result =
  { completion_match_length: int;
    completion_candidate: string;
    completion_annotation: string }

val json_of_completion_result : completion_result -> FStar.Util.json
val autocomplete : tbl:table -> query:query -> filter:(path -> symbol -> option<(path * symbol)>) -> list<completion_result>
