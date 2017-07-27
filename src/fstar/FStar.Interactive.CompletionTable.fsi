#light "off"
module FStar.Interactive.CompletionTable

type query = list<string>
type symbol = | Lid of FStar.Ident.lid

type trie<'a>
type table = trie<symbol>

val empty : table
val insert : tbl:table -> host_query:query -> id:string -> c:symbol -> table
val register_alias : tbl:table -> key:string -> host_query:query -> included_query:query -> table
val register_open : tbl:table -> is_module:bool -> host_query:query -> included_query:query -> table
val register_include : tbl:table -> host_query:query -> included_query:query -> table

type completion_result =
  { completion_kind: string;
    completion_match_length: int;
    completion_candidate: string;
    completion_annotation: string }

val json_of_completion_result: completion_result -> FStar.Util.json
val autocomplete : tbl:table -> query:query -> list<completion_result>
