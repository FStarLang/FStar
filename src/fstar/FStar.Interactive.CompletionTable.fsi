#light "off"
module FStar.Interactive.CompletionTable

type query = string list
type symbol = | Lid of FStar.Ident.lid

type trie<'a>
type table = trie<symbol>

val empty : table
val insert : tbl:table -> c:symbol -> table
val register_alias : tbl:table -> key:string -> query:query -> table
val register_include : tbl:table -> included_query:query -> target_query:query -> table

type completion_result =
  { completion_kind: string;
    completion_match_length: int;
    completion_candidate: string;
    completion_annotation: string }

val autocomplete : tbl:table -> query:query -> namespaces:list<query> -> completion_result list
