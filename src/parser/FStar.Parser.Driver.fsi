#light "off"
module FStar.Parser.Driver

module Range      = FStar.Range
module AST        = FStar.Parser.AST
module ParseIt    = FStar.Parser.ParseIt

val is_cache_file : string -> bool

type fragment =
    | Empty
    | Modul of AST.modul // an entire module or interface -- unspecified
    | Decls of list<AST.decl> // a partial set of declarations

val parse_fragment : ParseIt.input_frag -> fragment

(* Returns a non-desugared AST (as in [parser/ast.fs]) or aborts. *)
val parse_file : string -> AST.file * list<(string * Range.range)>
