#light "off"
module FStar.Syntax.Embeddings

open FStar.All
open FStar.Syntax.Syntax
module Range = FStar.Range

val embed_unit   : unit -> term
val unembed_unit : term -> option<unit>

val embed_bool   : bool -> term
val unembed_bool : term -> option<bool>

val embed_int   : int -> term
val unembed_int : term -> option<int>

val embed_string   : string -> term
val unembed_string : term -> option<string>

val embed_pair   : ('a -> term) -> term -> ('b -> term) -> term -> ('a*'b) -> term
val unembed_pair : (term -> option<'a>) -> (term -> option<'b>) -> term -> option<('a*'b)>

val embed_option   : ('a -> term) -> term -> option<'a> -> term
val unembed_option : (term -> option<'a>) -> term -> option<option<'a>>

val embed_list   : ('a -> term) -> term -> list<'a> -> term
val unembed_list : (term -> option<'a>) -> term -> option<list<'a>>

val embed_string_list   : list<string> -> term
val unembed_string_list : term -> option<list<string>>

type norm_step =
    | Simpl
    | WHNF
    | Primops
    | Delta
    | Zeta
    | Iota
    | UnfoldOnly of list<string>

val steps_Simpl : term
val steps_WHNF : term
val steps_Primops : term
val steps_Delta : term
val steps_Zeta : term
val steps_Iota : term
val steps_UnfoldOnly : term

val embed_norm_step : norm_step -> term
val unembed_norm_step : term -> option<norm_step>

val embed_range : Range.range -> term
val unembed_range : term -> option<Range.range>
