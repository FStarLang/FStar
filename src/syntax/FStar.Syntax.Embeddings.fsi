#light "off"
module FStar.Syntax.Embeddings

open FStar.All
open FStar.Syntax.Syntax
module Range = FStar.Range

(* Unmbedding functions return an option because they might fail to
 * interpret the given term as valid data. The `_safe` version will simply
 * return None in that case, but the unsafe one will also raise a
 * warning, and should be used only where we really expect to always be able
 * to unembed.
 *)

val embed_unit        : unit -> term
val unembed_unit      : term -> option<unit>
val unembed_unit_safe : term -> option<unit>

val embed_bool        : bool -> term
val unembed_bool      : term -> option<bool>
val unembed_bool_safe : term -> option<bool>

val embed_int        : int -> term
val unembed_int      : term -> option<int>
val unembed_int_safe : term -> option<int>

val embed_string        : string -> term
val unembed_string      : term -> option<string>
val unembed_string_safe : term -> option<string>

val embed_pair        : ('a -> term) -> term -> ('b -> term) -> term -> ('a*'b) -> term
val unembed_pair      : (term -> option<'a>) -> (term -> option<'b>) -> term -> option<('a*'b)>
val unembed_pair_safe : (term -> option<'a>) -> (term -> option<'b>) -> term -> option<('a*'b)>

val embed_option        : ('a -> term) -> term -> option<'a> -> term
val unembed_option      : (term -> option<'a>) -> term -> option<option<'a>>
val unembed_option_safe : (term -> option<'a>) -> term -> option<option<'a>>

val embed_list        : ('a -> term) -> term -> list<'a> -> term
val unembed_list      : (term -> option<'a>) -> term -> option<list<'a>>
val unembed_list_safe : (term -> option<'a>) -> term -> option<list<'a>>

val embed_string_list        : list<string> -> term
val unembed_string_list      : term -> option<list<string>>
val unembed_string_list_safe : term -> option<list<string>>

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

val embed_norm_step        : norm_step -> term
val unembed_norm_step      : term -> option<norm_step>
val unembed_norm_step_safe : term -> option<norm_step>

val embed_range        : Range.range -> term
val unembed_range      : term -> option<Range.range>
val unembed_range_safe : term -> option<Range.range>
