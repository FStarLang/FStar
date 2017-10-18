#light "off"
module FStar.Syntax.Embeddings

open FStar.All
open FStar.Syntax.Syntax
open FStar.Char

module Range = FStar.Range

(*
 * Unmbedding functions return an option because they might fail to
 * interpret the given term as valid data. The `_safe` version will simply
 * return None in that case, but the unsafe one will also raise a
 * warning, and should be used only where we really expect to always be able
 * to unembed.
 *
 * Polymorphic embedders need the type of whatever they're embedding to construct
 * a propert well-typed term.
 *)

type embedder<'a>   = Range.range -> 'a -> term
type unembedder<'a> = term -> option<'a>

val embed_unit        : embedder<unit>
val unembed_unit      : unembedder<unit>
val unembed_unit_safe : unembedder<unit>

val embed_bool        : embedder<bool>
val unembed_bool      : unembedder<bool>
val unembed_bool_safe : unembedder<bool>

val embed_char        : embedder<char>
val unembed_char      : unembedder<char>
val unembed_char_safe : unembedder<char>

val embed_int        : embedder<int>
val unembed_int      : unembedder<int>
val unembed_int_safe : unembedder<int>

val embed_string        : embedder<string>
val unembed_string      : unembedder<string>
val unembed_string_safe : unembedder<string>

val embed_pair        : embedder<'a> -> typ -> embedder<'b> -> typ -> embedder<('a * 'b)>
val unembed_pair      : unembedder<'a> -> unembedder<'b> -> unembedder<('a * 'b)>
val unembed_pair_safe : unembedder<'a> -> unembedder<'b> -> unembedder<('a * 'b)>

val embed_option        : embedder<'a> -> typ -> embedder<option<'a>>
val unembed_option      : unembedder<'a> -> unembedder<option<'a>>
val unembed_option_safe : unembedder<'a> -> unembedder<option<'a>>

val embed_list        : embedder<'a> -> typ -> embedder<list<'a>>
val unembed_list      : unembedder<'a> -> unembedder<list<'a>>
val unembed_list_safe : unembedder<'a> -> unembedder<list<'a>>

val embed_string_list        : embedder<list<string>>
val unembed_string_list      : unembedder<list<string>>
val unembed_string_list_safe : unembedder<list<string>>

type norm_step =
    | Simpl
    | Weak
    | HNF
    | Primops
    | Delta
    | Zeta
    | Iota
    | UnfoldOnly of list<string>

val steps_Simpl : term
val steps_Weak : term
val steps_HNF  : term
val steps_Primops : term
val steps_Delta : term
val steps_Zeta : term
val steps_Iota : term
val steps_UnfoldOnly : term

val embed_norm_step        : embedder<norm_step>
val unembed_norm_step      : unembedder<norm_step>
val unembed_norm_step_safe : unembedder<norm_step>

val embed_range        : embedder<Range.range>
val unembed_range      : unembedder<Range.range>
val unembed_range_safe : unembedder<Range.range>
