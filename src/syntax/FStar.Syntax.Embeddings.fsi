#light "off"
module FStar.Syntax.Embeddings

open FStar.All
open FStar.Syntax.Syntax
open FStar.Char

module Range = FStar.Range
module Z = FStar.BigInt

(* TODO: Find a better home for these *)
type norm_step =
    | Simpl
    | Weak
    | HNF
    | Primops
    | Delta
    | Zeta
    | Iota
    | Reify
    | UnfoldOnly of list<string>
    | UnfoldFully of list<string>
    | UnfoldAttr of attribute

val steps_Simpl         : term
val steps_Weak          : term
val steps_HNF           : term
val steps_Primops       : term
val steps_Delta         : term
val steps_Zeta          : term
val steps_Iota          : term
val steps_Reify         : term
val steps_UnfoldOnly    : term
val steps_UnfoldFully   : term
val steps_UnfoldAttr    : term

(*
 * Unmbedding functions return an option because they might fail
 * to interpret the given term as valid data. The `try_` version will
 * simply return None in that case, but the unsafe one will also raise a
 * warning, and should be used only where we really expect to always be
 * able to unembed.
 *)

type embedding<'a>

type raw_embedder<'a>    = Range.range -> 'a -> term
type raw_unembedder'<'a> = bool -> term -> option<'a> // bool = whether we should warn on a failure
type raw_unembedder<'a>  = term -> option<'a>

val mk_emb : raw_embedder<'a> -> raw_unembedder'<'a> -> typ -> embedding<'a>

// embed: turning a value into a term (compiler internals -> userland)
// unembed: interpreting a term as a value, which can fail (userland -> compiler internals)
val embed       : embedding<'a> -> Range.range -> 'a -> term
val unembed'    : bool -> embedding<'a> -> term -> option<'a>
val unembed     : embedding<'a> -> term -> option<'a>
val try_unembed : embedding<'a> -> term -> option<'a>
val type_of     : embedding<'a> -> typ
val set_type    : typ -> embedding<'a> -> embedding<'a>

(* Embeddings, both ways and containing type information *)
val e_any         : embedding<term> // an identity
val e_unit        : embedding<unit>
val e_bool        : embedding<bool>
val e_char        : embedding<char>
val e_int         : embedding<Z.t>
val e_string      : embedding<string>
val e_norm_step   : embedding<norm_step>
val e_range       : embedding<Range.range>

val e_option      : embedding<'a> -> embedding<option<'a>>
val e_list        : embedding<'a> -> embedding<list<'a>>
val e_tuple2      : embedding<'a> -> embedding<'b> -> embedding<('a * 'b)>
val e_string_list : embedding<list<string>>

val mk_any_emb : typ -> embedding<term>

(* These are different, really, we're not embedding functions *)
val embed_arrow_1     : embedding<'a> -> embedding<'b> ->
                        ('a -> 'b) -> args -> option<term>

val embed_arrow_2     : embedding<'a> -> embedding<'b> -> embedding<'c> ->
                        ('a -> 'b -> 'c) -> args -> option<term>

val embed_arrow_3     : embedding<'a> -> embedding<'b> -> embedding<'c> -> embedding<'d> ->
                        ('a -> 'b -> 'c -> 'd) -> args -> option<term>
