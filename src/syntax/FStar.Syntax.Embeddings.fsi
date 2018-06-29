#light "off"
module FStar.Syntax.Embeddings

open FStar
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

type norm_cb = FStar.Util.either<Ident.lident, term> -> term // a callback to the normalizer
val id_norm_cb : norm_cb
exception Embedding_failure
exception Unembedding_failure
type shadow_term = option<FStar.Common.thunk<term>>

type embed_t = FStar.Range.range -> shadow_term -> norm_cb -> term
type unembed_t<'a> = bool -> norm_cb -> option<'a> // bool = whether we should warn on a failure

type raw_embedder<'a>   = 'a -> embed_t
type raw_unembedder<'a> = term -> unembed_t<'a>

type embedding<'a>
val emb_typ_of: embedding<'a> -> emb_typ
val term_as_fv: term -> fv //partial!
val mk_emb : raw_embedder<'a> -> raw_unembedder<'a> -> fv -> embedding<'a>
val mk_emb_full: raw_embedder<'a>
              -> raw_unembedder<'a>
              -> typ
              -> ('a -> string)
              -> emb_typ
              -> embedding<'a>


// embed: turning a value into a term (compiler internals -> userland)
// unembed: interpreting a term as a value, which can fail (userland -> compiler internals)
val embed        : embedding<'a> -> 'a -> embed_t
val unembed      : embedding<'a> -> term -> unembed_t<'a>
val warn_unembed : embedding<'a> -> term -> norm_cb -> option<'a>
val try_unembed  : embedding<'a> -> term -> norm_cb -> option<'a>
val type_of      : embedding<'a> -> typ

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
val e_arrow       : embedding<'a> -> embedding<'b> -> embedding<('a -> 'b)>

val mk_any_emb : typ -> embedding<term>

(* Arity specific raw_embeddings of arrows; used to generate top-level
   registrations of compiled functions in FStar.Extraction.ML.Util *)
val arrow_as_prim_step_1:  embedding<'a>
                        -> embedding<'b>
                        -> ('a -> 'b)
                        -> n_tvars:int
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (args -> option<term>)

val arrow_as_prim_step_2:  embedding<'a>
                        -> embedding<'b>
                        -> embedding<'c>
                        -> ('a -> 'b -> 'c)
                        -> n_tvars:int
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (args -> option<term>)

val arrow_as_prim_step_3:  embedding<'a>
                        -> embedding<'b>
                        -> embedding<'c>
                        -> embedding<'d>
                        -> ('a -> 'b -> 'c -> 'd)
                        -> n_tvars:int
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (args -> option<term>)