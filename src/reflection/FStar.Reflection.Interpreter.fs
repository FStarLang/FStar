#light "off"
module FStar.Reflection.Interpreter

module N = FStar.TypeChecker.Normalize
open FStar.Reflection.Data
open FStar.Reflection.Basic
open FStar.Ident
open FStar.TypeChecker.Env
module Range = FStar.Range
open FStar.List
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
module Print = FStar.Syntax.Print
module BU = FStar.Util

let int1 (m:lid) (f:'a -> 'b) (ua:term -> option<'a>) (em:'b -> term)
                 (r:Range.range) (args : args) : option<term> =
    match args with
    | [(a, _)] ->
        BU.bind_opt (ua a) (fun a ->
        Some (em (f a)))
    | _ -> None

let int2 (m:lid) (f:'a -> 'b -> 'c) (ua:term -> option<'a>) (ub:term -> option<'b>) (em:'c -> term)
                 (r:Range.range) (args : args) : option<term> =
    match args with
    | [(a, _); (b, _)] ->
        BU.bind_opt (ua a) (fun a ->
        BU.bind_opt (ub b) (fun b ->
        Some (em (f a b))))
    | _ -> None

let reflection_primops : list<N.primitive_step> =
    let mklid (nm : string) : lid = fstar_refl_basic_lid nm in
    let mk (l : lid) (arity : int) (fn : Range.range -> args -> option<term>) : N.primitive_step =
        {
            N.name = l;
            N.arity = arity;
            N.strong_reduction_ok = false;
            N.requires_binder_substitution = false;
            N.interpretation = (fun ctxt args -> fn (N.psc_range ctxt) args)
        } in
    // GM: we need the annotation, otherwise F* will try to unify the types
    // for all mk1 calls. I guess a consequence that we don't generalize inner lets
    let mk1 nm (f : 'a -> 'b)       u1 em    : N.primitive_step = let l = mklid nm in mk l 1 (int1 l f u1 em) in
    let mk2 nm (f : 'a -> 'b -> 'c) u1 u2 em : N.primitive_step = let l = mklid nm in mk l 2 (int2 l f u1 u2 em) in
    [
        mk1 "__inspect" inspect unembed_term embed_term_view;
        mk1 "__pack"    pack    unembed_term_view embed_term;

        mk1 "__inspect_fv" inspect_fv unembed_fvar embed_string_list;
        mk1 "__pack_fv" pack_fv (unembed_list unembed_string) embed_fvar;

        mk1 "__inspect_comp" inspect_comp unembed_comp embed_comp_view;
        mk1 "__pack_comp"    pack_comp unembed_comp_view embed_comp;

        mk1 "__inspect_bv" inspect_bv unembed_binder embed_string;
        mk2 "__compare_binder" compare_binder unembed_binder unembed_binder embed_order;
        mk1 "__type_of_binder" type_of_binder unembed_binder embed_term;
        mk2 "__is_free" is_free unembed_binder unembed_term embed_bool;
        mk1 "__fresh_binder" fresh_binder unembed_term embed_binder;

        mk2 "__term_eq" term_eq unembed_term unembed_term embed_bool;

        mk1 "__term_to_string" term_to_string unembed_term embed_string;
        mk1 "__binders_of_env" binders_of_env unembed_env embed_binders;
        mk2 "__lookup_typ" lookup_typ unembed_env unembed_string_list embed_sigelt_view;
    ]
