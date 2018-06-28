#light "off"
module FStar.Reflection.Interpreter

module N = FStar.TypeChecker.Normalize
open FStar.Reflection.Data
open FStar.Reflection.Basic
module RB = FStar.Reflection.Basic
open FStar.Ident
open FStar.TypeChecker.Env
module Range = FStar.Range
open FStar.List
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
module Print = FStar.Syntax.Print
module BU = FStar.Util
module E = FStar.Reflection.Embeddings

let unembed ea a = unembed ea a true (fun x -> x)
let embed ea r x = embed ea x r None (fun x -> x)

let int1 (m:lid) (f:'a -> 'r) (ea:embedding<'a>) (er:embedding<'r>)
                 (r:Range.range) (args : args) : option<term> =
    match args with
    | [(a, _)] ->
        BU.bind_opt (unembed ea a) (fun a ->
        Some (embed er r (f a)))
    | _ -> None

let int2 (m:lid) (f:'a -> 'b -> 'r) (ea:embedding<'a>) (eb:embedding<'b>) (er:embedding<'r>)
                 (r:Range.range) (args : args) : option<term> =
    match args with
    | [(a, _); (b, _)] ->
        BU.bind_opt (unembed ea a) (fun a ->
        BU.bind_opt (unembed eb b) (fun b ->
        Some (embed er r (f a b))))
    | _ -> None

let reflection_primops : list<N.primitive_step> =
    let mklid (nm : string) : lid = fstar_refl_basic_lid nm in
    let mk (l : lid) (arity : int) (fn : Range.range -> args -> option<term>) : N.primitive_step =
        {
            N.name = l;
            N.arity = arity;
            N.auto_reflect = None;
            N.strong_reduction_ok = false;
            N.requires_binder_substitution = false;
            N.interpretation = (fun ctxt args -> fn (N.psc_range ctxt) args)
        } in
    // GM: we need the annotation, otherwise F* will try to unify the types
    // for all mk1 calls. I guess a consequence that we don't generalize inner lets
    let mk1 nm (f : 'a -> 'b)       u1 em    : N.primitive_step = let l = mklid nm in mk l 1 (int1 l f u1 em) in
    let mk2 nm (f : 'a -> 'b -> 'c) u1 u2 em : N.primitive_step = let l = mklid nm in mk l 2 (int2 l f u1 u2 em) in
    [
        mk1 "inspect_ln" inspect_ln E.e_term E.e_term_view;
        mk1 "pack_ln"    pack_ln    E.e_term_view E.e_term;

        mk1 "inspect_fv" inspect_fv E.e_fv e_string_list;
        mk1 "pack_fv" pack_fv (e_list e_string) E.e_fv;

        mk1 "inspect_comp" inspect_comp E.e_comp E.e_comp_view;
        mk1 "pack_comp"    pack_comp E.e_comp_view E.e_comp;

        mk1 "inspect_sigelt" inspect_sigelt E.e_sigelt E.e_sigelt_view;
        mk1 "pack_sigelt"    pack_sigelt E.e_sigelt_view E.e_sigelt;

        mk1 "inspect_bv" inspect_bv E.e_bv   E.e_bv_view;
        mk1 "pack_bv"    pack_bv E.e_bv_view E.e_bv;

        mk1 "inspect_binder" inspect_binder E.e_binder E.e_binder_view;

        mk2 "pack_binder"    pack_binder E.e_bv E.e_aqualv E.e_binder;

        mk2 "compare_bv" compare_bv E.e_bv E.e_bv E.e_order;

        mk2 "is_free" is_free E.e_bv E.e_term e_bool;

        mk2 "lookup_attr" RB.lookup_attr E.e_term E.e_env (e_list E.e_fv);

        mk2 "term_eq" term_eq E.e_term E.e_term e_bool;

        mk1 "moduleof" moduleof E.e_env (e_list e_string);
        mk1 "term_to_string" term_to_string E.e_term e_string;
        mk1 "binders_of_env" binders_of_env E.e_env E.e_binders;
        mk2 "lookup_typ" lookup_typ E.e_env e_string_list (e_option E.e_sigelt);
    ]
