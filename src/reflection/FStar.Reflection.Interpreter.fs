#light "off"
module FStar.Reflection.Interpreter

module Cfg = FStar.TypeChecker.Cfg
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
module NBE = FStar.TypeChecker.NBETerm
module Ident = FStar.Ident
module EMB = FStar.Syntax.Embeddings

let unembed ea a norm_cb = EMB.unembed ea a true norm_cb
let try_unembed ea a norm_cb = EMB.unembed ea a false norm_cb
let embed ea r x norm_cb = embed ea x r None norm_cb

(* We use `try_unembed` instead of `unembedding`, since we very well
 * might fail to unembed during the *previous* normalization stages
 * of metaprograms. When actually running, we certainly expect
 * everything to reduce to proper values and unembed just fine, but
 * we cannot ignore this case. So, use `try_` so we don't generate
 * spurious warnings. *)
let int1 (m:lid) (f:'a -> 'r) (ea:embedding<'a>) (er:embedding<'r>)
                 (r:Range.range) n (args : args) : option<term> =
    match args with
    | [(a, _)] ->
        BU.bind_opt (try_unembed ea a n) (fun a ->
        Some (embed er r (f a) n))
    | _ -> None

let int2 (m:lid) (f:'a -> 'b -> 'r) (ea:embedding<'a>) (eb:embedding<'b>) (er:embedding<'r>)
                 (r:Range.range) n (args : args) : option<term> =
    match args with
    | [(a, _); (b, _)] ->
        BU.bind_opt (try_unembed ea a n) (fun a ->
        BU.bind_opt (try_unembed eb b n) (fun b ->
        Some (embed er r (f a b) n)))
    | _ -> None

let reflection_primops : list<Cfg.primitive_step> =
    let mklid (nm : string) : lid = fstar_refl_basic_lid nm in
    let mk (l : lid) (arity : int) (fn : Range.range -> norm_cb -> args -> option<term>) : Cfg.primitive_step =
        {
            Cfg.name = l;
            Cfg.arity = arity;
            Cfg.univ_arity = 0;
            Cfg.auto_reflect = None;
            Cfg.strong_reduction_ok = false;
            Cfg.requires_binder_substitution = false;
            Cfg.interpretation = (fun ctxt n args -> fn (Cfg.psc_range ctxt) n args);
            Cfg.interpretation_nbe = (fun _cb args -> NBE.dummy_interp (Ident.lid_of_str "_") args);
        } in
    // GM: we need the annotation, otherwise F* will try to unify the types
    // for all mk1 calls. I guess a consequence that we don't generalize inner lets
    let mk1 nm (f : 'a -> 'b)       u1 em    : Cfg.primitive_step = let l = mklid nm in mk l 1 (int1 l f u1 em) in
    let mk2 nm (f : 'a -> 'b -> 'c) u1 u2 em : Cfg.primitive_step = let l = mklid nm in mk l 2 (int2 l f u1 u2 em) in
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

        mk1 "sigelt_attrs" sigelt_attrs E.e_sigelt E.e_attributes;
        mk2 "set_sigelt_attrs" set_sigelt_attrs E.e_attributes E.e_sigelt E.e_sigelt;

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
