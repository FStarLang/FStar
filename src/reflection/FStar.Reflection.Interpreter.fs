#light "off"
module FStar.Reflection.Interpreter

module N = FStar.TypeChecker.Normalize
open FStar.Reflection.Data
open FStar.Reflection.Basic
open FStar.Ident
module Range = FStar.Range
open FStar.List
open FStar.Syntax.Syntax
module Print = FStar.Syntax.Print

let int1 (m:lid) (f:'a -> 'b) (ua:term -> 'a) (em:'b -> term)
                 (r:Range.range) (args : args) : option<term> =
    match args with
    | [(a, _)] -> Some (em (f (ua a)))
    | _ -> None

let int2 (m:lid) (f:'a -> 'b -> 'c) (ua:term -> 'a) (ub:term -> 'b) (em:'c -> term)
                 (r:Range.range) (args : args) : option<term> =
    match args with
    | [(a, _); (b, _)] -> Some (em (f (ua a) (ub b)))
    | _ -> None

let reflection_primops : list<N.primitive_step> =
    let mklid (nm : string) : lid = fstar_refl_syntax_lid nm in
    let mk (l : lid) (arity : int) (fn : Range.range -> args -> option<term>) : N.primitive_step =
        {
            N.name = l;
            N.arity = arity;
            N.strong_reduction_ok = false;
            N.interpretation = fn
        } in
    // GM: we need the annotation, otherwise F* will try to unify the types
    // for all mk1 calls. I guess a consequence that we don't generalize inner lets
    let mk1 nm (f : 'a -> 'b) u1 em    : N.primitive_step = let l = mklid nm in mk l 1 (int1 l f u1 em) in
    let mk2 nm (f : 'a -> 'b -> 'c) u1 u2 em : N.primitive_step = let l = mklid nm in mk l 2 (int2 l f u1 u2 em) in
    [
        mk1 "__inspect" inspect unembed_term embed_term_view;
        mk1 "__pack"    pack    unembed_term_view (embed_option embed_term fstar_refl_term);

        mk1 "__inspect_fv" inspect_fv unembed_fvar (embed_list embed_string FStar.TypeChecker.Common.t_string);
        mk1 "__pack_fv" pack_fv (unembed_list unembed_string) embed_fvar;

        mk1 "__inspect_bv" inspect_bv unembed_binder embed_string;
        mk2 "__compare_binder" order_binder unembed_binder unembed_binder embed_order;

        //mk1 "__binders_of_env" Env.all_binders unembed_env embed_binders;
        mk1 "__type_of_binder" (fun (b,q) -> b.sort) unembed_binder embed_term;

        mk1 "__term_to_string" Print.term_to_string unembed_term embed_string
    ]
