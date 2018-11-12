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
module NRE = FStar.Reflection.NBEEmbeddings
module Ident = FStar.Ident
module EMB = FStar.Syntax.Embeddings
module NBET = FStar.TypeChecker.NBETerm

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
                 (psc:Cfg.psc) n (args : args) : option<term> =
    match args with
    | [(a, _)] ->
        BU.bind_opt (try_unembed ea a n) (fun a ->
        Some (embed er (Cfg.psc_range psc) (f a) n))
    | _ -> None

let int2 (m:lid) (f:'a -> 'b -> 'r) (ea:embedding<'a>) (eb:embedding<'b>) (er:embedding<'r>)
                 (psc:Cfg.psc) n (args : args) : option<term> =
    match args with
    | [(a, _); (b, _)] ->
        BU.bind_opt (try_unembed ea a n) (fun a ->
        BU.bind_opt (try_unembed eb b n) (fun b ->
        Some (embed er (Cfg.psc_range psc) (f a b) n)))
    | _ -> None

let nbe_int1 (m:lid) (f:'a -> 'r) (ea:NBET.embedding<'a>) (er:NBET.embedding<'r>)
                     (cb:NBET.nbe_cbs) (args : NBET.args) : option<NBET.t> =
    match args with
    | [(a, _)] ->
        BU.bind_opt (NBET.unembed ea cb a) (fun a ->
        Some (NBET.embed er cb (f a)))
    | _ -> None

let nbe_int2 (m:lid) (f:'a -> 'b -> 'r) (ea:NBET.embedding<'a>) (eb:NBET.embedding<'b>) (er:NBET.embedding<'r>)
                     (cb:NBET.nbe_cbs) (args : NBET.args) : option<NBET.t> =
    match args with
    | [(a, _); (b, _)] ->
        BU.bind_opt (NBET.unembed ea cb a) (fun a ->
        BU.bind_opt (NBET.unembed eb cb b) (fun b ->
        Some (NBET.embed er cb (f a b))))
    | _ -> None

let mklid (nm : string) : lid = fstar_refl_basic_lid nm

let mk (l : lid) (arity : int) (fn     : Cfg.psc -> norm_cb -> args -> option<term>)
                               (nbe_fn : NBET.nbe_cbs -> NBET.args -> option<NBET.t>) : Cfg.primitive_step
  =
  { Cfg.name                         = l
  ; Cfg.arity                        = arity
  ; Cfg.univ_arity                   = 0 (* There are currently no polymorphic reflection primitives *)
  ; Cfg.auto_reflect                 = None
  ; Cfg.strong_reduction_ok          = true
  ; Cfg.requires_binder_substitution = false
  ; Cfg.interpretation               = fn
  ; Cfg.interpretation_nbe           = nbe_fn
  }

let mk1 nm (f  : 'a  -> 'r)  (ea  : embedding<'a>)       (er  : embedding<'r>)
           (nf : 'na -> 'nr) (ena : NBET.embedding<'na>) (enr : NBET.embedding<'nr>) : Cfg.primitive_step =
    let l = mklid nm in
    mk l 1 (int1     l  f  ea  er)
           (nbe_int1 l nf ena enr)

let mk2 nm (f  : 'a  -> 'b  -> 'r)  (ea  : embedding<'a>)       (eb  : embedding<'b>)       (er  : embedding<'r>)
           (nf : 'na -> 'nb -> 'nr) (ena : NBET.embedding<'na>) (enb : NBET.embedding<'nb>) (enr : NBET.embedding<'nr>) : Cfg.primitive_step =
    let l = mklid nm in
    mk l 2 (int2     l  f  ea  eb  er)
           (nbe_int2 l nf ena enb enr)

let reflection_primops : list<Cfg.primitive_step> = [
    mk1 "inspect_ln"            inspect_ln            E.e_term            E.e_term_view
                                inspect_ln            NRE.e_term          NRE.e_term_view;

    mk1 "pack_ln"               pack_ln               E.e_term_view       E.e_term
                                pack_ln               NRE.e_term_view     NRE.e_term;

    mk1 "inspect_fv"            inspect_fv            E.e_fv              e_string_list
                                inspect_fv            NRE.e_fv            NBET.e_string_list;

    mk1 "pack_fv"               pack_fv               e_string_list       E.e_fv
                                pack_fv               NBET.e_string_list  NRE.e_fv;

    mk1 "inspect_comp"          inspect_comp          E.e_comp            E.e_comp_view
                                inspect_comp          NRE.e_comp          NRE.e_comp_view;

    mk1 "pack_comp"             pack_comp             E.e_comp_view       E.e_comp
                                pack_comp             NRE.e_comp_view     NRE.e_comp;

    mk1 "inspect_sigelt"        inspect_sigelt        E.e_sigelt          E.e_sigelt_view
                                inspect_sigelt        NRE.e_sigelt        NRE.e_sigelt_view;

    mk1 "pack_sigelt"           pack_sigelt           E.e_sigelt_view     E.e_sigelt
                                pack_sigelt           NRE.e_sigelt_view   NRE.e_sigelt;

    mk1 "inspect_bv"            inspect_bv            E.e_bv              E.e_bv_view
                                inspect_bv            NRE.e_bv            NRE.e_bv_view;

    mk1 "pack_bv"               pack_bv               E.e_bv_view         E.e_bv
                                pack_bv               NRE.e_bv_view       NRE.e_bv;

    mk1 "sigelt_attrs"          sigelt_attrs          E.e_sigelt          E.e_attributes
                                sigelt_attrs          NRE.e_sigelt        NRE.e_attributes;

    mk2 "set_sigelt_attrs"      set_sigelt_attrs      E.e_attributes      E.e_sigelt         E.e_sigelt
                                set_sigelt_attrs      NRE.e_attributes    NRE.e_sigelt       NRE.e_sigelt;

    mk1 "inspect_binder"        inspect_binder        E.e_binder          E.e_binder_view
                                inspect_binder        NRE.e_binder        NRE.e_binder_view;

    mk2 "pack_binder"           pack_binder           E.e_bv              E.e_aqualv         E.e_binder
                                pack_binder           NRE.e_bv            NRE.e_aqualv       NRE.e_binder;

    mk2 "compare_bv"            compare_bv            E.e_bv              E.e_bv             E.e_order
                                compare_bv            NRE.e_bv            NRE.e_bv           NRE.e_order;

    mk2 "is_free"               is_free               E.e_bv              E.e_term           e_bool
                                is_free               NRE.e_bv            NRE.e_term         NBET.e_bool;

    mk2 "lookup_attr"           RB.lookup_attr        E.e_term            E.e_env            (e_list E.e_fv)
                                RB.lookup_attr        NRE.e_term          NRE.e_env          (NBET.e_list NRE.e_fv);

    mk2 "term_eq"               term_eq               E.e_term            E.e_term           e_bool
                                term_eq               NRE.e_term          NRE.e_term         NBET.e_bool;

    mk1 "moduleof"              moduleof              E.e_env             e_string_list
                                moduleof              NRE.e_env           NBET.e_string_list;

    mk1 "term_to_string"        term_to_string        E.e_term            e_string
                                term_to_string        NRE.e_term          NBET.e_string;

    mk1 "binders_of_env"        binders_of_env        E.e_env             E.e_binders
                                binders_of_env        NRE.e_env           NRE.e_binders;

    mk2 "lookup_typ"            lookup_typ            E.e_env             e_string_list      (e_option E.e_sigelt)
                                lookup_typ            NRE.e_env           NBET.e_string_list (NBET.e_option NRE.e_sigelt);
]
