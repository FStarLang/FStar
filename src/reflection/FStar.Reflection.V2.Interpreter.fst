(*
   Copyright 2008-2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Reflection.V2.Interpreter

module BU    = FStar.Compiler.Util
module Cfg   = FStar.TypeChecker.Cfg
module EMB   = FStar.Syntax.Embeddings
module Env   = FStar.TypeChecker.Env
module NBET  = FStar.TypeChecker.NBETerm
module NRE   = FStar.Reflection.V2.NBEEmbeddings
module PO    = FStar.TypeChecker.Primops
module RB    = FStar.Reflection.V2.Builtins
module RD    = FStar.Reflection.V2.Data
module RE    = FStar.Reflection.V2.Embeddings
module Z     = FStar.BigInt
module Range = FStar.Compiler.Range
open FStar.Compiler
open FStar.Compiler.List
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.Reflection.V2.Constants
open FStar.Class.Monad

let unembed #a {| EMB.embedding a |} (x:a) norm_cb = EMB.unembed #a x norm_cb
let try_unembed #a {| EMB.embedding a |} x norm_cb = EMB.try_unembed #a x norm_cb
let embed #a {| EMB.embedding a |} r x norm_cb     = EMB.embed #a x r None norm_cb

(* We use `try_unembed` instead of `unembedding`, since we very well
 * might fail to unembed during the *previous* normalization stages
 * of metaprograms. When actually running, we certainly expect
 * everything to reduce to proper values and unembed just fine, but
 * we cannot ignore this case. So, use `try_` so we don't generate
 * spurious warnings. *)

let int1 (m:lid)
         {| EMB.embedding 'a |} {| EMB.embedding 'r |}
         (f:'a -> 'r)
         (psc:PO.psc) n (args : args) : option term =
    match args with
    | [(a, _)] ->
      let! v = f <$> try_unembed a n in
      return (embed (PO.psc_range psc) v n)
    | _ -> None

let int2 (m:lid)
         {| EMB.embedding 'a |} {| EMB.embedding 'b |} {| EMB.embedding 'r |}
         (f:'a -> 'b -> 'r)
         (psc:PO.psc) n (args : args) : option term =
    match args with
    | [(a, _); (b, _)] ->
      let! v = f <$> try_unembed a n <*> try_unembed b n in
      return (embed (PO.psc_range psc) v n)
    | _ -> None

let int3 (m:lid)
         {| EMB.embedding 'a |} {| EMB.embedding 'b |} {| EMB.embedding 'c |} {| EMB.embedding 'r |}
         (f:'a -> 'b -> 'c -> 'r)
         (psc:PO.psc) n (args : args) : option term =
    match args with
    | [(a, _); (b, _); (c, _)] ->
      let! v = (f <$> try_unembed a n <*> try_unembed b n) <*> try_unembed c n in
      return (embed (PO.psc_range psc) v n)
    | _ -> None

let nbe_int1 (m:lid) (f:'a -> 'r) (ea:NBET.embedding 'a) (er:NBET.embedding 'r)
                     (cb:NBET.nbe_cbs) (args : NBET.args) : option NBET.t =
    match args with
    | [(a, _)] ->
        BU.bind_opt (NBET.unembed ea cb a) (fun a ->
        Some (NBET.embed er cb (f a)))
    | _ -> None

let nbe_int2 (m:lid) (f:'a -> 'b -> 'r) (ea:NBET.embedding 'a) (eb:NBET.embedding 'b) (er:NBET.embedding 'r)
                     (cb:NBET.nbe_cbs) (args : NBET.args) : option NBET.t =
    match args with
    | [(a, _); (b, _)] ->
        BU.bind_opt (NBET.unembed ea cb a) (fun a ->
        BU.bind_opt (NBET.unembed eb cb b) (fun b ->
        Some (NBET.embed er cb (f a b))))
    | _ -> None

let nbe_int3 (m:lid) (f:'a -> 'b -> 'c -> 'r) (ea:NBET.embedding 'a) (eb:NBET.embedding 'b) (ec:NBET.embedding 'c) (er:NBET.embedding 'r)
                     (cb:NBET.nbe_cbs) (args : NBET.args) : option NBET.t =
    match args with
    | [(a, _); (b, _); (c, _)] ->
        BU.bind_opt (NBET.unembed ea cb a) (fun a ->
        BU.bind_opt (NBET.unembed eb cb b) (fun b ->
        BU.bind_opt (NBET.unembed ec cb c) (fun c ->
        Some (NBET.embed er cb (f a b c)))))
    | _ -> None
let mklid (nm : string) : lid = fstar_refl_builtins_lid nm

let mk_us (l : lid) (u_arity:int) (arity : int)
            (fn     : PO.psc -> EMB.norm_cb -> args -> option term)
            (nbe_fn : NBET.nbe_cbs -> NBET.args -> option NBET.t) : PO.primitive_step
  =
  { name                         = l
  ; arity                        = arity
  ; univ_arity                   = u_arity
  ; auto_reflect                 = None
  ; strong_reduction_ok          = true
  ; requires_binder_substitution = false
  ; renorm_after                 = false
  ; interpretation               = (fun psc cbs _us args -> fn psc cbs args)
  ; interpretation_nbe           = (fun cbs _us args -> nbe_fn cbs args)
  }

(* Most primitives are not universe polymorphic. *)
let mk l arity fn nbe_fn = mk_us l 0 arity fn nbe_fn

(*
 ** Packing both regular and NBE embedding in a single type, for brevity
 ** in the table below. This should all be unfolded at F* initialization
 ** time so it won't be a performance concern.
 *)
class dualemb 'a = {
  s_emb : EMB.embedding 'a;
  nbe_emb : NBET.embedding 'a;
}

instance emb_from_dual (d : dualemb 'a) : Tot (EMB.embedding 'a) = d.s_emb

instance e_int             : dualemb Z.t                = Mkdualemb EMB.e_int NBET.e_int
instance e_bool            : dualemb bool               = Mkdualemb EMB.e_bool NBET.e_bool
instance e_string          : dualemb string             = Mkdualemb EMB.e_string NBET.e_string
instance e_order           : dualemb FStar.Order.order  = Mkdualemb RE.e_order NRE.e_order

instance e_term            : dualemb term               = Mkdualemb RE.e_term NRE.e_term
instance e_term_view       : dualemb RD.term_view       = Mkdualemb RE.e_term_view NRE.e_term_view
instance e_fv              : dualemb fv                 = Mkdualemb RE.e_fv NRE.e_fv
let      e_bv              : dualemb bv                 = Mkdualemb RE.e_bv NRE.e_bv
let      e_namedv          : dualemb RE.namedv          = Mkdualemb RE.e_namedv NRE.e_namedv
instance e_bv_view         : dualemb RD.bv_view         = Mkdualemb RE.e_bv_view NRE.e_bv_view
instance e_namedv_view     : dualemb RD.namedv_view     = Mkdualemb RE.e_namedv_view NRE.e_namedv_view
instance e_binding         : dualemb RD.binding         = Mkdualemb RE.e_binding NRE.e_binding
instance e_comp            : dualemb comp               = Mkdualemb RE.e_comp NRE.e_comp
instance e_comp_view       : dualemb RD.comp_view       = Mkdualemb RE.e_comp_view NRE.e_comp_view
instance e_universe        : dualemb universe           = Mkdualemb RE.e_universe NRE.e_universe
instance e_universe_view   : dualemb RD.universe_view   = Mkdualemb RE.e_universe_view NRE.e_universe_view
instance e_sigelt          : dualemb sigelt             = Mkdualemb RE.e_sigelt NRE.e_sigelt
instance e_sigelt_view     : dualemb RD.sigelt_view     = Mkdualemb RE.e_sigelt_view NRE.e_sigelt_view
instance e_binder          : dualemb binder             = Mkdualemb RE.e_binder NRE.e_binder
instance e_binder_view     : dualemb RD.binder_view     = Mkdualemb RE.e_binder_view NRE.e_binder_view
instance e_binders         : dualemb binders            = Mkdualemb RE.e_binders NRE.e_binders

instance e_letbinding      : dualemb letbinding         = Mkdualemb RE.e_letbinding NRE.e_letbinding
instance e_lb_view         : dualemb RD.lb_view         = Mkdualemb RE.e_lb_view NRE.e_lb_view
(* ^ Inconsistent naming with these.. but too long otherwise and userspace has
 * lb_view already. Probably not worth the fix. *)

instance e_env             : dualemb Env.env            = Mkdualemb RE.e_env NRE.e_env
instance e_aqualv          : dualemb RD.aqualv          = Mkdualemb RE.e_aqualv NRE.e_aqualv
instance e_vconfig         : dualemb VConfig.vconfig    = Mkdualemb EMB.e_vconfig NBET.e_vconfig
instance e_qualifier       : dualemb RD.qualifier       = Mkdualemb RE.e_qualifier NRE.e_qualifier
instance e_range           : dualemb Range.range              =
  Mkdualemb FStar.Syntax.Embeddings.e_range FStar.TypeChecker.NBETerm.e_range

instance e_list (e : dualemb 'a) : Tot (dualemb (list 'a)) =
  { s_emb = EMB.e_list e.s_emb;
    nbe_emb = NBET.e_list e.nbe_emb; }

instance e_option (e : dualemb 'a) : Tot (dualemb (option 'a)) =
  { s_emb = EMB.e_option e.s_emb;
    nbe_emb = NBET.e_option e.nbe_emb; }

instance e_tuple2 (ea : dualemb 'a) (eb : dualemb 'b) : Tot (dualemb ('a & 'b)) = {
  s_emb = EMB.e_tuple2 ea.s_emb eb.s_emb;
  nbe_emb = NBET.e_tuple2 ea.nbe_emb eb.nbe_emb;
}

let nbe_dummy #a : NBET.embedding a =
  let open FStar.Compiler.Effect in
  NBET.mk_emb
    (fun _ _ -> failwith "nbe_dummy embed")
    (fun _ _ -> failwith "nbe_dummy unembed")
    (fun () -> NBET.mk_t NBET.Unknown)
    (fun () -> ET_abstract)

instance e_ident : dualemb Ident.ident = Mkdualemb RE.e_ident (nbe_dummy #Ident.ident)
instance e_subst_elt : dualemb subst_elt = Mkdualemb RE.e_subst_elt NRE.e_subst_elt


(** Helpers to create a (total) primitive step from a function and embeddings. *)
let mk1 (nm : string)
    {|ea  : dualemb 'a|} {|er : dualemb 'r|}
    (f : 'a  -> 'r)
: PO.primitive_step =
    let l = mklid nm in
    mk l 1 (int1     l f)
           (nbe_int1 l f ea.nbe_emb er.nbe_emb)

let mk2 (nm : string)
    {|ea  : dualemb 'a|} {|eb : dualemb 'b|} {|er : dualemb 'r|}
    (f : 'a  -> 'b -> 'r)
: PO.primitive_step =
    let l = mklid nm in
    mk l 2 (int2     l f)
           (nbe_int2 l f ea.nbe_emb eb.nbe_emb er.nbe_emb)

let mk3 (nm : string)
    {|ea  : dualemb 'a|} {|eb : dualemb 'b|} {|ec : dualemb 'c|} {|er : dualemb 'r|}
    (f  : 'a  -> 'b -> 'c -> 'r)
: PO.primitive_step =
    let l = mklid nm in
    mk l 3 (int3     l f)
           (nbe_int3 l f ea.nbe_emb eb.nbe_emb ec.nbe_emb er.nbe_emb)

(*
 * NOTE: all primitives must be carefully inspected to make sure they
 * do not break the abstraction barrier imposed by the term_view.
 * Otherwise, the pack_inspect_inv and inspect_pack_inv lemmas could
 * likely be used to derive a contradiction.
 *
 * The way to go about adding new primitives is to implement them in the
 * FStar.Reflection.V2.Builtins module and implement them using the (internal)
 * inspect_ln and pack_ln functions, which means they should not break
 * the view abstraction.
 *
 * _Any_ call to functions elsewhere, say term_to_string or
 * Util.term_eq, will _very likely_ be inconsistent with the view.
 * Exceptions to the "way to go" above should be well justified.
 *)
let reflection_primops : list PO.primitive_step = [
  (****** Inspecting/packing various kinds of syntax ******)
  mk1 "inspect_ln" RB.inspect_ln;
  mk1 "pack_ln" RB.pack_ln;
  mk1 "inspect_fv" RB.inspect_fv;
  mk1 "pack_fv" RB.pack_fv;
  mk1 "inspect_comp" RB.inspect_comp;
  mk1 "pack_comp" RB.pack_comp;
  mk1 "inspect_universe" RB.inspect_universe;
  mk1 "pack_universe" RB.pack_universe;
  mk1 "inspect_sigelt" RB.inspect_sigelt;
  mk1 "pack_sigelt" RB.pack_sigelt;
  mk1 "inspect_lb" RB.inspect_lb;
  mk1 "pack_lb" RB.pack_lb;
  mk1 "inspect_namedv"
    #e_namedv #e_namedv_view
    RB.inspect_namedv;
  mk1 "pack_namedv"
    #e_namedv_view #e_namedv
    RB.pack_namedv;
  mk1 "inspect_bv"
    #e_bv #e_bv_view
    RB.inspect_bv;
  mk1 "pack_bv"
    #e_bv_view #e_bv
    RB.pack_bv;
  mk1 "inspect_binder" RB.inspect_binder;
  mk1 "pack_binder" RB.pack_binder;

  (****** Actual primitives ******)

  mk1 "sigelt_opts" RB.sigelt_opts;
  mk1 "embed_vconfig" RB.embed_vconfig;
  mk1 "sigelt_attrs" RB.sigelt_attrs;
  mk2 "set_sigelt_attrs" RB.set_sigelt_attrs;
  mk1 "sigelt_quals" RB.sigelt_quals;
  mk2 "set_sigelt_quals" RB.set_sigelt_quals;
  mk2 "subst_term" RB.subst_term;
  mk2 "subst_comp" RB.subst_comp;
  mk2 "compare_bv"
    #e_bv #e_bv
    RB.compare_bv;
  mk2 "compare_namedv"
    #e_namedv #e_namedv
    RB.compare_namedv;
  mk2 "lookup_attr" RB.lookup_attr;
  mk1 "all_defs_in_env" RB.all_defs_in_env;
  mk2 "defs_in_module" RB.defs_in_module;
  mk2 "term_eq" RB.term_eq;
  mk1 "moduleof" RB.moduleof;
  mk1 "vars_of_env" RB.vars_of_env;
  mk2 "lookup_typ" RB.lookup_typ;
  mk1 "env_open_modules" RB.env_open_modules;

  (* See note in ulib/FStar.Reflection.V2.Builints.fsti: we expose these
     three to reduce dependencies. *)
  mk1 "implode_qn" RB.implode_qn;

  mk1 "explode_qn" RB.explode_qn;
  mk2 "compare_string" RB.compare_string;
  mk2 "push_namedv"
    #e_env #e_namedv
    RB.push_namedv;
  mk1 "range_of_term" RB.range_of_term;
  mk1 "range_of_sigelt" RB.range_of_sigelt;
  mk1 "inspect_ident" RB.inspect_ident;
  mk1 "pack_ident" RB.pack_ident;
]

let _ = List.iter FStar.TypeChecker.Cfg.register_extra_step reflection_primops