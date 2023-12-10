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
module FStar.Reflection.V1.Interpreter

module BU    = FStar.Compiler.Util
module Cfg   = FStar.TypeChecker.Cfg
module EMB   = FStar.Syntax.Embeddings
module Env   = FStar.TypeChecker.Env
module NBET  = FStar.TypeChecker.NBETerm
module NRE   = FStar.Reflection.V1.NBEEmbeddings
module PO    = FStar.TypeChecker.Primops
module RB    = FStar.Reflection.V1.Builtins
module RD    = FStar.Reflection.V1.Data
module RE    = FStar.Reflection.V1.Embeddings
module Z     = FStar.BigInt
module Range = FStar.Compiler.Range
open FStar.Compiler
open FStar.Compiler.List
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.Reflection.V1.Constants
open FStar.Class.Monad

// FIXME: why are the #a needed?
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
      let! a = try_unembed a n in
      return (embed (PO.psc_range psc) (f a) n)
    | _ -> None

let int2 (m:lid)
         {| EMB.embedding 'a |} {| EMB.embedding 'b |} {| EMB.embedding 'r |}
         (f:'a -> 'b -> 'r)
         (psc:PO.psc) n (args : args) : option term =
    match args with
    | [(a, _); (b, _)] ->
      let! a = try_unembed a n in
      let! b = try_unembed b n in
      return (embed (PO.psc_range psc) (f a b) n)
    | _ -> None

let int3 (m:lid)
         {| EMB.embedding 'a |} {| EMB.embedding 'b |} {| EMB.embedding 'c |} {| EMB.embedding 'r |}
         (f:'a -> 'b -> 'c -> 'r)
         (psc:PO.psc) n (args : args) : option term =
    match args with
    | [(a, _); (b, _); (c, _)] ->
      let! a = try_unembed a n in
      let! b = try_unembed b n in
      let! c = try_unembed c n in
      return (embed (PO.psc_range psc) (f a b c) n)
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
instance e_bv              : dualemb bv                 = Mkdualemb RE.e_bv NRE.e_bv
instance e_bv_view         : dualemb RD.bv_view         = Mkdualemb RE.e_bv_view NRE.e_bv_view
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
instance e_attributes      : dualemb (list attribute)   = Mkdualemb RE.e_attributes NRE.e_attributes
instance e_qualifiers      : dualemb RD.qualifiers      = Mkdualemb RE.e_qualifiers NRE.e_qualifiers
instance e_range           : dualemb Range.range              =
  Mkdualemb FStar.Syntax.Embeddings.e_range FStar.TypeChecker.NBETerm.e_range

instance e_list (e : dualemb 'a) : Tot (dualemb (list 'a)) =
  { s_emb = EMB.e_list e.s_emb;
    nbe_emb = NBET.e_list e.nbe_emb; }

instance e_option (e : dualemb 'a) : Tot (dualemb (option 'a)) =
  { s_emb = EMB.e_option e.s_emb;
    nbe_emb = NBET.e_option e.nbe_emb; }

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
 * FStar.Reflection.V1.Builtins module and implement them using the (internal)
 * inspect_ln and pack_ln functions, which means they should not break
 * the view abstraction.
 *
 * _Any_ call to functions elsewhere, say term_to_string or
 * Util.term_eq, will _very likely_ be inconsistent with the view.
 * Exceptions to the "way to go" above should be well justified.
 *)
let reflection_primops : list PO.primitive_step = [
  (****** Inspecting/packing various kinds of syntax ******)
  mk1 "inspect_ln" RB.inspect_ln ;
  mk1 "pack_ln" RB.pack_ln ;

  mk1 "inspect_fv" RB.inspect_fv;
  mk1 "pack_fv"    RB.pack_fv;

  mk1 "inspect_comp" RB.inspect_comp ;
  mk1 "pack_comp" RB.pack_comp ;

  mk1 "inspect_universe" RB.inspect_universe ;
  mk1 "pack_universe" RB.pack_universe ;
  mk1 "inspect_sigelt" RB.inspect_sigelt ;
  mk1 "pack_sigelt" RB.pack_sigelt ;
  mk1 "inspect_lb" RB.inspect_lb ;
  mk1 "pack_lb" RB.pack_lb ;
  mk1 "inspect_bv" RB.inspect_bv ;
  mk1 "pack_bv" RB.pack_bv ;

  (* TODO: Make this consistent with others? No good reason for it to be "exploded" *)
  mk1 "inspect_binder" RB.inspect_binder;
  mk1 "pack_binder" RB.pack_binder;

  (****** Actual primitives ******)

  mk1 "sigelt_opts" RB.sigelt_opts;

  (* This exposes the embedding of vconfig since it is useful to create attributes *)
  mk1 "embed_vconfig" RB.embed_vconfig;

  mk1 "sigelt_attrs" RB.sigelt_attrs;
  mk2 "set_sigelt_attrs" RB.set_sigelt_attrs;
  mk1 "sigelt_quals" RB.sigelt_quals;
  mk2 "set_sigelt_quals" RB.set_sigelt_quals;
  mk3 "subst" RB.subst;
  mk2 "close_term" RB.close_term;
  mk2 "compare_bv" RB.compare_bv;
  mk2 "lookup_attr" RB.lookup_attr;
  mk1 "all_defs_in_env" RB.all_defs_in_env;
  mk2 "defs_in_module" RB.defs_in_module;

  mk2 "term_eq" RB.term_eq;
  mk1 "moduleof" RB.moduleof;
  mk1 "binders_of_env" RB.binders_of_env;
  mk2 "lookup_typ" RB.lookup_typ;
  mk1 "env_open_modules" RB.env_open_modules;

  (* See note in ulib/FStar.Reflection.V1.Builints.fsti: we expose these
     three to reduce dependencies. *)
  mk1 "implode_qn" RB.implode_qn;

  mk1 "explode_qn" RB.explode_qn;
  mk2 "compare_string" RB.compare_string;
  mk2 "push_binder" RB.push_binder;
  mk1 "range_of_term" RB.range_of_term;
  mk1 "range_of_sigelt" RB.range_of_sigelt;
]

let _ = List.iter FStar.TypeChecker.Cfg.register_extra_step reflection_primops
