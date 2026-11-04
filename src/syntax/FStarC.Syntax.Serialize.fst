(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Syntax.Serialize

open FStarC
open FStarC.Effect
open FStarC.Range.Type
open FStarC.Ident
open FStarC.Const
open FStarC.Syntax.Syntax
open FStarC.Serialize
open FStarC.Class.Deq
open FStarC.Class.Hashable
module H = FStarC.Hash

(* The constructor tags below are part of the format: append new ones. *)

let unexpected (#a:Type) (what:string) : ML a =
  failwith ("FStarC.Syntax.Serialize: cannot serialize " ^ what)

(* Ranges *)

let rng_eq (r1 r2 : rng) : bool =
  file_of_rng r1 = file_of_rng r2 &&
  int_of_pos (start_of_rng r1) = int_of_pos (start_of_rng r2) &&
  int_of_pos (end_of_rng r1) = int_of_pos (end_of_rng r2)

let rng_hash (r:rng) : H.hash_code =
  H.mix (H.of_int (int_of_pos (start_of_rng r)))
        (H.mix (H.of_int (int_of_pos (end_of_rng r))) (H.of_string (file_of_rng r)))

let deq_rng : deq rng = { (=?) = (fun r1 r2 -> rng_eq r1 r2) }
let hashable_rng : hashable rng = { hash = (fun r -> rng_hash r) }

let rng_slot = new_slot "rng"

instance serializable_rng : serializable rng =
  shared #rng #deq_rng #hashable_rng rng_slot {
    ser = (fun w r ->
      let s = int_of_pos (start_of_rng r) in
      ser w (file_of_rng r);
      ser w s;
      ser w (int_of_pos (end_of_rng r) - s));
    deser = (fun r ->
      let f : string = deser r in
      let s : int = deser r in
      let d : int = deser r in
      rng_of_parts f (pos_of_int s) (pos_of_int (s + d)));
  }

let range_eq (r1 r2 : range) : bool =
  rng_eq (def_range r1) (def_range r2) && rng_eq (use_range r1) (use_range r2)

let deq_range : deq range = { (=?) = (fun r1 r2 -> range_eq r1 r2) }
let hashable_range : hashable range =
  { hash = (fun r -> H.mix (rng_hash (def_range r)) (rng_hash (use_range r))) }

let range_slot = new_slot "range"

instance serializable_range : serializable range =
  shared #range #deq_range #hashable_range range_slot {
    ser = (fun w r -> ser w (def_range r); ser w (use_range r));
    deser = (fun r ->
      let d : rng = deser r in
      let u : rng = deser r in
      range_of_rng d u);
  }

(* Identifiers *)

let ident_eq (i1 i2 : ident) : bool =
  string_of_id i1 = string_of_id i2 && range_eq (range_of_id i1) (range_of_id i2)

let deq_ident : deq ident = { (=?) = (fun i1 i2 -> ident_eq i1 i2) }
let hashable_ident : hashable ident = { hash = (fun i -> H.of_string (string_of_id i)) }

let ident_slot = new_slot "ident"

instance serializable_ident : serializable ident =
  shared #ident #deq_ident #hashable_ident ident_slot {
    ser = (fun w i -> ser w (string_of_id i); ser w (range_of_id i));
    deser = (fun r ->
      let s : string = deser r in
      let rng : range = deser r in
      mk_ident (s, rng));
  }

let rec idents_eq (l1 l2 : list ident) : bool =
  match l1, l2 with
  | [], [] -> true
  | i1 :: l1, i2 :: l2 -> ident_eq i1 i2 && idents_eq l1 l2
  | _ -> false

let deq_lident : deq lident = {
  (=?) = (fun l1 l2 ->
    string_of_lid l1 = string_of_lid l2 &&
    ident_eq (ident_of_lid l1) (ident_of_lid l2) &&
    idents_eq (ns_of_lid l1) (ns_of_lid l2))
}
let hashable_lident : hashable lident = { hash = (fun l -> H.of_string (string_of_lid l)) }

let lident_slot = new_slot "lident"

instance serializable_lident : serializable lident =
  shared #lident #deq_lident #hashable_lident lident_slot {
    ser = (fun w l -> ser w (ns_of_lid l); ser w (ident_of_lid l));
    deser = (fun r ->
      let ns : list ident = deser r in
      let id : ident = deser r in
      lid_of_ns_and_id ns id);
  }

(* Constants *)

let ser_int_base (w:writer) (b:int_base) : ML unit =
  write_tag w (match b with Dec -> 0 | Hex -> 1 | Oct -> 2 | Bin -> 3)

let deser_int_base (r:reader) : ML int_base =
  match read_tag r with
  | 0 -> Dec | 1 -> Hex | 2 -> Oct | 3 -> Bin
  | t -> bad_tag "int_base" t

let ser_signedness (w:writer) (s:signedness) : ML unit =
  write_tag w (match s with Unsigned -> 0 | Signed -> 1)

let deser_signedness (r:reader) : ML signedness =
  match read_tag r with
  | 0 -> Unsigned | 1 -> Signed
  | t -> bad_tag "signedness" t

let ser_width (w:writer) (x:width) : ML unit =
  write_tag w (match x with Int8 -> 0 | Int16 -> 1 | Int32 -> 2 | Int64 -> 3 | Sizet -> 4)

let deser_width (r:reader) : ML width =
  match read_tag r with
  | 0 -> Int8 | 1 -> Int16 | 2 -> Int32 | 3 -> Int64 | 4 -> Sizet
  | t -> bad_tag "width" t

let ser_const (w:writer) (c:sconst) : ML unit =
  match c with
  | Const_effect -> write_tag w 0
  | Const_unit -> write_tag w 1
  | Const_bool b -> write_tag w 2; ser w b
  | Const_int (i, b) -> write_tag w 3; ser w i; ser_int_base w b
  | Const_machine_int (i, b, s, x) ->
    write_tag w 4; ser w i; ser_int_base w b; ser_signedness w s; ser_width w x
  | Const_char c -> write_tag w 5; ser w c
  | Const_real x -> write_tag w 6; ser w (Real.mantissa x); ser w (Real.exponent x)
  | Const_string (s, r) -> write_tag w 7; ser w s; ser w r
  | Const_range_of -> write_tag w 8
  | Const_set_range_of -> write_tag w 9
  | Const_range r -> write_tag w 10; ser w r
  | Const_reify l -> write_tag w 11; ser w l
  | Const_reflect l -> write_tag w 12; ser w l

let deser_const (r:reader) : ML sconst =
  match read_tag r with
  | 0 -> Const_effect
  | 1 -> Const_unit
  | 2 -> Const_bool (deser r)
  | 3 ->
    let i : int = deser r in
    let b = deser_int_base r in
    Const_int (i, b)
  | 4 ->
    let i : int = deser r in
    let b = deser_int_base r in
    let s = deser_signedness r in
    let x = deser_width r in
    Const_machine_int (i, b, s, x)
  | 5 -> Const_char (deser r)
  | 6 ->
    let m : int = deser r in
    let e : int = deser r in
    Const_real (Real.mk m e)
  | 7 ->
    let s : string = deser r in
    let rng : range = deser r in
    Const_string (s, rng)
  | 8 -> Const_range_of
  | 9 -> Const_set_range_of
  | 10 -> Const_range (deser r)
  | 11 -> Const_reify (deser r)
  | 12 -> Const_reflect (deser r)
  | t -> bad_tag "sconst" t

(* Universes *)

let rec ser_univ (w:writer) (u:universe) : ML unit =
  match u with
  | U_zero -> write_tag w 0
  | U_succ u -> write_tag w 1; ser_univ w u
  | U_max us -> write_tag w 2; ser_list ser_univ w us
  | U_bvar i -> write_tag w 3; ser w i
  | U_name x -> write_tag w 4; ser w x
  | U_unknown -> write_tag w 5
  | U_unif _ ->
    (match FStarC.Syntax.Subst.compress_univ u with
     | U_unif _ -> unexpected "a universe unification variable"
     | u -> ser_univ w u)

let rec deser_univ (r:reader) : ML universe =
  match read_tag r with
  | 0 -> U_zero
  | 1 -> U_succ (deser_univ r)
  | 2 -> U_max (deser_list deser_univ r)
  | 3 -> U_bvar (deser r)
  | 4 -> U_name (deser r)
  | 5 -> U_unknown
  | t -> bad_tag "universe" t

instance serializable_universe : serializable universe = {
  ser = ser_univ;
  deser = deser_univ;
}

let ser_univs (w:writer) (us:universes) : ML unit = ser_list ser_univ w us
let deser_univs (r:reader) : ML universes = deser_list deser_univ r

(* Terms *)

let deq_term : deq term = { (=?) = (fun t1 t2 -> Util.physical_equality t1 t2) }
let hashable_term : hashable term = { hash = (fun t -> t.hash_code) }

let deq_bv : deq bv = { (=?) = (fun x1 x2 -> Util.physical_equality x1 x2) }
let hashable_bv : hashable bv = { hash = (fun x -> H.mix (H.of_int x.index) x.sort.hash_code) }

let term_slot = new_slot "term"
let bv_slot = new_slot "bv"

let ser_meta_source_info (w:writer) (m:meta_source_info) : ML unit =
  match m with
  | Sequence -> write_tag w 0
  | Primop -> write_tag w 1
  | Masked_effect -> write_tag w 2
  | Meta_smt_pat -> write_tag w 3
  | Machine_integer (s, x) -> write_tag w 4; ser_signedness w s; ser_width w x

let deser_meta_source_info (r:reader) : ML meta_source_info =
  match read_tag r with
  | 0 -> Sequence
  | 1 -> Primop
  | 2 -> Masked_effect
  | 3 -> Meta_smt_pat
  | 4 ->
    let s = deser_signedness r in
    let x = deser_width r in
    Machine_integer (s, x)
  | t -> bad_tag "meta_source_info" t

let ser_doc (w:writer) (d:Pprint.document) : ML unit =
  ser w (Errors.Msg.renderdoc d)

let deser_doc (r:reader) : ML Pprint.document =
  Pprint.arbitrary_string (deser r)

let rec ser_term (w:writer) (t:term) : ML unit =
  match t.n with
  | Tm_lazy i ->
    (match !lazy_chooser with
     | Some f -> ser_term w (f i.lkind i)
     | None -> unexpected "a lazy term (no lazy_chooser)")
  (* Pushes a delayed substitution, or resolves a solved unification
     variable. *)
  | Tm_delayed _
  | Tm_uvar _ ->
    let t' = FStarC.Syntax.Subst.compress t in
    (match t'.n with
     | Tm_delayed _ -> unexpected "a delayed substitution"
     | Tm_uvar _ -> unexpected "a unification variable"
     | _ -> ser_term w t')
  | _ -> write_shared #term #deq_term #hashable_term term_slot w t ser_term_node

and ser_term_node (w:writer) (t:term) : ML unit =
  ser w t.pos;
  match t.n with
  | Tm_bvar x -> write_tag w 0; ser_bv w x
  | Tm_name x -> write_tag w 1; ser_bv w x
  | Tm_fvar fv -> write_tag w 2; ser_fv w fv
  | Tm_uinst (t, us) -> write_tag w 3; ser_term w t; ser_univs w us
  | Tm_constant c -> write_tag w 4; ser_const w c
  | Tm_type u -> write_tag w 5; ser_univ w u
  | Tm_abs {b; body; rc_opt} ->
    write_tag w 6; ser_binder w b; ser_term w body; ser_option ser_residual_comp w rc_opt
  | Tm_arrow {b; comp} -> write_tag w 7; ser_binder w b; ser_comp w comp
  | Tm_refine {b; phi} -> write_tag w 8; ser_bv w b; ser_term w phi
  | Tm_app {hd; arg} -> write_tag w 9; ser_term w hd; ser_arg w arg
  | Tm_match {scrutinee; ret_opt; brs; rc_opt} ->
    write_tag w 10;
    ser_term w scrutinee;
    ser_option ser_match_returns w ret_opt;
    ser_list ser_branch w brs;
    ser_option ser_residual_comp w rc_opt
  | Tm_ascribed {tm; asc; eff_opt} ->
    write_tag w 11; ser_term w tm; ser_ascription w asc; ser w eff_opt
  | Tm_let {lbs; body} -> write_tag w 12; ser_letbindings w lbs; ser_term w body
  | Tm_meta {tm; meta} -> write_tag w 13; ser_term w tm; ser_metadata w meta
  | Tm_quoted (tm, qi) ->
    write_tag w 14;
    ser_term w tm;
    write_tag w (match qi.qkind with Quote_static -> 0 | Quote_dynamic -> 1);
    ser w (fst qi.antiquotations);
    ser_list ser_term w (snd qi.antiquotations)
  | Tm_unknown -> write_tag w 15
  | Tm_uvar _ -> unexpected "a unification variable"
  | Tm_delayed _ -> unexpected "a delayed substitution"
  | Tm_lazy _ -> unexpected "a lazy term"

and ser_bv (w:writer) (x:bv) : ML unit =
  write_shared #bv #deq_bv #hashable_bv bv_slot w x ser_bv_node

and ser_bv_node (w:writer) (x:bv) : ML unit =
  ser w x.ppname; ser w x.index; ser_term w x.sort

and ser_fv (w:writer) (fv:fv) : ML unit =
  ser w fv.fv_name; ser_option ser_fv_qual w fv.fv_qual

and ser_fv_qual (w:writer) (q:fv_qual) : ML unit =
  match q with
  | Data_ctor -> write_tag w 0
  | Record_projector (l, i) -> write_tag w 1; ser w l; ser w i
  | Record_ctor (l, is) -> write_tag w 2; ser w l; ser w is
  | Unresolved_projector fv -> write_tag w 3; ser_option ser_fv w fv
  | Unresolved_constructor uc ->
    write_tag w 4; ser w uc.uc_base_term; ser w uc.uc_typename; ser w uc.uc_fields
  | Unresolved_name fvs -> write_tag w 5; ser_list ser_fv w fvs

and ser_binder (w:writer) (b:binder) : ML unit =
  ser_bv w b.binder_bv;
  ser_option ser_binder_qualifier w b.binder_qual;
  ser_option ser_positivity w b.binder_positivity;
  ser_list ser_term w b.binder_attrs

and ser_binder_qualifier (w:writer) (q:binder_qualifier) : ML unit =
  match q with
  | Implicit b -> write_tag w 0; ser w b
  | Meta t -> write_tag w 1; ser_term w t
  | Equality -> write_tag w 2

and ser_positivity (w:writer) (q:positivity_qualifier) : ML unit =
  match q with
  | BinderStrictlyPositive -> write_tag w 0
  | BinderUnused -> write_tag w 1

and ser_arg (w:writer) (a:arg) : ML unit =
  ser_term w (fst a);
  ser_option ser_arg_qualifier w (snd a)

and ser_arg_qualifier (w:writer) (q:arg_qualifier) : ML unit =
  ser w q.aqual_implicit;
  ser_list ser_term w q.aqual_attributes

and ser_comp (w:writer) (c:comp) : ML unit =
  ser w c.pos;
  match c.n with
  | Comp ct ->
    ser w ct.effect_name;
    ser_term w ct.result_typ;
    ser_list ser_cflag w ct.flags;
    ser w ct.source_effect_name

and ser_cflag (w:writer) (f:cflag) : ML unit =
  match f with
  | SMTPAT t -> write_tag w 0; ser_term w t
  | DECREASES (Decreases_lex ts) -> write_tag w 1; ser_list ser_term w ts
  | DECREASES (Decreases_wf (rel, e)) -> write_tag w 2; ser_term w rel; ser_term w e

and ser_residual_comp (w:writer) (rc:residual_comp) : ML unit =
  ser w rc.residual_effect;
  ser_option ser_term w rc.residual_typ;
  ser_list ser_cflag w rc.residual_flags

and ser_ascription (w:writer) (a:ascription) : ML unit =
  let (tc, tac, eq) = a in
  (match tc with
   | Inl t -> write_tag w 0; ser_term w t
   | Inr c -> write_tag w 1; ser_comp w c);
  ser_option ser_term w tac;
  ser w eq

and ser_match_returns (w:writer) (m:match_returns_ascription) : ML unit =
  ser_binder w (fst m);
  ser_ascription w (snd m)

and ser_branch (w:writer) (b:branch) : ML unit =
  let (p, wopt, e) = b in
  ser_pat w p;
  ser_option ser_term w wopt;
  ser_term w e

and ser_pat (w:writer) (p:pat) : ML unit =
  ser w p.p;
  match p.v with
  | Pat_constant c -> write_tag w 0; ser_const w c
  | Pat_cons (fv, us, ps) ->
    write_tag w 1; ser_fv w fv; ser_option ser_univs w us; ser_list ser_subpat w ps
  | Pat_var x -> write_tag w 2; ser_bv w x
  | Pat_dot_term t -> write_tag w 3; ser_option ser_term w t

and ser_subpat (w:writer) (p:pat & bool) : ML unit =
  ser_pat w (fst p);
  ser w (snd p)

and ser_letbindings (w:writer) (lbs:letbindings) : ML unit =
  ser w (fst lbs);
  ser_list ser_letbinding w (snd lbs)

and ser_letbinding (w:writer) (lb:letbinding) : ML unit =
  (match lb.lbname with
   | Inl x -> write_tag w 0; ser_bv w x
   | Inr fv -> write_tag w 1; ser_fv w fv);
  ser w lb.lbunivs;
  ser_term w lb.lbtyp;
  ser w lb.lbeff;
  ser_term w lb.lbdef;
  ser_list ser_term w lb.lbattrs;
  ser w lb.lbpos

and ser_metadata (w:writer) (m:metadata) : ML unit =
  match m with
  | Meta_pattern (ns, pats) ->
    write_tag w 0; ser_list ser_term w ns; ser_list ser_args w pats
  | Meta_named l -> write_tag w 1; ser w l
  | Meta_labeled (docs, r, b) ->
    write_tag w 2; ser_list ser_doc w docs; ser w r; ser w b
  | Meta_desugared i -> write_tag w 3; ser_meta_source_info w i
  | Meta_monadic (m, t) -> write_tag w 4; ser w m; ser_term w t
  | Meta_monadic_lift (m1, m2, t) -> write_tag w 5; ser w m1; ser w m2; ser_term w t

and ser_args (w:writer) (args:args) : ML unit =
  ser_list ser_arg w args

let rec deser_term (r:reader) : ML term =
  read_shared #term term_slot r deser_term_node

and deser_term_node (r:reader) : ML term =
  let pos : range = deser r in
  let t' : term' =
    match read_tag r with
    | 0 -> Tm_bvar (deser_bv r)
    | 1 -> Tm_name (deser_bv r)
    | 2 -> Tm_fvar (deser_fv r)
    | 3 ->
      let t = deser_term r in
      let us = deser_univs r in
      Tm_uinst (t, us)
    | 4 -> Tm_constant (deser_const r)
    | 5 -> Tm_type (deser_univ r)
    | 6 ->
      let b = deser_binder r in
      let body = deser_term r in
      let rc_opt = deser_option deser_residual_comp r in
      Tm_abs {b; body; rc_opt}
    | 7 ->
      let b = deser_binder r in
      let comp = deser_comp r in
      Tm_arrow {b; comp}
    | 8 ->
      let b = deser_bv r in
      let phi = deser_term r in
      Tm_refine {b; phi}
    | 9 ->
      let hd = deser_term r in
      let arg = deser_arg r in
      Tm_app {hd; arg}
    | 10 ->
      let scrutinee = deser_term r in
      let ret_opt = deser_option deser_match_returns r in
      let brs = deser_list deser_branch r in
      let rc_opt = deser_option deser_residual_comp r in
      Tm_match {scrutinee; ret_opt; brs; rc_opt}
    | 11 ->
      let tm = deser_term r in
      let asc = deser_ascription r in
      let eff_opt : option lident = deser r in
      Tm_ascribed {tm; asc; eff_opt}
    | 12 ->
      let lbs = deser_letbindings r in
      let body = deser_term r in
      Tm_let {lbs; body}
    | 13 ->
      let tm = deser_term r in
      let meta = deser_metadata r in
      Tm_meta {tm; meta}
    | 14 ->
      let tm = deser_term r in
      let qkind =
        match read_tag r with
        | 0 -> Quote_static
        | 1 -> Quote_dynamic
        | t -> bad_tag "quote_kind" t in
      let shift : int = deser r in
      let aqs = deser_list deser_term r in
      Tm_quoted (tm, {qkind; antiquotations = (shift, aqs)})
    | 15 -> Tm_unknown
    | t -> bad_tag "term" t
  in
  mk t' pos

and deser_bv (r:reader) : ML bv =
  read_shared #bv bv_slot r deser_bv_node

and deser_bv_node (r:reader) : ML bv =
  let ppname : ident = deser r in
  let index : int = deser r in
  let sort = deser_term r in
  {ppname; index; sort}

and deser_fv (r:reader) : ML fv =
  let fv_name : lident = deser r in
  let fv_qual = deser_option deser_fv_qual r in
  {fv_name; fv_qual}

and deser_fv_qual (r:reader) : ML fv_qual =
  match read_tag r with
  | 0 -> Data_ctor
  | 1 ->
    let l : lident = deser r in
    let i : ident = deser r in
    Record_projector (l, i)
  | 2 ->
    let l : lident = deser r in
    let is : list ident = deser r in
    Record_ctor (l, is)
  | 3 -> Unresolved_projector (deser_option deser_fv r)
  | 4 ->
    let uc_base_term : bool = deser r in
    let uc_typename : option lident = deser r in
    let uc_fields : list lident = deser r in
    Unresolved_constructor {uc_base_term; uc_typename; uc_fields}
  | 5 -> Unresolved_name (deser_list deser_fv r)
  | t -> bad_tag "fv_qual" t

and deser_binder (r:reader) : ML binder =
  let binder_bv = deser_bv r in
  let binder_qual = deser_option deser_binder_qualifier r in
  let binder_positivity = deser_option deser_positivity r in
  let binder_attrs = deser_list deser_term r in
  {binder_bv; binder_qual; binder_positivity; binder_attrs}

and deser_binder_qualifier (r:reader) : ML binder_qualifier =
  match read_tag r with
  | 0 -> Implicit (deser r)
  | 1 -> Meta (deser_term r)
  | 2 -> Equality
  | t -> bad_tag "binder_qualifier" t

and deser_positivity (r:reader) : ML positivity_qualifier =
  match read_tag r with
  | 0 -> BinderStrictlyPositive
  | 1 -> BinderUnused
  | t -> bad_tag "positivity_qualifier" t

and deser_arg (r:reader) : ML arg =
  let t = deser_term r in
  let q = deser_option deser_arg_qualifier r in
  (t, q)

and deser_arg_qualifier (r:reader) : ML arg_qualifier =
  let aqual_implicit : bool = deser r in
  let aqual_attributes = deser_list deser_term r in
  {aqual_implicit; aqual_attributes}

and deser_comp (r:reader) : ML comp =
  let pos : range = deser r in
  let effect_name : lident = deser r in
  let result_typ = deser_term r in
  let flags = deser_list deser_cflag r in
  let source_effect_name : lident = deser r in
  mk_comp' (Comp {effect_name; result_typ; flags; source_effect_name}) pos

and deser_cflag (r:reader) : ML cflag =
  match read_tag r with
  | 0 -> SMTPAT (deser_term r)
  | 1 -> DECREASES (Decreases_lex (deser_list deser_term r))
  | 2 ->
    let rel = deser_term r in
    let e = deser_term r in
    DECREASES (Decreases_wf (rel, e))
  | t -> bad_tag "cflag" t

and deser_residual_comp (r:reader) : ML residual_comp =
  let residual_effect : lident = deser r in
  let residual_typ = deser_option deser_term r in
  let residual_flags = deser_list deser_cflag r in
  {residual_effect; residual_typ; residual_flags}

and deser_ascription (r:reader) : ML ascription =
  let tc =
    match read_tag r with
    | 0 -> Inl (deser_term r)
    | 1 -> Inr (deser_comp r)
    | t -> bad_tag "ascription" t in
  let tac = deser_option deser_term r in
  let eq : bool = deser r in
  (tc, tac, eq)

and deser_match_returns (r:reader) : ML match_returns_ascription =
  let b = deser_binder r in
  let asc = deser_ascription r in
  (b, asc)

and deser_branch (r:reader) : ML branch =
  let p = deser_pat r in
  let wopt = deser_option deser_term r in
  let e = deser_term r in
  (p, wopt, e)

and deser_pat (r:reader) : ML pat =
  let pos : range = deser r in
  let v =
    match read_tag r with
    | 0 -> Pat_constant (deser_const r)
    | 1 ->
      let fv = deser_fv r in
      let us = deser_option deser_univs r in
      let ps = deser_list deser_subpat r in
      Pat_cons (fv, us, ps)
    | 2 -> Pat_var (deser_bv r)
    | 3 -> Pat_dot_term (deser_option deser_term r)
    | t -> bad_tag "pat" t in
  withinfo v pos

and deser_subpat (r:reader) : ML (pat & bool) =
  let p = deser_pat r in
  let b : bool = deser r in
  (p, b)

and deser_letbindings (r:reader) : ML letbindings =
  let is_rec : bool = deser r in
  let lbs = deser_list deser_letbinding r in
  (is_rec, lbs)

and deser_letbinding (r:reader) : ML letbinding =
  let lbname : lbname =
    match read_tag r with
    | 0 -> Inl (deser_bv r)
    | 1 -> Inr (deser_fv r)
    | t -> bad_tag "lbname" t in
  let lbunivs : list univ_name = deser r in
  let lbtyp = deser_term r in
  let lbeff : lident = deser r in
  let lbdef = deser_term r in
  let lbattrs = deser_list deser_term r in
  let lbpos : range = deser r in
  {lbname; lbunivs; lbtyp; lbeff; lbdef; lbattrs; lbpos}

and deser_metadata (r:reader) : ML metadata =
  match read_tag r with
  | 0 ->
    let ns = deser_list deser_term r in
    let pats = deser_list deser_args r in
    Meta_pattern (ns, pats)
  | 1 -> Meta_named (deser r)
  | 2 ->
    let docs = deser_list deser_doc r in
    let rng : range = deser r in
    let b : bool = deser r in
    Meta_labeled (docs, rng, b)
  | 3 -> Meta_desugared (deser_meta_source_info r)
  | 4 ->
    let m : lident = deser r in
    let t = deser_term r in
    Meta_monadic (m, t)
  | 5 ->
    let m1 : lident = deser r in
    let m2 : lident = deser r in
    let t = deser_term r in
    Meta_monadic_lift (m1, m2, t)
  | t -> bad_tag "metadata" t

and deser_args (r:reader) : ML args =
  deser_list deser_arg r

instance serializable_term : serializable term = {
  ser = ser_term;
  deser = deser_term;
}

let serializable_binder : serializable binder = { ser = ser_binder; deser = deser_binder }
let serializable_cflag : serializable cflag = { ser = ser_cflag; deser = deser_cflag }
let serializable_letbindings : serializable letbindings =
  { ser = ser_letbindings; deser = deser_letbindings }

(* Signatures *)

instance serializable_qualifier : serializable qualifier = {
  ser = (fun w q ->
    match q with
    | Assumption -> write_tag w 0
    | New -> write_tag w 1
    | Private -> write_tag w 2
    | Unfold_for_unification_and_vcgen -> write_tag w 3
    | Irreducible -> write_tag w 4
    | Inline_for_extraction -> write_tag w 5
    | NoExtract -> write_tag w 6
    | Noeq -> write_tag w 7
    | Unopteq -> write_tag w 8
    | TotalEffect -> write_tag w 9
    | Logic -> write_tag w 10
    | Reifiable -> write_tag w 11
    | Reflectable l -> write_tag w 12; ser w l
    | Visible_default -> write_tag w 13
    | Discriminator l -> write_tag w 14; ser w l
    | Projector (l, i) -> write_tag w 15; ser w l; ser w i
    | RecordType (ns, fs) -> write_tag w 16; ser w ns; ser w fs
    | RecordConstructor (ns, fs) -> write_tag w 17; ser w ns; ser w fs
    | Action l -> write_tag w 18; ser w l
    | ExceptionConstructor -> write_tag w 19
    | HasMaskedEffect -> write_tag w 20
    | FStarC.Syntax.Syntax.Effect -> write_tag w 21
    | OnlyName -> write_tag w 22
    | InternalAssumption -> write_tag w 23);
  deser = (fun r ->
    match read_tag r with
    | 0 -> Assumption
    | 1 -> New
    | 2 -> Private
    | 3 -> Unfold_for_unification_and_vcgen
    | 4 -> Irreducible
    | 5 -> Inline_for_extraction
    | 6 -> NoExtract
    | 7 -> Noeq
    | 8 -> Unopteq
    | 9 -> TotalEffect
    | 10 -> Logic
    | 11 -> Reifiable
    | 12 -> Reflectable (deser r)
    | 13 -> Visible_default
    | 14 -> Discriminator (deser r)
    | 15 ->
      let l : lident = deser r in
      let i : ident = deser r in
      Projector (l, i)
    | 16 ->
      let ns : list ident = deser r in
      let fs : list ident = deser r in
      RecordType (ns, fs)
    | 17 ->
      let ns : list ident = deser r in
      let fs : list ident = deser r in
      RecordConstructor (ns, fs)
    | 18 -> Action (deser r)
    | 19 -> ExceptionConstructor
    | 20 -> HasMaskedEffect
    | 21 -> FStarC.Syntax.Syntax.Effect
    | 22 -> OnlyName
    | 23 -> InternalAssumption
    | t -> bad_tag "qualifier" t);
}

let serializable_pragma : serializable pragma = {
  ser = (fun w p ->
    match p with
    | ShowOptions -> write_tag w 0
    | SetOptions s -> write_tag w 1; ser w s
    | ResetOptions s -> write_tag w 2; ser w s
    | PushOptions s -> write_tag w 3; ser w s
    | PopOptions -> write_tag w 4
    | RestartSolver -> write_tag w 5
    | PrintEffectsGraph -> write_tag w 6
    | Check t -> write_tag w 7; ser w t
    | Eval t -> write_tag w 8; ser w t);
  deser = (fun r ->
    match read_tag r with
    | 0 -> ShowOptions
    | 1 -> SetOptions (deser r)
    | 2 -> ResetOptions (deser r)
    | 3 -> PushOptions (deser r)
    | 4 -> PopOptions
    | 5 -> RestartSolver
    | 6 -> PrintEffectsGraph
    | 7 -> Check (deser r)
    | 8 -> Eval (deser r)
    | t -> bad_tag "pragma" t);
}

let serializable_tscheme : serializable tscheme =
  serializable_tuple2 (serializable_list serializable_ident) serializable_term

let serializable_eff_decl : serializable eff_decl = {
  ser = (fun w ed ->
    ser w ed.mname;
    ser #_ #(serializable_list serializable_cflag) w ed.cattributes;
    ser_option (fun w (c:eff_combinators) ->
      ser w c.repr; ser w c.return_repr; ser w c.bind_repr; ser w c.repr_universe)
      w ed.combinators;
    ser w ed.eff_attrs;
    match ed.extraction_mode with
    | Extract_none s -> write_tag w 0; ser w s
    | Extract_reify -> write_tag w 1
    | Extract_primitive -> write_tag w 2);
  deser = (fun r ->
    let mname : lident = deser r in
    let cattributes : list cflag = deser #_ #(serializable_list serializable_cflag) r in
    let combinators = deser_option (fun r ->
      let repr : tscheme = deser r in
      let return_repr : tscheme = deser r in
      let bind_repr : tscheme = deser r in
      let repr_universe : tscheme = deser r in
      {repr; return_repr; bind_repr; repr_universe}) r in
    let eff_attrs : list term = deser r in
    let extraction_mode =
      match read_tag r with
      | 0 -> Extract_none (deser r)
      | 1 -> Extract_reify
      | 2 -> Extract_primitive
      | t -> bad_tag "eff_extraction_mode" t in
    {mname; cattributes; combinators; eff_attrs; extraction_mode});
}

let serializable_sub_eff : serializable sub_eff = {
  ser = (fun w se -> ser w se.source; ser w se.target; ser w se.lift);
  deser = (fun r ->
    let source : lident = deser r in
    let target : lident = deser r in
    let lift : option tscheme = deser r in
    {source; target; lift});
}

let serializable_sig_metadata : serializable sig_metadata = {
  ser = (fun w m ->
    ser w m.sigmeta_active;
    ser w m.sigmeta_fact_db_ids;
    ser w m.sigmeta_admit;
    ser w m.sigmeta_spliced;
    ser w m.sigmeta_already_checked;
    ser w m.sigmeta_extension_decl;
    ser w m.sigmeta_extension_data;
    ser w m.sigmeta_type_constructor);
  deser = (fun r ->
    let sigmeta_active : bool = deser r in
    let sigmeta_fact_db_ids : list string = deser r in
    let sigmeta_admit : bool = deser r in
    let sigmeta_spliced : bool = deser r in
    let sigmeta_already_checked : bool = deser r in
    let sigmeta_extension_decl : bool = deser r in
    let sigmeta_extension_data : list (string & term) = deser r in
    let sigmeta_type_constructor : bool = deser r in
    {sigmeta_active; sigmeta_fact_db_ids; sigmeta_admit; sigmeta_spliced;
     sigmeta_already_checked; sigmeta_extension_decl; sigmeta_extension_data;
     sigmeta_type_constructor});
}

instance serializable_open_kind : serializable open_kind = {
  ser = (fun w k -> write_tag w (match k with Open_module -> 0 | Open_namespace -> 1));
  deser = (fun r ->
    match read_tag r with
    | 0 -> Open_module
    | 1 -> Open_namespace
    | t -> bad_tag "open_kind" t);
}

instance serializable_restriction : serializable restriction = {
  ser = (fun w x ->
    match x with
    | Unrestricted -> write_tag w 0
    | AllowList l -> write_tag w 1; ser w l);
  deser = (fun r ->
    match read_tag r with
    | 0 -> Unrestricted
    | 1 -> AllowList (deser r)
    | t -> bad_tag "restriction" t);
}

let serializable_vconfig : serializable FStar.VConfig.vconfig = {
  ser = (fun w (c:FStar.VConfig.vconfig) ->
    ser w c.initial_fuel;
    ser w c.max_fuel;
    ser w c.initial_ifuel;
    ser w c.max_ifuel;
    ser w c.no_smt;
    ser w c.quake_lo;
    ser w c.quake_hi;
    ser w c.quake_keep;
    ser w c.retry;
    ser w c.smtencoding_elim_box;
    ser w c.smtencoding_nl_arith_repr;
    ser w c.smtencoding_l_arith_repr;
    ser w c.tcnorm;
    ser w c.no_plugins;
    ser w c.no_tactics;
    ser w c.z3cliopt;
    ser w c.z3smtopt;
    ser w c.z3refresh;
    ser w c.z3rlimit;
    ser w c.z3rlimit_factor;
    ser w c.z3seed;
    ser w c.z3version;
    ser w c.trivial_pre_for_unannotated_effectful_fns);
  deser = (fun r ->
    let initial_fuel : int = deser r in
    let max_fuel : int = deser r in
    let initial_ifuel : int = deser r in
    let max_ifuel : int = deser r in
    let no_smt : bool = deser r in
    let quake_lo : int = deser r in
    let quake_hi : int = deser r in
    let quake_keep : bool = deser r in
    let retry : bool = deser r in
    let smtencoding_elim_box : bool = deser r in
    let smtencoding_nl_arith_repr : string = deser r in
    let smtencoding_l_arith_repr : string = deser r in
    let tcnorm : bool = deser r in
    let no_plugins : bool = deser r in
    let no_tactics : bool = deser r in
    let z3cliopt : list string = deser r in
    let z3smtopt : list string = deser r in
    let z3refresh : bool = deser r in
    let z3rlimit : int = deser r in
    let z3rlimit_factor : int = deser r in
    let z3seed : int = deser r in
    let z3version : string = deser r in
    let trivial_pre_for_unannotated_effectful_fns : bool = deser r in
    { FStar.VConfig.initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt;
      quake_lo; quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm; no_plugins;
      no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit; z3rlimit_factor;
      z3seed; z3version; trivial_pre_for_unannotated_effectful_fns });
}

let rec ser_sigelt (w:writer) (se:sigelt) : ML unit =
  (match se.sigel with
   | Sig_inductive_typ {lid; us; params; num_uniform_params; t; mutuals; ds; injective_type_params} ->
     write_tag w 0;
     ser w lid; ser w us;
     ser #_ #(serializable_list serializable_binder) w params;
     ser w num_uniform_params; ser w t; ser w mutuals; ser w ds;
     ser w injective_type_params
   | Sig_bundle {ses; lids} ->
     write_tag w 1; ser_list ser_sigelt w ses; ser w lids
   | Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals; injective_type_params; proj_disc_lids} ->
     write_tag w 2;
     ser w lid; ser w us; ser w t; ser w ty_lid; ser w num_ty_params;
     ser w mutuals; ser w injective_type_params; ser w proj_disc_lids
   | Sig_declare_typ {lid; us; t} ->
     write_tag w 3; ser w lid; ser w us; ser w t
   | Sig_let {lbs; lids} ->
     write_tag w 4; ser #_ #serializable_letbindings w lbs; ser w lids
   | Sig_assume {lid; us; phi} ->
     write_tag w 5; ser w lid; ser w us; ser w phi
   | Sig_new_effect ed -> write_tag w 6; ser #_ #serializable_eff_decl w ed
   | Sig_sub_effect se -> write_tag w 7; ser #_ #serializable_sub_eff w se
   | Sig_effect_abbrev {lid; root} -> write_tag w 8; ser w lid; ser w root
   | Sig_pragma p -> write_tag w 9; ser #_ #serializable_pragma w p
   | Sig_splice {is_typed; lids; tac} ->
     write_tag w 10; ser w is_typed; ser w lids; ser w tac
   | Sig_fail {errs; rng; fail_in_lax; ses} ->
     write_tag w 11; ser w errs; ser w rng; ser w fail_in_lax; ser_list ser_sigelt w ses);
  ser w se.sigrng;
  ser w se.sigquals;
  ser #_ #serializable_sig_metadata w se.sigmeta;
  ser w se.sigattrs;
  ser #_ #(serializable_list (serializable_either
            (serializable_tuple3 serializable_lident serializable_open_kind serializable_restriction)
            (serializable_tuple2 serializable_ident serializable_lident)))
    w se.sigopens_and_abbrevs;
  ser #_ #(serializable_option serializable_vconfig) w se.sigopts

let rec deser_sigelt (r:reader) : ML sigelt =
  let sigel =
    match read_tag r with
    | 0 ->
      let lid : lident = deser r in
      let us : univ_names = deser r in
      let params : binders = deser #_ #(serializable_list serializable_binder) r in
      let num_uniform_params : option int = deser r in
      let t : typ = deser r in
      let mutuals : list lident = deser r in
      let ds : list lident = deser r in
      let injective_type_params : bool = deser r in
      Sig_inductive_typ {lid; us; params; num_uniform_params; t; mutuals; ds; injective_type_params}
    | 1 ->
      let ses = deser_list deser_sigelt r in
      let lids : list lident = deser r in
      Sig_bundle {ses; lids}
    | 2 ->
      let lid : lident = deser r in
      let us : univ_names = deser r in
      let t : typ = deser r in
      let ty_lid : lident = deser r in
      let num_ty_params : int = deser r in
      let mutuals : list lident = deser r in
      let injective_type_params : bool = deser r in
      let proj_disc_lids : list lident = deser r in
      Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals; injective_type_params; proj_disc_lids}
    | 3 ->
      let lid : lident = deser r in
      let us : univ_names = deser r in
      let t : typ = deser r in
      Sig_declare_typ {lid; us; t}
    | 4 ->
      let lbs = deser #_ #serializable_letbindings r in
      let lids : list lident = deser r in
      Sig_let {lbs; lids}
    | 5 ->
      let lid : lident = deser r in
      let us : univ_names = deser r in
      let phi : term = deser r in
      Sig_assume {lid; us; phi}
    | 6 -> Sig_new_effect (deser #_ #serializable_eff_decl r)
    | 7 -> Sig_sub_effect (deser #_ #serializable_sub_eff r)
    | 8 ->
      let lid : lident = deser r in
      let root : lident = deser r in
      Sig_effect_abbrev {lid; root}
    | 9 -> Sig_pragma (deser #_ #serializable_pragma r)
    | 10 ->
      let is_typed : bool = deser r in
      let lids : list lident = deser r in
      let tac : term = deser r in
      Sig_splice {is_typed; lids; tac}
    | 11 ->
      let errs : list int = deser r in
      let rng : range = deser r in
      let fail_in_lax : bool = deser r in
      let ses = deser_list deser_sigelt r in
      Sig_fail {errs; rng; fail_in_lax; ses}
    | t -> bad_tag "sigelt" t
  in
  let sigrng : range = deser r in
  let sigquals : list qualifier = deser r in
  let sigmeta = deser #_ #serializable_sig_metadata r in
  let sigattrs : list attribute = deser r in
  let sigopens_and_abbrevs =
    deser #_ #(serializable_list (serializable_either
                (serializable_tuple3 serializable_lident serializable_open_kind serializable_restriction)
                (serializable_tuple2 serializable_ident serializable_lident))) r in
  let sigopts = deser #_ #(serializable_option serializable_vconfig) r in
  {sigel; sigrng; sigquals; sigmeta; sigattrs; sigopens_and_abbrevs; sigopts}

instance serializable_sigelt : serializable sigelt = {
  ser = ser_sigelt;
  deser = deser_sigelt;
}

instance serializable_modul : serializable modul = {
  ser = (fun w m -> ser w m.name; ser w m.declarations; ser w m.is_interface);
  deser = (fun r ->
    let name : lident = deser r in
    let declarations : list sigelt = deser r in
    let is_interface : bool = deser r in
    {name; declarations; is_interface});
}
