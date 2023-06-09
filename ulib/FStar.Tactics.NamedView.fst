(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Tactics.NamedView

(* inner let bindings not encoded, OK *)
#set-options "--warn_error -242"

(* This file is part of the tactics core, we open only what's needed. *)
open FStar.Tactics.Effect
open FStar.Tactics.Util
open FStar.Tactics.V2.Builtins

exception LengthMismatch
exception NotEnoughBinders

(* We work with reflection V2. *)
open FStar.Reflection.V2
module R = FStar.Reflection.V2
module RD = FStar.Reflection.V2.Data

(* Disable printing, but mark private so we don't mess
with clients. *)
private
let print (s:string) : Tac unit = ()

(* Re export the syntax types. Expose variables as their views, users do
not need to pack/inspect these if they are using the named view. *)
let namedv   = R.namedv_view
let bv       = R.bv_view
let comp     = R.comp_view
let binding  = R.binding (* already good *)
(* Terms and universes are still *deep*, so we do not change their
representation, and the user needs to pack/inspect. *)
let term     = R.term
let universe = R.universe

[@@plugin]
noeq
type binder = {
  uniq   : nat;

  ppname : ppname_t;
  sort   : typ;
  qual   : aqualv;
  attrs  : list term;
}
type binders = list binder

let is_simple_binder (b:binder) = Q_Explicit? b.qual /\ Nil? b.attrs
type simple_binder = b:binder{is_simple_binder b}

[@@plugin]
noeq
type pattern =
 // A built-in constant
 | Pat_Constant {
     c : vconst
   }

 // A fully applied constructor, each boolean marks whether the
 // argument was an explicitly-provided implicit argument
 | Pat_Cons {
     head    : fv;
     univs   : option universes;
     subpats : list (pattern * bool)
   }

 // A pattern-bound *named* variable.
 | Pat_Var {
     v    : namedv;
     sort : sealed typ;
   }

 // Dot pattern: resolved by other elements in the pattern and type
 | Pat_Dot_Term {
     t : option term;
   }

type branch = pattern & term
type match_returns_ascription = binder & (either term comp & option term & bool)

[@@plugin]
noeq
type named_term_view =
  | Tv_Var    : v:namedv -> named_term_view
  | Tv_BVar   : v:bv -> named_term_view
  | Tv_FVar   : v:fv -> named_term_view
  | Tv_UInst  : v:fv -> us:universes -> named_term_view
  | Tv_App    : hd:term -> a:argv -> named_term_view
  | Tv_Abs    : bv:binder -> body:term -> named_term_view
  | Tv_Arrow  : bv:binder -> c:comp -> named_term_view
  | Tv_Type   : universe -> named_term_view
  | Tv_Refine : b:simple_binder -> ref:term -> named_term_view
  | Tv_Const  : vconst -> named_term_view
  | Tv_Uvar   : nat -> ctx_uvar_and_subst -> named_term_view
  | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_binder -> def:term -> body:term -> named_term_view
  | Tv_Match  : scrutinee:term -> ret:option match_returns_ascription -> brs:(list branch) -> named_term_view
  | Tv_AscribedT : e:term -> t:term -> tac:option term -> use_eq:bool -> named_term_view
  | Tv_AscribedC : e:term -> c:comp -> tac:option term -> use_eq:bool -> named_term_view
  | Tv_Unknown  : named_term_view // An underscore: _
  | Tv_Unsupp : named_term_view // failed to inspect, not supported

private
let __binding_to_binder (bnd : binding) (b : R.binder) : binder =
  {
      ppname = bnd.ppname;
      uniq   = bnd.uniq;
      sort   = bnd.sort;
      qual   = (inspect_binder b).qual;
      attrs  = (inspect_binder b).attrs;
  }

let binding_to_binder (bnd : binding) : binder =
  {
      ppname = bnd.ppname;
      uniq   = bnd.uniq;
      sort   = bnd.sort;
      qual   = Q_Explicit;
      attrs  = []
  }

let binder_to_binding (b : binder) : binding =
  {
      ppname = b.ppname;
      uniq   = b.uniq;
      sort   = b.sort;
  }

private
let r_binder_to_namedv (b : binder) : R.namedv =
  pack_namedv {
    uniq   = b.uniq;
    sort   = seal b.sort;
    ppname = b.ppname;
  }

let namedv_to_binder (v : namedv) (sort : term) : binder =
  {
    uniq   = v.uniq;
    sort   = sort;
    ppname = v.ppname;
    qual   = Q_Explicit;
    attrs  = [];
  }

(* Bindings and simple_binders are the same *)
let binding_to_simple_binder (b:binding) : simple_binder = {
  uniq   = b.uniq;
  sort   = b.sort;
  ppname = b.ppname;
  qual   = Q_Explicit;
  attrs  = [];
}
let simple_binder_to_binding (b:simple_binder) : binding = {
  uniq   = b.uniq;
  sort   = b.sort;
  ppname = b.ppname;
}

private
let open_binder (b : R.binder) : Tac binder =
  let n = fresh () in
  let bv = inspect_binder b in
  {
    uniq   = n;
    sort   = bv.sort;
    ppname = bv.ppname;
    qual   = bv.qual;
    attrs  = bv.attrs;
  }

private
let close_binder (b : binder) : R.binder =
  pack_binder {
    sort   = b.sort;
    qual   = b.qual;
    ppname = b.ppname;
    attrs  = b.attrs;
  }

private
let open_term_with (b : R.binder) (nb : binder) (t : term) : Tac term =
  let nv : R.namedv = pack_namedv {
    uniq   = nb.uniq;
    sort   = seal nb.sort;
    ppname = nb.ppname;
  }
  in
  let t' = subst_term [DB 0 nv] t in
  t'

private
let open_term (b : R.binder) (t : term) : Tac (binder & term) =
  let bndr : binder = open_binder b in
  (bndr, open_term_with b bndr t)

let subst_comp (s : subst_t) (c : comp) : comp =
  inspect_comp (R.subst_comp s (pack_comp c))

private
let open_comp (b : R.binder) (t : comp) : Tac (binder & comp) =
  let n = fresh () in
  let bv : binder_view = inspect_binder b in
  let nv : R.namedv = pack_namedv {
    uniq   = n;
    sort   = seal bv.sort;
    ppname = bv.ppname;
  }
  in
  let t' = subst_comp [DB 0 nv] t in
  let bndr : binder = {
    uniq   = n;
    sort   = bv.sort;
    ppname = bv.ppname;
    qual   = bv.qual;
    attrs  = bv.attrs;
  }
  in
  (bndr, t')

private
let open_comp_with (b : R.binder) (nb : binder) (c : comp) : Tac comp =
  let nv : R.namedv = pack_namedv {
    uniq   = nb.uniq;
    sort   = seal nb.sort;
    ppname = nb.ppname;
  }
  in
  let t' = subst_comp [DB 0 nv] c in
  t'

(* FIXME: unfortunate duplication here. The effect means this proof cannot
be done extrinsically. Can we add a refinement to the binder? *)
private
let open_term_simple (b : R.simple_binder) (t : term) : Tac (simple_binder & term) =
  let n = fresh () in
  let bv : binder_view = inspect_binder b in
  let nv : R.namedv = pack_namedv {
    uniq   = n;
    sort   = seal bv.sort;
    ppname = bv.ppname;
  }
  in
  let t' = subst_term [DB 0 nv] t in
  let bndr : binder = {
    uniq   = n;
    sort   = bv.sort;
    ppname = bv.ppname;
    qual   = bv.qual;
    attrs  = bv.attrs;
  }
  in
  (bndr, t')

private
let open_comp_simple (b : R.simple_binder) (t : comp) : Tac (simple_binder & comp) =
  let n = fresh () in
  let bv : binder_view = inspect_binder b in
  let nv : R.namedv = pack_namedv {
    uniq   = n;
    sort   = seal bv.sort;
    ppname = bv.ppname;
  }
  in
  let t' = subst_comp [DB 0 nv] t in
  let bndr : binder = {
    uniq   = n;
    sort   = bv.sort;
    ppname = bv.ppname;
    qual   = bv.qual;
    attrs  = bv.attrs;
  }
  in
  (bndr, t')

(* This two are in Tot *)
private
let close_term (b:binder) (t:term) : R.binder & term =
  let nv = r_binder_to_namedv b in
  let t' = subst_term [NM nv 0] t in
  let b = pack_binder { sort = b.sort; ppname = b.ppname; qual = b.qual; attrs = b.attrs } in
  (b, t')
private
let close_comp (b:binder) (t:comp) : R.binder & comp =
  let nv = r_binder_to_namedv b in
  let t' = subst_comp [NM nv 0] t in
  let b = pack_binder { sort = b.sort; ppname = b.ppname; qual = b.qual; attrs = b.attrs } in
  (b, t')

private
let close_term_simple (b:simple_binder) (t:term) : R.simple_binder & term =
  let nv = r_binder_to_namedv b in
  let t' = subst_term [NM nv 0] t in
  let bv : binder_view = { sort = b.sort; ppname = b.ppname; qual = b.qual; attrs = b.attrs } in
  let b = pack_binder bv in
  inspect_pack_binder bv;
  (b, t')
private
let close_comp_simple (b:simple_binder) (t:comp) : R.simple_binder & comp =
  let nv = r_binder_to_namedv b in
  let t' = subst_comp [NM nv 0] t in
  let bv : binder_view = { sort = b.sort; ppname = b.ppname; qual = b.qual; attrs = b.attrs } in
  let b = pack_binder bv in
  inspect_pack_binder bv;
  (b, t')

private
let r_subst_binder_sort (s : subst_t) (b : R.binder) : R.binder =
  let v = inspect_binder b in
  let v = { v with sort = subst_term s v.sort } in
  pack_binder v

let subst_binder_sort (s : subst_t) (b : binder) : binder =
  { b with sort = subst_term s b.sort }

(* Can't define this inside open_term_n. See #2955 *)
private
let rec __open_term_n_aux (bs : list R.binder) (nbs : list binder) (s : subst_t) : Tac (list binder & subst_t) =
  match bs with
  | [] -> nbs, s
  | b::bs ->
    let b = r_subst_binder_sort s b in
    let b = open_binder b in
    let nv = r_binder_to_namedv b in
    __open_term_n_aux bs (b::nbs) (DB 0 nv :: shift_subst 1 s)

private
let open_term_n (bs : list R.binder) (t : term) : Tac (list binder & term) =
  let nbs, s = __open_term_n_aux bs [] [] in
  List.Tot.rev nbs, subst_term s t

private
let rec open_term_n_with (bs : list R.binder) (nbs : list binder) (t : term) : Tac term =
  match bs, nbs with
  | [], [] -> t
  | b::bs, nb::nbs ->
    // FIXME: sorts
    let t' = open_term_n_with bs nbs t in
    let t'' = open_term_with b nb t' in
    t''
  | _ -> raise LengthMismatch

private
let close_term_n (bs : list binder) (t : term) : list R.binder & term =
  let rec aux (bs : list binder) (cbs : list R.binder) (s : subst_t) : list R.binder & subst_t =
    match bs with
    | [] -> cbs, s
    | b::bs ->
      let b = subst_binder_sort s b in
      let nv = r_binder_to_namedv b in
      let b = close_binder b in
      aux bs (b::cbs) (NM nv 0 :: shift_subst 1 s)
  in
  let cbs, s = aux bs [] [] in
  List.Tot.rev cbs, subst_term s t

private
let rec open_term_n_simple (bs : list R.simple_binder) (t : term) : Tac (list simple_binder & term) =
  match bs with
  | [] -> ([], t)
  | b::bs ->
    let bs', t' = open_term_n_simple bs t in
    let b', t'' = open_term_simple b t' in
    (b'::bs', t'')

private
let rec close_term_n_simple (bs : list simple_binder) (t : term) : list R.simple_binder & term =
  match bs with
  | [] -> ([], t)
  | b::bs ->
    let bs', t' = close_term_n_simple bs t in
    let b', t'' = close_term_simple b t' in
    (b'::bs', t'')

private
let open_univ_s (us : list univ_name) : Tac (list univ_name & subst_t) =
  let n = List.Tot.length us in
  let s = mapi (fun i u -> UN (n-1-i) (pack_universe (Uv_Name u))) us in
  us, s

private
let close_univ_s (us : list univ_name) : list univ_name & subst_t =
  let n = List.Tot.length us in
  let s = List.Tot.mapi (fun i u -> UD u (n-i-1)) us in
  us, s

private
let rec open_pat (p : R.pattern) (s : subst_t) : Tac (pattern & subst_t) =
  match p with
  | R.Pat_Constant c ->
    Pat_Constant {c=c}, s

  | R.Pat_Var ssort n ->
    let sort = unseal ssort in
    let sort = subst_term s sort in
    let nvv : namedv = {
      uniq = fresh();
      sort = seal sort;
      ppname = n;
    }
    in
    let nv = pack_namedv nvv in
    Pat_Var {v=nvv; sort=seal sort}, (DB 0 nv) :: shift_subst 1 s

  | R.Pat_Cons head univs subpats ->
    let subpats, s = fold_left (fun (pats,s) (pat,b) ->
                        let pat, s' = open_pat pat s in
                        ((pat,b)::pats, s'))
                       ([], s) subpats
    in
    let subpats = List.Tot.rev subpats in
    Pat_Cons {head=head; univs=univs; subpats=subpats}, s

  | R.Pat_Dot_Term None ->
    Pat_Dot_Term {t=None}, s

  | R.Pat_Dot_Term (Some t) ->
    let t = subst_term s t in
    Pat_Dot_Term {t=Some t}, s

private
let open_branch (b : R.branch) : Tac branch =
  let (pat, t) = b in
  let pat, s = open_pat pat [] in
  let t' = subst_term s t in
  (pat, t')

private
let rec close_pat (p : pattern) (s : subst_t) : Tot (R.pattern & subst_t) =
  match p with
  | Pat_Constant {c} ->
    R.Pat_Constant c, s

  | Pat_Var {v; sort} ->
    let nv = pack_namedv v in
    (* NOTE: we cannot do anything on the sort wihtout going
    into TAC. Need a sealed_bind. *)
    //let sort = unseal sort in
    //let sort = subst_term s sort in
    //let sort = seal sort in
    let s = (NM nv 0) :: shift_subst 1 s in
    R.Pat_Var sort v.ppname, s

  | Pat_Cons {head; univs; subpats} ->
    let subpats, s = List.Tot.fold_left (fun (pats,s) (pat,b) ->
                        assume(pat << p);
                        let pat, s' = close_pat pat s in
                        ((pat,b)::pats, s'))
                       ([], s) subpats
    in
    let subpats = List.Tot.rev subpats in
    R.Pat_Cons head univs subpats, s

  | Pat_Dot_Term {t=None} ->
    R.Pat_Dot_Term None, s

  | Pat_Dot_Term {t=Some t} ->
    let t = subst_term s t in
    R.Pat_Dot_Term (Some t), s

private
let close_branch (b : branch) : Tot R.branch =
  let (pat, t) = b in
  let pat, s = close_pat pat [] in
  let t' = subst_term s t in
  (pat, t')

private
let open_match_returns_ascription (mra : R.match_returns_ascription) : Tac match_returns_ascription =
  let (b, (ct, topt, use_eq)) = mra in
  let nb = open_binder b in
  let ct = match ct with
    | Inl t -> Inl (open_term_with b nb t)
    | Inr c ->
      let c = inspect_comp c in
      let c = open_comp_with b nb c in
      Inr c
  in
  let topt =
    match topt with
    | None -> None
    | Some t -> Some (open_term_with b nb t)
  in
  (nb, (ct, topt, use_eq))

private
let close_match_returns_ascription (mra : match_returns_ascription) : R.match_returns_ascription =
  let (nb, (ct, topt, use_eq)) = mra in
  let b = close_binder nb in
  // FIXME: all this is repeating the close_binder work, for no good reason
  let ct = match ct with
    | Inl t -> Inl (snd (close_term nb t))
    | Inr c ->
      let _, c = close_comp nb c in
      let c = pack_comp c in
      Inr c
  in
  let topt =
    match topt with
    | None -> None
    | Some t -> Some (snd (close_term nb t))
  in
  (b, (ct, topt, use_eq))

private
let open_view (tv:term_view) : Tac named_term_view =
  match tv with
  (* Nothing interesting *)
  | RD.Tv_Var v -> Tv_Var (inspect_namedv v)
  | RD.Tv_BVar v -> Tv_BVar (inspect_bv v)
  | RD.Tv_FVar v -> Tv_FVar v
  | RD.Tv_UInst v us -> Tv_UInst v us
  | RD.Tv_App hd a -> Tv_App hd a
  | RD.Tv_Type u -> Tv_Type u
  | RD.Tv_Const c -> Tv_Const c
  | RD.Tv_Uvar n ctx_uvar_and_subst -> Tv_Uvar n ctx_uvar_and_subst
  | RD.Tv_AscribedT e t tac use_eq -> Tv_AscribedT e t tac use_eq
  | RD.Tv_AscribedC e c tac use_eq -> Tv_AscribedC e (inspect_comp c) tac use_eq
  | RD.Tv_Unknown -> Tv_Unknown
  | RD.Tv_Unsupp -> Tv_Unsupp

  (* Below are the nodes that actually involve a binder.
  Open them and convert to named binders. *)

  | RD.Tv_Abs b body ->
    let nb, body = open_term b body in
    Tv_Abs nb body

  | RD.Tv_Arrow b c ->
    let nb, c = open_comp b (inspect_comp c) in
    Tv_Arrow nb c

  | RD.Tv_Refine b ref ->
    let nb, ref = open_term_simple b ref in
    Tv_Refine nb ref

  | RD.Tv_Let recf attrs b def body ->
    let nb, body = open_term_simple b body in
    let def =
      if recf
      then subst_term [DB 0 (r_binder_to_namedv nb)] def
      else def
    in
    Tv_Let recf attrs nb def body

  | RD.Tv_Match scrutinee ret brs ->
    let brs = map open_branch brs in
    let ret = map_opt open_match_returns_ascription ret in
    Tv_Match scrutinee ret brs

private
let close_view (tv : named_term_view) : Tot term_view =
  match tv with
  (* Nothing interesting *)
  | Tv_Var v -> RD.Tv_Var (pack_namedv v)
  | Tv_BVar v -> RD.Tv_BVar (pack_bv v)
  | Tv_FVar v -> RD.Tv_FVar v
  | Tv_UInst v us -> RD.Tv_UInst v us
  | Tv_App hd a -> RD.Tv_App hd a
  | Tv_Type u -> RD.Tv_Type u 
  | Tv_Const c -> RD.Tv_Const c
  | Tv_Uvar n ctx_uvar_and_subst -> RD.Tv_Uvar n ctx_uvar_and_subst
  | Tv_AscribedT e t tac use_eq -> RD.Tv_AscribedT e t tac use_eq
  | Tv_AscribedC e c tac use_eq -> RD.Tv_AscribedC e (pack_comp c) tac use_eq
  | Tv_Unknown -> RD.Tv_Unknown
  | Tv_Unsupp -> RD.Tv_Unsupp

  (* Below are the nodes that actually involve a binder.
  Open them and convert to named binders. *)

  | Tv_Abs nb body ->
    let b, body = close_term nb body in
    RD.Tv_Abs b body

  | Tv_Arrow nb c ->
    let b, c = close_comp nb c in
    let c = pack_comp c in
    RD.Tv_Arrow b c

  | Tv_Refine nb ref ->
    let b, ref = close_term_simple nb ref in
    RD.Tv_Refine b ref

  | Tv_Let recf attrs nb def body ->
    let def =
      if recf
      then subst_term [NM (r_binder_to_namedv nb) 0] def
      else def
    in
    let b, body = close_term_simple nb body in
    RD.Tv_Let recf attrs b def body

  | Tv_Match scrutinee ret brs ->
    let brs = List.Tot.map close_branch brs in
    let ret = FStar.Option.mapTot close_match_returns_ascription ret in
    RD.Tv_Match scrutinee ret brs

[@@plugin]
let inspect (t:term) : Tac named_term_view =
  let t = compress t in
  let tv = inspect_ln t in
  open_view tv

[@@plugin]
let pack (tv:named_term_view) : Tot term =
  let tv = close_view tv in
  pack_ln tv

// Repeat from FStar.R.Data
let notAscription (tv:named_term_view) : bool =
  not (Tv_AscribedT? tv) && not (Tv_AscribedC? tv)

[@@plugin]
noeq
type letbinding = {
  lb_fv : fv;
  lb_us : list univ_name; (* opened *)
  lb_typ : typ;
  lb_def : term;
}

[@@plugin]
noeq
type named_sigelt_view =
  | Sg_Let {
      isrec : bool;
      lbs   : list letbinding;
    }

  // Sg_Inductive basically coalesces the Sig_bundle used internally,
  // where the type definition and its constructors are split.
  // While that might be better for typechecking, this is probably better for metaprogrammers
  // (no mutually defined types for now)
  | Sg_Inductive {
      nm     : name;             // name of the inductive type being defined
      univs  : list univ_name;   // named universe variables
      params : binders;          // parameters
      typ    : typ;              // the type annotation for the inductive, i.e., indices -> Type #u
      ctors  : list ctor;        // the constructors, opened with univs and applied to params already
    }

  | Sg_Val {
      nm    : name;
      univs : list univ_name;
      typ   : typ;
    }

  | Unk

private
let open_lb (lb : R.letbinding) : Tac letbinding =
  let {lb_fv; lb_us; lb_typ; lb_def} = inspect_lb lb in
  let lb_us, s = open_univ_s lb_us in
  let lb_typ = subst_term s lb_typ in
  let lb_def = subst_term s lb_def in
  { lb_fv; lb_us; lb_typ; lb_def }

private
let close_lb (lb : letbinding) : R.letbinding =
  let {lb_fv; lb_us; lb_typ; lb_def} = lb in
  let lb_us, s = close_univ_s lb_us in
  let lb_typ = subst_term s lb_typ in
  let lb_def = subst_term s lb_def in
  pack_lb { lb_fv; lb_us; lb_typ; lb_def }

private
let subst_r_binders (s:subst_t) (bs : list R.binder) : list R.binder =
  List.Tot.mapi (fun i b -> r_subst_binder_sort (shift_subst i s) b) bs

private
let rec open_n_binders_from_arrow (bs : binders) (t : term) : Tac term =
  match bs with
  | [] -> t
  | b::bs ->
    match inspect t with
    | Tv_Arrow b' (C_Total t') ->
      let t' = subst_term [NT (r_binder_to_namedv b') (pack (Tv_Var (inspect_namedv (r_binder_to_namedv b))))] t' in
      open_n_binders_from_arrow bs t'
    | _ -> raise NotEnoughBinders

private
let open_sigelt_view (sv : sigelt_view) : Tac named_sigelt_view =
  match sv with
  | RD.Sg_Let isrec lbs ->
    let lbs = map open_lb lbs in
    (* open universes, maybe *)
    Sg_Let { isrec; lbs }

  | RD.Sg_Inductive nm univs params typ ctors ->
    let nparams = List.Tot.length params in

    (* Open universes everywhere *)
    let us, s = open_univ_s univs in
    let params = subst_r_binders s params in
    let typ = subst_term (shift_subst nparams s) typ in
    let ctors = map (fun (nm, ty) -> nm, subst_term s ty) ctors in

    (* Open parameters in themselves and in type *)
    let params, typ = open_term_n params typ in
    (* Remove the parameter binders from the constructors,
    replace them by the opened param binders. Hence we get
      Cons : a0 -> list a0
    instead of
      Cons : #a:Type -> a -> list a
    for the returned open parameter a0. *)
    let ctors =
      map (fun (nm, ty) ->
          let ty'= open_n_binders_from_arrow params ty in
          nm, ty')
        ctors
    in

    Sg_Inductive {nm; univs; params; typ; ctors}

  | RD.Sg_Val nm univs typ ->
    let univs, s = open_univ_s univs in
    let typ = subst_term s typ in
    Sg_Val {nm; univs; typ}

  | RD.Unk -> Unk

private
let rec mk_arr (args : list binder) (t : term) : Tac term =
  match args with
  | [] -> t
  | a :: args' ->
    let t' = C_Total (mk_arr args' t) in
    pack (Tv_Arrow a t')

private
let close_sigelt_view (sv : named_sigelt_view{~(Unk? sv)}) : Tac (sv:sigelt_view{~(RD.Unk? sv)}) =
  match sv with
  | Sg_Let { isrec; lbs } ->
    let lbs = List.Tot.map close_lb lbs in
    RD.Sg_Let isrec lbs

  | Sg_Inductive {nm; univs; params; typ; ctors} ->
    let nparams = List.Tot.length params in
    (* Abstract constructors by the parameters. This
    is the inverse of the open_n_binders_from_arrow above. *)
    let ctors =
        map (fun (nm, ty) ->
            let ty' = mk_arr params ty in
            nm, ty')
        ctors
    in

    (* Close parameters in themselves and typ *)
    let params, typ = close_term_n params typ in

    (* close univs *)
    let us, s = close_univ_s univs in
    let params = subst_r_binders s params in
    let typ = subst_term (shift_subst nparams s) typ in
    let ctors = map (fun (nm, ty) -> nm, subst_term s ty) ctors in

    RD.Sg_Inductive nm univs params typ ctors

  | Sg_Val {nm; univs; typ} ->
    let univs, s = close_univ_s univs in
    let typ = subst_term s typ in
    RD.Sg_Val nm univs typ

[@@plugin]
let inspect_sigelt (s : sigelt) : Tac named_sigelt_view =
  let sv = R.inspect_sigelt s in
  (* dump ("sv orig = " ^ term_to_string (quote sv)); *)
  open_sigelt_view sv

[@@plugin]
let pack_sigelt (sv:named_sigelt_view{~(Unk? sv)}) : Tac sigelt =
  let sv = close_sigelt_view sv in
  R.pack_sigelt sv

(* Clients of this module use the named view. *)
let term_view   = named_term_view
let sigelt_view = named_sigelt_view

(* Temporary adapters, to avoid breaking existing code too much. *)
let inspect_namedv   = id #namedv
let pack_namedv      = id #namedv
let inspect_bv       = id #bv
let pack_bv          = id #bv
let inspect_comp     = id #comp
let pack_comp        = id #comp

(* Some primitives mention `comp`, wrap them to use `comp_view` *)
let tcc (e:env) (t:term) : Tac comp =
  let c : R.comp = V2.Builtins.tcc e t in
  R.inspect_comp c

let comp_to_string (c:comp) : Tac string = V2.Builtins.comp_to_string (R.pack_comp c)
