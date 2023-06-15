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
open FStar.Stubs.Tactics.V2.Builtins

exception LengthMismatch
exception NotEnoughBinders

(* We work with reflection V2. *)
module R = FStar.Reflection.V2
module RD = FStar.Stubs.Reflection.V2.Data

let open_universe_view (v:RD.universe_view) : named_universe_view =
  match v with
  | R.Uv_Zero -> Uv_Zero
  | R.Uv_Succ u -> Uv_Succ u
  | R.Uv_Max us -> Uv_Max us
  | R.Uv_BVar n -> Uv_BVar n
  | R.Uv_Name i -> Uv_Name (inspect_ident i)
  | R.Uv_Unif uvar -> Uv_Unif uvar
  | R.Uv_Unk -> Uv_Unk

let inspect_universe (u:universe) : named_universe_view =
  let v = R.inspect_universe u in
  open_universe_view v

let close_universe_view (v:named_universe_view) : R.universe_view =
  match v with
  | Uv_Zero -> R.Uv_Zero
  | Uv_Succ u -> R.Uv_Succ u
  | Uv_Max us -> R.Uv_Max us
  | Uv_BVar n -> R.Uv_BVar n
  | Uv_Name i -> R.Uv_Name (pack_ident i)
  | Uv_Unif uvar -> R.Uv_Unif uvar
  | Uv_Unk -> R.Uv_Unk

let pack_universe (uv:named_universe_view) : universe =
  let uv = close_universe_view uv in
  R.pack_universe uv

private
let __binding_to_binder (bnd : binding) (b : R.binder) : binder =
  {
      ppname = bnd.ppname;
      uniq   = bnd.uniq;
      sort   = bnd.sort;
      qual   = (inspect_binder b).qual;
      attrs  = (inspect_binder b).attrs;
  }

private
let r_binder_to_namedv (b : binder) : R.namedv =
  pack_namedv {
    uniq   = b.uniq;
    sort   = seal b.sort;
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

(* This can be useful externally *)
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
    (* NOTE: this used to use FStar.Option.mapTot, but that brings
    in way too many dependencies. *)
    let ret =
      match ret with
      | None -> None
      | Some asc -> Some (close_match_returns_ascription asc)
    in
    RD.Tv_Match scrutinee ret brs

[@@plugin; coercion]
let inspect (t:term) : Tac named_term_view =
  let t = compress t in
  let tv = inspect_ln t in
  open_view tv

[@@plugin; coercion]
let pack (tv:named_term_view) : Tot term =
  let tv = close_view tv in
  pack_ln tv

private
let open_univ_s (us : list R.univ_name) : Tac (list univ_name & subst_t) =
  let n = List.Tot.length us in
  let s = mapi (fun i u -> UN (n-1-i) (R.pack_universe (R.Uv_Name u))) us in
  Util.map (fun i -> inspect_ident i) us, s

private
let close_univ_s (us : list univ_name) : list R.univ_name & subst_t =
  let n = List.Tot.length us in
  let us = List.Tot.map (fun i -> pack_ident i) us in
  let s = List.Tot.mapi (fun i u -> UD u (n-i-1)) us in
  us, s

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
    let univs, s = open_univ_s univs in
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
    let univs, s = close_univ_s univs in
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

let tcc (e:env) (t:term) : Tac comp =
  let c : R.comp = Stubs.Tactics.V2.Builtins.tcc e t in
  R.inspect_comp c

let comp_to_string (c:comp) : Tac string = Stubs.Tactics.V2.Builtins.comp_to_string (R.pack_comp c)
