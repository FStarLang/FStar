(*
   Copyright 2008-2023 Microsoft Research

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

module FStar.Reflection.Typing

(** This module defines a typing judgment for (parts of) the total
    and ghost fragment of F*.
    
    We are using it in the meta DSL framework as an
    official specification for the F* type system.

    We expect it to grow to cover more of the F* language.

    IT IS HIGHLY EXPERIMENTAL AND NOT YET READY TO USE.
  *)

open FStar.List.Tot
open FStar.Reflection
module R = FStar.Reflection
module T = FStar.Tactics
module FTB = FStar.Tactics.Builtins

val inspect_pack (t:R.term_view)
  : Lemma (ensures R.(inspect_ln (pack_ln t) == t))
          [SMTPat R.(inspect_ln (pack_ln t))]
  
val pack_inspect (t:R.term)
  : Lemma (requires ~(Tv_Unknown? (inspect_ln t)))
          (ensures R.(pack_ln (inspect_ln t) == t))
          [SMTPat R.(pack_ln (inspect_ln t))]
  
val inspect_pack_bv (t:R.bv_view)
  : Lemma (ensures R.(inspect_bv (pack_bv t) == t))
          [SMTPat R.(inspect_bv (pack_bv t))]
  
val pack_inspect_bv (t:R.bv)
  : Lemma (ensures R.(pack_bv (inspect_bv t) == t))
          [SMTPat R.(pack_bv (inspect_bv t))]
  
val inspect_pack_binder (bview:R.binder_view)
  : Lemma (ensures R.(R.inspect_binder (R.pack_binder bview) == bview))
          [SMTPat R.(inspect_binder (pack_binder bview))]
  
val pack_inspect_binder (t:R.binder)
   : Lemma (ensures (R.pack_binder (R.inspect_binder t) == t))
           [SMTPat (R.pack_binder (R.inspect_binder t))]
  
val pack_inspect_comp (t:R.comp)
  : Lemma (ensures (R.pack_comp (R.inspect_comp t) == t))
          [SMTPat (R.pack_comp (R.inspect_comp t))]
  
val inspect_pack_comp (t:R.comp_view)
  : Lemma (ensures (R.inspect_comp (R.pack_comp t) == t))
          [SMTPat (R.inspect_comp (R.pack_comp t))]

val pack_inspect_fv (fv:R.fv)
  : Lemma (ensures R.pack_fv (R.inspect_fv fv) == fv)
          [SMTPat (R.pack_fv (R.inspect_fv fv))]

val inspect_pack_fv (nm:R.name)
  : Lemma (ensures R.inspect_fv (R.pack_fv nm) == nm)
          [SMTPat (R.inspect_fv (R.pack_fv nm))]

val pack_inspect_universe (u:R.universe)
  : Lemma (requires ~(Uv_Unk? (inspect_universe u)))
          (ensures R.pack_universe (R.inspect_universe u) == u)
          [SMTPat (R.pack_universe (R.inspect_universe u))]

val inspect_pack_universe (u:R.universe_view)
  : Lemma (ensures R.inspect_universe (R.pack_universe u) == u)
          [SMTPat (R.inspect_universe (R.pack_universe u))]

val lookup_bvar (e:env) (x:int) : option term

val lookup_fvar_uinst (e:R.env) (x:R.fv) (us:list R.universe) : option R.term

let lookup_fvar (e:env) (x:fv) : option term = lookup_fvar_uinst e x []

let pp_name_t = FStar.Sealed.Inhabited.sealed "x"
let pp_name_default : pp_name_t = FStar.Sealed.Inhabited.seal "x"
let seal_pp_name x : pp_name_t = FStar.Sealed.Inhabited.seal x

let mk_binder (pp_name:pp_name_t) (x:var) (ty:term) (q:aqualv)
  = pack_binder
      { binder_bv=pack_bv ({bv_ppname=pp_name;
                            bv_index=x});
        binder_qual=q;
        binder_attrs=[];
        binder_sort=ty}

let extend_env (e:env) (x:var) (ty:term) : env =
  R.push_binder e (mk_binder (seal_pp_name "x") x ty Q_Explicit)
  
val lookup_bvar_extend_env (g:env) (x y:var) (ty:term)
  : Lemma 
    (ensures (
           if x = y
           then lookup_bvar (extend_env g x ty) y == Some ty
           else lookup_bvar (extend_env g x ty) y == lookup_bvar g y))
    [SMTPat (lookup_bvar (extend_env g x ty) y)]

val lookup_fvar_extend_env (g:env) (x:fv) (us:universes) (y:var) (ty:term)
  : Lemma 
    (ensures lookup_fvar_uinst (extend_env g y ty) x us == lookup_fvar_uinst g x us)
    [SMTPat (lookup_fvar_uinst (extend_env g y ty) x us)]

let as_binder (x:var) (ty:term) =
  mk_binder (seal_pp_name "x") x ty Q_Explicit

let bv_index (x:bv)
  : var
  = (inspect_bv x).bv_index

let binder_sort (b:binder) =
  (inspect_binder b).binder_sort

let binder_qual (b:binder) =
  let { binder_qual = q } = inspect_binder b in q

noeq
type open_or_close =
  | OpenWith of term
  | CloseVar of var
  | Rename   : var -> var -> open_or_close

let tun = pack_ln Tv_Unknown

let make_bv (n:nat) = {
  bv_ppname = pp_name_default;
  bv_index = n;
}
let make_bv_with_name (s:pp_name_t) (n:nat) = {
  bv_ppname = s;
  bv_index = n;
}
let var_as_bv (v:nat) = pack_bv (make_bv v)
let var_as_term (v:var) = pack_ln (Tv_Var (var_as_bv v))

let binder_of_t_q t q = mk_binder pp_name_default 0 t q
let mk_abs ty qual t : R.term =  R.pack_ln (R.Tv_Abs (binder_of_t_q ty qual) t)
let mk_total t = pack_comp (C_Total t)
let mk_ghost t = pack_comp (C_GTotal t)
let mk_arrow ty qual t : R.term =
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty qual) (mk_total t))
let mk_ghost_arrow ty qual t : R.term =
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty qual) (mk_ghost t))
let bound_var i : R.term = R.pack_ln (R.Tv_BVar (R.pack_bv (make_bv i)))

let open_with_var (x:var) = OpenWith (pack_ln (Tv_Var (var_as_bv x)))
  
let maybe_index_of_term (x:term) =
  match inspect_ln x with
  | Tv_Var bv -> Some (bv_index bv)
  | _ -> None
  
val open_or_close_ctx_uvar_and_subst (c:ctx_uvar_and_subst) (v:open_or_close) (i:nat) 
  : ctx_uvar_and_subst

let rec binder_offset_patterns (ps:list (pattern & bool))
  : nat
  = match ps with
    | [] -> 0
    | (p, b)::ps ->
      let n = binder_offset_pattern p in
      let m = binder_offset_patterns ps in
      n + m

and binder_offset_pattern (p:pattern)
  : nat
  = match p with
    | Pat_Constant _
    | Pat_Dot_Term _ -> 0

    | Pat_Var _
    | Pat_Wild _ -> 1

    | Pat_Cons fv us pats -> 
      binder_offset_patterns pats

let rec open_or_close_term' (t:term) (v:open_or_close) (i:nat)
  : Tot term (decreases t)
  = match inspect_ln t with
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown -> t
    | Tv_Var x ->
      (match v with
       | OpenWith _ -> t
       | CloseVar y ->
         if bv_index x = y 
         then pack_ln (Tv_BVar (pack_bv { inspect_bv x with bv_index = i }))
         else t
       | Rename y z ->
         if bv_index x = y
         then pack_ln (Tv_Var (pack_bv { inspect_bv x with bv_index = z }))
         else t)

    | Tv_BVar j -> 
      (match v with
       | Rename _ _ -> t
       | CloseVar _ -> t
       | OpenWith v ->
         if i=bv_index j 
         then (
           match maybe_index_of_term v with
           | None -> v
           | Some k ->
             //if we're substituting a name j for a name k, retain the pp_name of j
             pack_ln (Tv_Var (pack_bv { inspect_bv j with bv_index = k }))
         )
         else t
      )

    | Tv_App hd argv ->
      pack_ln (Tv_App (open_or_close_term' hd v i)
                      (open_or_close_term' (fst argv) v i, snd argv))

    | Tv_Abs b body -> 
      let b' = open_or_close_binder' b v i in
      pack_ln (Tv_Abs b' (open_or_close_term' body v (i + 1)))

    | Tv_Arrow b c ->
      let b' = open_or_close_binder' b v i in
      pack_ln (Tv_Arrow b' (open_or_close_comp' c v (i + 1)))      

    | Tv_Refine bv sort f ->
      pack_ln (Tv_Refine bv (open_or_close_term' sort v i)
                            (open_or_close_term' f v (i + 1)))

    | Tv_Uvar j c ->
      pack_ln (Tv_Uvar j (open_or_close_ctx_uvar_and_subst c v i))
      
    | Tv_Let recf attrs bv ty def body ->
      pack_ln (Tv_Let recf 
                      (open_or_close_terms' attrs v i)
                      bv
                      (open_or_close_term' ty v i)
                      (if recf 
                       then open_or_close_term' def v (i + 1)
                       else open_or_close_term' def v i)
                      (open_or_close_term' body v (i + 1)))

    | Tv_Match scr ret brs ->
      pack_ln (Tv_Match (open_or_close_term' scr v i)
                        (match ret with
                         | None -> None
                         | Some m -> Some (open_or_close_match_returns' m v i))
                        (open_or_close_branches' brs v i))
      
    | Tv_AscribedT e t tac b ->
      pack_ln (Tv_AscribedT (open_or_close_term' e v i)
                            (open_or_close_term' t v i)
                            (match tac with
                             | None -> None
                             | Some tac -> Some (open_or_close_term' tac v i))
                             b)

    | Tv_AscribedC e c tac b ->
      pack_ln (Tv_AscribedC (open_or_close_term' e v i)
                            (open_or_close_comp' c v i)
                            (match tac with
                             | None -> None
                             | Some tac -> Some (open_or_close_term' tac v i))
                             b)

and open_or_close_binder' (b:binder) (v:open_or_close) (i:nat)
  : Tot binder (decreases b)
  = let bndr  = inspect_binder b in
    pack_binder {binder_bv=bndr.binder_bv;
                 binder_qual=bndr.binder_qual;
                 binder_attrs=open_or_close_terms' bndr.binder_attrs v i;
                 binder_sort=open_or_close_term' bndr.binder_sort v i}

and open_or_close_comp' (c:comp) (v:open_or_close) (i:nat)
  : Tot comp (decreases c)
  = match inspect_comp c with
    | C_Total t ->
      pack_comp (C_Total (open_or_close_term' t v i))

    | C_GTotal t ->
      pack_comp (C_GTotal (open_or_close_term' t v i))

    | C_Lemma pre post pats ->
      pack_comp (C_Lemma (open_or_close_term' pre v i)
                         (open_or_close_term' post v i)
                         (open_or_close_term' pats v i))

    | C_Eff us eff_name res args decrs ->
      pack_comp (C_Eff us eff_name
                       (open_or_close_term' res v i)
                       (open_or_close_args' args v i)
                       (open_or_close_terms' decrs v i))

and open_or_close_terms' (ts:list term) (v:open_or_close) (i:nat)
  : Tot (list term) (decreases ts)
  = match ts with
    | [] -> []
    | t::ts -> open_or_close_term' t v i :: open_or_close_terms' ts v i

and open_or_close_args' (ts:list argv) (v:open_or_close) (i:nat)
  : Tot (list argv) (decreases ts)
  = match ts with
    | [] -> []
    | (t,q)::ts -> (open_or_close_term' t v i,q) :: open_or_close_args' ts v i

and open_or_close_patterns' (ps:list (pattern & bool)) (v:open_or_close) (i:nat) 
  : Tot (list (pattern & bool))
         (decreases ps)
  = match ps with
    | [] -> ps
    | (p, b)::ps ->
      let n = binder_offset_pattern p in
      let p = open_or_close_pattern' p v i in
      let ps = open_or_close_patterns' ps v (i + n) in
      (p,b)::ps

and open_or_close_pattern' (p:pattern) (v:open_or_close) (i:nat) 
  : Tot pattern
         (decreases p)
  = match p with
    | Pat_Constant _ -> p

    | Pat_Cons fv us pats -> 
      let pats = open_or_close_patterns' pats v i in
      Pat_Cons fv us pats
      
    | Pat_Var bv ->
      Pat_Var bv

    | Pat_Wild bv ->
      Pat_Wild bv

    | Pat_Dot_Term topt ->
      Pat_Dot_Term (match topt with
                    | None -> None
                    | Some t -> Some (open_or_close_term' t v i))

    
and open_or_close_branch' (br:branch) (v:open_or_close) (i:nat)
  : Tot branch (decreases br)
  = let p, t = br in
    let p = open_or_close_pattern' p v i in
    let j = binder_offset_pattern p in
    let t = open_or_close_term' t v (i + j) in
    p, t
  
and open_or_close_branches' (brs:list branch) (v:open_or_close) (i:nat)
  : Tot (list branch) (decreases brs)
  = match brs with
    | [] -> []
    | br::brs -> open_or_close_branch' br v i :: open_or_close_branches' brs v i
  
and open_or_close_match_returns' (m:match_returns_ascription) (v:open_or_close) (i:nat)
  : Tot match_returns_ascription (decreases m)
  = let b, (ret, as_, eq) = m in
    let b = open_or_close_binder' b v i in
    let ret =
      match ret with
      | Inl t -> Inl (open_or_close_term' t v (i + 1))
      | Inr c -> Inr (open_or_close_comp' c v (i + 1))
    in
    let as_ =
      match as_ with
      | None -> None
      | Some t -> Some (open_or_close_term' t v (i + 1))
    in
    b, (ret, as_, eq)

val open_with (t:term) (v:term) : term
  
val open_with_spec (t v:term)
  : Lemma (open_with t v == open_or_close_term' t (OpenWith v) 0)

val open_term (t:term) (v:var) : term

val open_term_spec (t:term) (v:var)
  : Lemma (open_term t v == open_or_close_term' t (open_with_var v) 0)
  
val close_term (t:term) (v:var) : term

val close_term_spec (t:term) (v:var)
  : Lemma (close_term t v == open_or_close_term' t (CloseVar v) 0)

val rename (t:term) (x y:var) : term

val rename_spec (t:term) (x y:var)
  : Lemma (rename t x y == open_or_close_term' t (Rename x y) 0)
  
val bv_index_of_make_bv (n:nat)
  : Lemma (ensures bv_index (pack_bv (make_bv n)) == n)
          [SMTPat (bv_index (pack_bv (make_bv n)))]

let constant_as_term (v:vconst) = pack_ln (Tv_Const v)
let unit_exp = constant_as_term C_Unit
let unit_fv = pack_fv unit_lid
let unit_ty = pack_ln (Tv_FVar unit_fv)
let bool_fv = pack_fv bool_lid
let bool_ty = pack_ln (Tv_FVar bool_fv)

let u_zero = pack_universe Uv_Zero
let u_max u1 u2 = pack_universe (Uv_Max [u1; u2])
let u_succ u = pack_universe (Uv_Succ u)
let tm_type u = pack_ln (Tv_Type u)
let tm_prop = 
  let prop_fv = R.pack_fv R.prop_qn in
  R.pack_ln (Tv_FVar prop_fv)
let eqtype_lid : R.name = ["Prims"; "eqtype"]

let true_bool = pack_ln (Tv_Const C_True)
let false_bool = pack_ln (Tv_Const C_False)
let eq2 (u:universe) (t v0 v1:term) 
  : term 
  = let eq2 = pack_fv eq2_qn in
    let eq2 = pack_ln (Tv_UInst eq2 [u]) in
    let h = pack_ln (Tv_App eq2 (t, Q_Implicit)) in
    let h1 = pack_ln (Tv_App h (v0, Q_Explicit)) in
    let h2 = pack_ln (Tv_App h1 (v1, Q_Explicit)) in    
    h2

let b2t_lid : R.name = ["Prims"; "b2t"]
let b2t_fv : R.fv = R.pack_fv b2t_lid
let b2t_ty : R.term = R.(pack_ln (Tv_Arrow (as_binder 0 bool_ty) (mk_total (tm_type u_zero))))


////////////////////////////////////////////////////////////////////////////////
// freevars
////////////////////////////////////////////////////////////////////////////////


let rec freevars (e:term)
  : FStar.Set.set var
  = match inspect_ln e with
    | Tv_Uvar _ _ -> Set.complement Set.empty
    
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown 
    | Tv_BVar _ -> Set.empty

    | Tv_Var x -> Set.singleton (bv_index x)
       
    | Tv_App e1 (e2, _) ->
      Set.union (freevars e1) (freevars e2)

    | Tv_Abs b body -> 
      Set.union (freevars_binder b) (freevars body)

    | Tv_Arrow b c ->
      Set.union (freevars_binder b) (freevars_comp c)

    | Tv_Refine bv sort f ->
       freevars sort `Set.union`
       freevars f
      
    | Tv_Let recf attrs bv ty def body ->
      freevars_terms attrs `Set.union`
      freevars ty `Set.union`
      freevars def `Set.union`
      freevars body

    | Tv_Match scr ret brs ->
      freevars scr `Set.union`
      freevars_opt ret freevars_match_returns  `Set.union`
      freevars_branches brs

    | Tv_AscribedT e t tac b ->
      freevars e `Set.union`
      freevars t `Set.union`
      freevars_opt tac freevars
                            
    | Tv_AscribedC e c tac b ->
      freevars e `Set.union`
      freevars_comp c `Set.union`
      freevars_opt tac freevars

and freevars_opt (#a:Type0) (o:option a) (f: (x:a { x << o } -> FStar.Set.set var))
  : FStar.Set.set var
  = match o with
    | None -> Set.empty
    | Some x -> f x

and freevars_comp (c:comp)
  : FStar.Set.set var
  = match inspect_comp c with
    | C_Total t
    | C_GTotal t ->
      freevars t

    | C_Lemma pre post pats ->
      freevars pre `Set.union`
      freevars post `Set.union`
      freevars pats

    | C_Eff us eff_name res args decrs ->
      freevars res `Set.union`
      freevars_args args `Set.union`
      freevars_terms decrs

and freevars_args (ts:list argv)
  : FStar.Set.set var
  = match ts with
    | [] -> Set.empty
    | (t,q)::ts ->
      freevars t `Set.union`
      freevars_args ts

and freevars_terms (ts:list term)
  : FStar.Set.set var
  = match ts with
    | [] -> Set.empty
    | t::ts ->
      freevars t `Set.union`
      freevars_terms ts
    
and freevars_binder (b:binder)
  : Tot (Set.set var) (decreases b)
  = let bndr  = inspect_binder b in
    freevars bndr.binder_sort `Set.union`
    freevars_terms bndr.binder_attrs 
    

and freevars_pattern (p:pattern) 
  : Tot (Set.set var) (decreases p)
  = match p with
    | Pat_Constant _ ->
      Set.empty

    | Pat_Cons fv us pats -> 
      freevars_patterns pats
      
    | Pat_Var bv 
    | Pat_Wild bv -> Set.empty

    | Pat_Dot_Term topt ->
      freevars_opt topt freevars

and freevars_patterns (ps:list (pattern & bool))
  : Tot (Set.set var) (decreases ps)
  = match ps with
    | [] -> Set.empty
    | (p, b)::ps ->
      freevars_pattern p `Set.union`
      freevars_patterns ps

and freevars_branch (br:branch)
  : Tot (Set.set var) (decreases br)
  = let p, t = br in
    freevars_pattern p `Set.union`
    freevars t

and freevars_branches (brs:list branch)
  : Tot (Set.set var) (decreases brs)
  = match brs with
    | [] -> Set.empty
    | hd::tl -> freevars_branch hd `Set.union` freevars_branches tl
  
and freevars_match_returns (m:match_returns_ascription)
  : Tot (Set.set var) (decreases m)
  = let b, (ret, as_, eq) = m in
    let b = freevars_binder b in
    let ret =
      match ret with
      | Inl t -> freevars t
      | Inr c -> freevars_comp c
    in
    let as_ = freevars_opt as_ freevars in
    b `Set.union` ret `Set.union` as_

//
// term_ctxt is used to define the equiv relation later,
//   basically putting two equiv terms in a hole gives equiv terms
//
// The abs, arrow, refine, and let cases don't seem right here,
//   since to prove their equiv, we need to extend gamma for their bodies
//
// If this is useful only for app, then may be we should remove it,
//   and add app rules to the equiv relation itself

[@@ no_auto_projectors]
noeq
type term_ctxt =
  | Ctxt_hole            : term_ctxt
  | Ctxt_app_head        : term_ctxt -> argv -> term_ctxt
  | Ctxt_app_arg         : term -> aqualv -> term_ctxt -> term_ctxt
  // | Ctxt_abs_binder      : binder_ctxt -> term -> term_ctxt
  // | Ctxt_abs_body        : binder -> term_ctxt -> term_ctxt
  // | Ctxt_arrow_binder    : binder_ctxt -> comp -> term_ctxt
  // | Ctxt_arrow_comp      : binder -> comp_ctxt -> term_ctxt
  // | Ctxt_refine_sort     : bv -> term_ctxt -> term -> term_ctxt
  // | Ctxt_refine_ref      : bv -> typ -> term_ctxt -> term_ctxt
  // | Ctxt_let_sort        : bool -> list term -> bv -> term_ctxt -> term -> term -> term_ctxt
  // | Ctxt_let_def         : bool -> list term -> bv -> term -> term_ctxt -> term -> term_ctxt
  // | Ctxt_let_body        : bool -> list term -> bv -> term -> term -> term_ctxt -> term_ctxt
  // | Ctxt_match_scrutinee : term_ctxt -> option match_returns_ascription -> list branch -> term_ctxt

// and bv_ctxt =
//   | Ctxt_bv : sealed string -> nat -> term_ctxt -> bv_ctxt

// and binder_ctxt =
//   | Ctxt_binder : bv -> aqualv -> list term -> term_ctxt -> binder_ctxt

// and comp_ctxt =
//   | Ctxt_total  : term_ctxt -> comp_ctxt
//   | Ctxt_gtotal : term_ctxt -> comp_ctxt

let rec apply_term_ctxt (e:term_ctxt) (t:term) : Tot term (decreases e) =
  match e with
  | Ctxt_hole -> t
  | Ctxt_app_head e arg -> pack_ln (Tv_App (apply_term_ctxt e t) arg)
  | Ctxt_app_arg hd q e -> pack_ln (Tv_App hd (apply_term_ctxt e t, q))
//   | Ctxt_abs_binder b body -> pack_ln (Tv_Abs (apply_binder_ctxt b t) body)
//   | Ctxt_abs_body b e -> pack_ln (Tv_Abs b (apply_term_ctxt e t))
//   | Ctxt_arrow_binder b c -> pack_ln (Tv_Arrow (apply_binder_ctxt b t) c)
//   | Ctxt_arrow_comp b c -> pack_ln (Tv_Arrow b (apply_comp_ctxt c t))
//   | Ctxt_refine_sort b sort phi -> pack_ln (Tv_Refine b (apply_term_ctxt sort t) phi)
//   | Ctxt_refine_ref b sort phi -> pack_ln (Tv_Refine b sort (apply_term_ctxt phi t))
  
//   | Ctxt_let_sort b attrs bv sort def body ->
//     pack_ln (Tv_Let b attrs bv (apply_term_ctxt sort t) def body)
//   | Ctxt_let_def b attrs bv sort def body ->
//     pack_ln (Tv_Let b attrs bv sort (apply_term_ctxt def t) body)
//   | Ctxt_let_body b attrs bv sort def body ->
//     pack_ln (Tv_Let b attrs bv sort def (apply_term_ctxt body t))
    
//   | Ctxt_match_scrutinee sc ret brs ->
//     pack_ln (Tv_Match (apply_term_ctxt sc t) ret brs)

// and apply_binder_ctxt (b:binder_ctxt) (t:term) : Tot binder (decreases b) =
//   let Ctxt_binder binder_bv binder_qual binder_attrs ctxt = b in
//   pack_binder {binder_bv; binder_qual; binder_attrs; binder_sort=apply_term_ctxt ctxt t}

// and apply_comp_ctxt (c:comp_ctxt) (t:term) : Tot comp (decreases c) =
//   match c with
//   | Ctxt_total e -> pack_comp (C_Total (apply_term_ctxt e t))
//   | Ctxt_gtotal e -> pack_comp (C_GTotal (apply_term_ctxt e t))

noeq
type constant_typing: vconst -> term -> Type0 = 
  | CT_Unit: constant_typing C_Unit unit_ty
  | CT_True: constant_typing C_True bool_ty
  | CT_False: constant_typing C_False bool_ty

[@@ no_auto_projectors]
noeq
type univ_eq : universe -> universe -> Type0 = 
  | UN_Refl : 
    u:universe ->
    univ_eq u u

  | UN_MaxCongL :
    u:universe ->
    u':universe ->
    v:universe ->
    univ_eq u u' ->
    univ_eq (u_max u v) (u_max u' v)

  | UN_MaxCongR :
    u:universe ->
    v:universe ->
    v':universe ->
    univ_eq v v' ->
    univ_eq (u_max u v) (u_max u v')

  | UN_MaxComm:
    u:universe ->
    v:universe ->
    univ_eq (u_max u v) (u_max v u)

  | UN_MaxLeq:
    u:universe ->
    v:universe ->
    univ_leq u v ->
    univ_eq (u_max u v) v

and univ_leq : universe -> universe -> Type0 = 
  | UNLEQ_Refl:
    u:universe ->
    univ_leq u u

  | UNLEQ_Succ:
    u:universe ->
    v:universe ->
    univ_leq u v ->
    univ_leq u (u_succ v)

  | UNLEQ_Max:
    u:universe ->
    v:universe ->
    univ_leq u (u_max u v)

let mk_if (scrutinee then_ else_:R.term) : R.term =
  pack_ln (Tv_Match scrutinee None [(Pat_Constant C_True, then_); 
                                    (Pat_Constant C_False, else_)])


// effect and type
type comp_typ = T.effect_label & typ

let close_comp_typ' (c:comp_typ) (x:var) (i:nat) =
  fst c, open_or_close_term' (snd c) (CloseVar x) i

let close_comp_typ (c:comp_typ) (x:var) =
  close_comp_typ' c x 0

let open_comp_typ' (c:comp_typ) (x:var) (i:nat) =
  fst c, open_or_close_term' (snd c) (open_with_var x) i

let open_comp_typ (c:comp_typ) (x:var) =
  open_comp_typ' c x 0

let freevars_comp_typ (c:comp_typ) = freevars (snd c)

let mk_comp (c:comp_typ) : R.comp =
  match fst c with
  | T.E_Total -> mk_total (snd c)
  | T.E_Ghost -> mk_ghost (snd c)

let mk_arrow_ct ty qual (c:comp_typ) : R.term =
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty qual) (mk_comp c))
 
type relation =
  | R_Eq
  | R_Sub

//
// TODO: support for erasable attribute
//
let is_non_informative_name (l:name) : bool =
  l = R.squash_qn ||
  l = ["FStar"; "Ghost"; "erased"]

let is_non_informative_fv (f:fv) : bool =
  is_non_informative_name (inspect_fv f)

[@@ no_auto_projectors]
noeq
type non_informative : term -> Type0 =
  | Non_informative_type:
    u:universe ->
    non_informative (pack_ln (Tv_Type u))
  
  | Non_informative_fv:
    x:fv{is_non_informative_fv x} ->
    non_informative (pack_ln (Tv_FVar x))
  
  | Non_informative_uinst:
    x:fv ->
    us:list universe ->
    non_informative (pack_ln (Tv_UInst x us))

  | Non_informative_app:
    t:term ->
    arg:argv ->
    non_informative t ->
    non_informative (pack_ln (Tv_App t arg))

  | Non_informative_total_arrow:
    t0:term ->
    q:aqualv ->
    t1:term ->
    non_informative t1 ->
    non_informative (mk_arrow_ct t0 q (T.E_Total, t1))
  
  | Non_informative_ghost_arrow:
    t0:term ->
    q:aqualv ->
    t1:term ->
    non_informative (mk_arrow_ct t0 q (T.E_Ghost, t1))
    

[@@ no_auto_projectors]
noeq
type typing : env -> term -> comp_typ -> Type0 =
  | T_Token :
    g:env ->
    e:term ->
    c:comp_typ ->
    squash (FTB.typing_token g e c) ->
    typing g e c

  | T_Var : 
     g:env ->
     x:bv { Some? (lookup_bvar g (bv_index x)) } ->
     typing g (pack_ln (Tv_Var x)) (T.E_Total, Some?.v (lookup_bvar g (bv_index x)))

  | T_FVar :
     g:env ->
     x:fv { Some? (lookup_fvar g x) } -> 
     typing g (pack_ln (Tv_FVar x)) (T.E_Total, Some?.v (lookup_fvar g x))

  | T_UInst :
     g:env ->
     x:fv ->
     us:list universe { Some? (lookup_fvar_uinst g x us) } ->
     typing g (pack_ln (Tv_UInst x us)) (T.E_Total, Some?.v (lookup_fvar_uinst g x us))

  | T_Const:
     g:env ->
     v:vconst ->
     t:term ->
     constant_typing v t ->
     typing g (constant_as_term v) (T.E_Total, t)

  | T_Abs :
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     ty:term ->
     body:term { ~(x `Set.mem` freevars body) } ->
     body_c:comp_typ ->
     u:universe ->
     pp_name:pp_name_t ->
     q:aqualv ->
     typing g ty (T.E_Ghost, tm_type u) ->
     typing (extend_env g x ty) (open_term body x) body_c ->
     typing g (pack_ln (Tv_Abs (mk_binder pp_name 0 ty q) body))
              (T.E_Total,
               pack_ln (Tv_Arrow (mk_binder pp_name 0 ty q)
                                 (mk_comp (close_comp_typ body_c x))))

  | T_App :
     g:env ->
     e1:term ->
     e2:term ->
     x:binder ->
     t:term ->
     eff:T.effect_label ->
     typing g e1 (eff, pack_ln (Tv_Arrow x (mk_comp (eff, t)))) ->
     typing g e2 (eff, binder_sort x) ->
     typing g (pack_ln (Tv_App e1 (e2, binder_qual x)))
              (eff, open_with t e2)

  | T_Arrow:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     t1:term ->
     t2:term { ~(x `Set.mem` freevars t2) } ->
     u1:universe ->
     u2:universe ->
     pp_name:pp_name_t ->
     q:aqualv ->
     eff:T.effect_label ->
     typing g t1 (T.E_Ghost, tm_type u1) ->
     typing (extend_env g x t1) (open_term t2 x) (T.E_Ghost, tm_type u2) ->
     typing g (pack_ln (Tv_Arrow (mk_binder pp_name 0 t1 q) (mk_comp (eff, t2))))
              (T.E_Total, tm_type (u_max u1 u2))

  | T_Refine:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->     
     t:term ->
     e:term { ~(x `Set.mem` freevars e) } ->
     u1:universe ->
     u2:universe ->     
     typing g t (T.E_Ghost, tm_type u1) ->
     typing (extend_env g x t) (open_term e x) (T.E_Ghost, tm_type u2) ->
     typing g (pack_ln (Tv_Refine (pack_bv (make_bv 0)) t e)) (T.E_Total, tm_type u1)

  | T_PropIrrelevance:
     g:env -> 
     e:term -> 
     t:term ->
     typing g e (T.E_Ghost, t) ->
     typing g t (T.E_Ghost, tm_prop) ->
     typing g (`()) (T.E_Total, t)
     
  | T_Sub:
     g:env ->
     e:term ->
     c:comp_typ ->
     c':comp_typ ->
     typing g e c ->
     sub_comp g c c' ->
     typing g e c'

  | T_If: 
     g:env ->
     scrutinee:term ->
     then_:term ->
     else_:term ->
     ty:term ->
     u_ty:universe ->
     hyp:var { None? (lookup_bvar g hyp) /\ ~(hyp `Set.mem` (freevars then_ `Set.union` freevars else_)) } ->
     eff:T.effect_label ->
     typing g scrutinee (eff, bool_ty) ->
     typing (extend_env g hyp (eq2 (pack_universe Uv_Zero) bool_ty scrutinee true_bool)) then_ (eff, ty) ->
     typing (extend_env g hyp (eq2 (pack_universe Uv_Zero) bool_ty scrutinee false_bool)) else_ (eff, ty) ->
     typing g ty (T.E_Ghost, tm_type u_ty) -> //typedness of ty cannot rely on hyp
     typing g (mk_if scrutinee then_ else_) (eff, ty)

  // | T_Match: 
  //    g:env ->
  //    scrutinee:term ->
  //    i_ty:term ->
  //    branches:list branch ->
  //    ty:term ->
  //    typing g scrutinee i_ty ->
  //    branches_typing g scrutinee i_ty branches ty ->
  //    typing g (pack_ln (Tv_Match scrutinee None branches)) ty

and related : env -> term -> relation -> term -> Type0 =
  | Rel_equiv:
    g:env ->
    t0:term ->
    t1:term ->
    rel:relation ->
    equiv g t0 t1 ->
    related g t0 rel t1

  | Rel_subtyping_token:
    g:env ->
    t0:term ->
    t1:term ->
    squash (FTB.subtyping_token g t0 t1) ->
    related g t0 R_Sub t1

  | Rel_univ_eq:  // can it be part of the equiv relation?
    g:env ->
    u:universe ->
    v:universe ->
    rel:relation ->
    univ_eq u v ->
    related g (tm_type u) rel (tm_type v)

  | Rel_arrow:
    g:env ->
    t1:term ->
    t2:term ->
    q:aqualv ->
    c1:comp_typ ->
    c2:comp_typ ->
    rel:relation ->
    x:var{
      None? (lookup_bvar g x) /\
      ~ (x `Set.mem` (freevars_comp_typ c1 `Set.union` freevars_comp_typ c2))
    } ->
    related g t2 rel t1 ->
    related_comp (extend_env g x t2)
                 (open_comp_typ c1 x)
                 rel
                 (open_comp_typ c2 x) ->
    related g (mk_arrow_ct t1 q c1) rel (mk_arrow_ct t2 q c2)

  | Rel_abs:
    g:env ->
    t1:term ->
    t2:term ->
    q:aqualv ->
    e1:term ->
    e2:term ->
    x:var{
      None? (lookup_bvar g x) /\ ~ (x `Set.mem` (freevars e1 `Set.union` freevars e2))
    } ->
    related g t1 R_Eq t2 ->
    related (extend_env g x t1)
            (open_or_close_term' e1 (open_with_var x) 0)
            R_Eq
            (open_or_close_term' e2 (open_with_var x) 0) ->
    related g (mk_abs t1 q e1) R_Eq (mk_abs t2 q e2)

and equiv : env -> term -> term -> Type0 =
  | EQ_Refl:
      g:env ->
      t0:term ->
      equiv g t0 t0

  | EQ_Sym:
      g:env ->
      t0:term ->
      t1:term ->
      equiv g t0 t1 ->
      equiv g t1 t0

  | EQ_Trans:
      g:env ->
      t0:term ->
      t1:term ->
      t2:term ->
      equiv g t0 t1 ->
      equiv g t1 t2 ->
      equiv g t0 t2
  
  | EQ_Beta:  // may be e should be ln 0?
      g:env ->
      t:R.typ ->
      q:R.aqualv ->
      e:R.term ->
      arg:R.term ->
      equiv g (R.pack_ln (R.Tv_App (mk_abs t q e) (arg, q)))
              (open_or_close_term' e (OpenWith arg) 0)

  | EQ_Token:
      g:env ->
      t0:term ->
      t1:term ->
      squash (FTB.equiv_token g t0 t1) ->
      equiv g t0 t1

  | EQ_Ctxt:
      g:env ->
      t0:term ->
      t1:term ->
      ctxt:term_ctxt ->
      equiv g t0 t1 ->
      equiv g (apply_term_ctxt ctxt t0) (apply_term_ctxt ctxt t1)

and related_comp : env -> comp_typ -> relation -> comp_typ -> Type0 =
  | Relc_typ:
    g:env ->
    t0:term ->
    t1:term ->
    eff:T.effect_label ->
    rel:relation ->
    related g t0 rel t1 ->
    related_comp g (eff, t0) rel (eff, t1)
  
  | Relc_total_ghost:
    g:env ->
    t:term ->
    related_comp g (T.E_Total, t) R_Sub (T.E_Ghost, t)

  | Relc_ghost_total:
    g:env ->
    t:term ->
    non_informative t ->
    related_comp g (T.E_Ghost, t) R_Sub (T.E_Total, t)

// and branches_typing : env -> term -> term -> list branch -> term -> Type0 =

and sub_typing (g:env) (t1 t2:term) = related g t1 R_Sub t2

and sub_comp (g:env) (c1 c2:comp_typ) = related_comp g c1 R_Sub c2

let bindings = list (var & term)
let rename_bindings bs x y = FStar.List.Tot.map (fun (v, t) -> (v, rename t x y)) bs

let rec extend_env_l (g:env) (bs:bindings) 
  : env
  = match bs with
    | [] -> g
    | (x,t)::bs -> extend_env (extend_env_l g bs) x t

val subtyping_token_renaming (g:env)
                             (bs0:bindings)
                             (bs1:bindings)
                             (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                             (y:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) y) })
                             (t:term)
                             (t0 t1:term)
                             (d:FTB.subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1)
  : FTB.subtyping_token (extend_env_l g (rename_bindings bs1 x y@(y,t)::bs0))
                        (rename t0 x y)
                        (rename t1 x y)

val subtyping_token_weakening (g:env)
                              (bs0:bindings)
                              (bs1:bindings)
                              (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                              (t:term)
                              (t0 t1:term)
                              (d:FTB.subtyping_token (extend_env_l g (bs1@bs0)) t0 t1)
  : FTB.subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1

let simplify_umax (#g:R.env) (#t:R.term) (#u:R.universe)
                  (d:typing g t (T.E_Total, tm_type (u_max u u)))
   : typing g t (T.E_Total, tm_type u)
   = let ue
       : univ_eq (u_max u u) u
       = UN_MaxLeq u u (UNLEQ_Refl u)
     in

     T_Sub _ _ _ _ d (Relc_typ _ _ _ T.E_Total _ (Rel_univ_eq _ _ _ R_Sub ue))

#push-options "--ifuel 2"

let rec ln' (e:term) (n:int)
  : Tot bool (decreases e)
  = match inspect_ln e with
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown 
    | Tv_Var _ -> true
    | Tv_BVar m -> bv_index m <= n
    | Tv_App e1 (e2, _) -> ln' e1 n && ln' e2 n
    | Tv_Abs b body -> 
      ln'_binder b n &&
      ln' body (n + 1)

    | Tv_Arrow b c ->
      ln'_binder b n &&
      ln'_comp c (n + 1)

    | Tv_Refine bv sort f ->
      ln' sort n &&
      ln' f (n + 1)

    | Tv_Uvar _ _ ->
      false
      
    | Tv_Let recf attrs bv ty def body ->
      ln'_terms attrs n &&
      ln' ty n &&
      (if recf then ln' def (n + 1) else ln' def n) &&
      ln' body (n + 1)

    | Tv_Match scr ret brs ->
      ln' scr n &&
      (match ret with
      | None -> true
      | Some m -> ln'_match_returns m n) &&
      ln'_branches brs n
      
    | Tv_AscribedT e t tac b ->
      ln' e n &&
      ln' t n &&
      (match tac with
       | None -> true
       | Some tac -> ln' tac n)
                            
    | Tv_AscribedC e c tac b ->
      ln' e n &&
      ln'_comp c n &&
      (match tac with
       | None -> true
       | Some tac -> ln' tac n)
                            
and ln'_comp (c:comp) (i:int)
  : Tot bool (decreases c)
  = match inspect_comp c with
    | C_Total t
    | C_GTotal t -> ln' t i

    | C_Lemma pre post pats ->
      ln' pre i &&
      ln' post i &&
      ln' pats i

    | C_Eff us eff_name res args decrs ->
      ln' res i &&
      ln'_args args i &&
      ln'_terms decrs i

and ln'_args (ts:list argv) (i:int)
  : Tot bool (decreases ts)
  = match ts with
    | [] -> true
    | (t,q)::ts -> 
      ln' t i &&
      ln'_args ts i

and ln'_binder (b:binder) (n:int)
  : Tot bool (decreases b)
  = let bndr  = inspect_binder b in
    ln' bndr.binder_sort n &&
    ln'_terms bndr.binder_attrs n

and ln'_terms (ts:list term) (n:int)
  : Tot bool (decreases ts)
  = match ts with
    | [] -> true
    | t::ts -> ln' t n && ln'_terms ts n

and ln'_patterns (ps:list (pattern & bool)) (i:int)
  : Tot bool
    (decreases ps)
  = match ps with
    | [] -> true
    | (p, b)::ps ->
      let b0 = ln'_pattern p i in
      let n = binder_offset_pattern p in
      let b1 = ln'_patterns ps (i + n) in
      b0 && b1

and ln'_pattern (p:pattern) (i:int) 
  : Tot bool
        (decreases p)
  = match p with
    | Pat_Constant _ -> true

    | Pat_Cons fv us pats -> 
      ln'_patterns pats i
      
    | Pat_Var bv 
    | Pat_Wild bv -> true


    | Pat_Dot_Term topt ->
      (match topt with
       | None -> true
       | Some t -> ln' t i)
    
and ln'_branch (br:branch) (i:int)
  : Tot bool (decreases br)
  = let p, t = br in
    let b = ln'_pattern p i in
    let j = binder_offset_pattern p in
    let b' = ln' t (i + j) in
    b&&b'
  
and ln'_branches (brs:list branch) (i:int)
  : Tot bool (decreases brs)
  = match brs with
    | [] -> true
    | br::brs -> 
      ln'_branch br i &&
      ln'_branches brs i
  
and ln'_match_returns (m:match_returns_ascription) (i:int)
  : Tot bool (decreases m)
  = let b, (ret, as_, eq) = m in
    let b = ln'_binder b i in
    let ret =
      match ret with
      | Inl t -> ln' t (i + 1)
      | Inr c -> ln'_comp c (i + 1)
    in
    let as_ =
      match as_ with
      | None -> true
      | Some t -> ln' t (i + 1)
    in
    b && ret && as_

let ln (t:term) = ln' t (-1)
let ln_comp (c:comp) = ln'_comp c (-1)

val well_typed_terms_are_ln (g:R.env) (e:R.term) (c:comp_typ) (_:typing g e c)
  : Lemma (ensures ln e /\ ln (snd c))

val type_correctness (g:R.env) (e:R.term) (c:comp_typ) (_:typing g e c)
  : GTot (u:R.universe & typing g (snd c) (T.E_Total, tm_type u))

val binder_offset_pattern_invariant (p:pattern) (s:open_or_close) (i:nat)
  : Lemma (binder_offset_pattern p == binder_offset_pattern (open_or_close_pattern' p s i))

val binder_offset_patterns_invariant (p:list (pattern & bool)) (s:open_or_close) (i:nat)
  : Lemma (binder_offset_patterns p == binder_offset_patterns (open_or_close_patterns' p s i))

val open_close_inverse' (i:nat) (t:term { ln' t (i - 1) }) (x:var)
  : Lemma 
       (ensures open_or_close_term' 
                       (open_or_close_term' t (CloseVar x) i)
                       (open_with_var x)
                       i
                == t)

val open_close_inverse'_binder (i:nat) (b:binder { ln'_binder b (i - 1) }) (x:var)
  : Lemma (ensures open_or_close_binder'
                         (open_or_close_binder' b (CloseVar x) i)
                         (open_with_var x)
                         i
                   == b)

val open_close_inverse'_terms (i:nat) (ts:list term { ln'_terms ts (i - 1) }) (x:var)
  : Lemma (ensures open_or_close_terms' (open_or_close_terms' ts (CloseVar x) i)
                                        (open_with_var x)
                                        i
                   == ts)

val open_close_inverse'_comp (i:nat) (c:comp { ln'_comp c (i - 1) }) (x:var)
  : Lemma 
    (ensures open_or_close_comp' (open_or_close_comp' c (CloseVar x) i)
                              (open_with_var x)
                              i
             == c)

val open_close_inverse'_args (i:nat) 
                            (ts:list argv { ln'_args ts (i - 1) })
                            (x:var)
  : Lemma
    (ensures open_or_close_args' (open_or_close_args' ts (CloseVar x) i)
                                 (open_with_var x)
                                 i
             == ts)

val open_close_inverse'_patterns (i:nat)
                                (ps:list (pattern & bool) { ln'_patterns ps (i - 1) })
                                (x:var)
  : Lemma 
    (ensures open_or_close_patterns' (open_or_close_patterns' ps (CloseVar x) i)
                                     (open_with_var x)
                                     i
             == ps)

val open_close_inverse'_pattern (i:nat) (p:pattern{ln'_pattern p (i - 1)}) (x:var)
  : Lemma 
    (ensures open_or_close_pattern' (open_or_close_pattern' p (CloseVar x) i)
                                    (open_with_var x)
                                      i
             == p)
    
val open_close_inverse'_branch (i:nat) (br:branch{ln'_branch br (i - 1)}) (x:var)
  : Lemma
    (ensures open_or_close_branch'
                 (open_or_close_branch' br (CloseVar x) i)
                 (open_with_var x)
                 i
             == br)
  
val open_close_inverse'_branches (i:nat)
                                (brs:list branch { ln'_branches brs (i - 1) })
                                (x:var)
  : Lemma
    (ensures open_or_close_branches'
                 (open_or_close_branches' brs (CloseVar x) i)
                 (open_with_var x)
                 i
             == brs)
  
val open_close_inverse'_match_returns (i:nat) 
                                     (m:match_returns_ascription { ln'_match_returns m (i - 1) })
                                     (x:var)
  : Lemma 
    (ensures open_or_close_match_returns' 
                 (open_or_close_match_returns' m (CloseVar x) i)
                 (open_with_var x)
                 i
             == m)

val open_close_inverse (e:R.term { ln e }) (x:var)
  : Lemma (open_term (close_term e x) x == e)


val close_open_inverse' (i:nat)
                            (t:term) 
                            (x:var { ~(x `Set.mem` freevars t) })
  : Lemma 
       (ensures open_or_close_term' 
                       (open_or_close_term' t (open_with_var x) i)
                       (CloseVar x)
                       i
                == t)

val close_open_inverse'_comp (i:nat)
                             (c:comp)
                             (x:var{ ~(x `Set.mem` freevars_comp c) })
  : Lemma
       (ensures open_or_close_comp' 
                       (open_or_close_comp' c (open_with_var x) i)
                       (CloseVar x)
                       i
                == c)

val close_open_inverse'_args (i:nat) (args:list argv) (x:var{ ~(x `Set.mem` freevars_args args) })
  : Lemma
       (ensures open_or_close_args' 
                       (open_or_close_args' args (open_with_var x) i)
                       (CloseVar x)
                       i
                == args)

val close_open_inverse'_binder (i:nat) (b:binder) (x:var{ ~(x `Set.mem` freevars_binder b) })
  : Lemma 
       (ensures open_or_close_binder' 
                       (open_or_close_binder' b (open_with_var x) i)
                       (CloseVar x)
                       i
                == b)

val close_open_inverse'_terms (i:nat) (ts:list term) (x:var{ ~(x `Set.mem` freevars_terms ts) })
  : Lemma 
       (ensures open_or_close_terms' 
                       (open_or_close_terms' ts (open_with_var x) i)
                       (CloseVar x)
                       i
                == ts)

val close_open_inverse'_branches (i:nat) (brs:list branch) 
                                 (x:var{ ~(x `Set.mem` freevars_branches brs) })
  : Lemma
    (ensures open_or_close_branches'
                       (open_or_close_branches' brs (open_with_var x) i)
                       (CloseVar x)
                       i
                == brs)

val close_open_inverse'_branch (i:nat)
                               (br:branch)
                               (x:var{ ~(x `Set.mem` freevars_branch br) })
  : Lemma
    (ensures open_or_close_branch'
                       (open_or_close_branch' br (open_with_var x) i)
                       (CloseVar x)
                       i
                == br)

val close_open_inverse'_pattern (i:nat)
                                (p:pattern)
                                (x:var{ ~(x `Set.mem` freevars_pattern p) })
  : Lemma
    (ensures open_or_close_pattern'
                       (open_or_close_pattern' p (open_with_var x) i)
                       (CloseVar x)
                       i
                == p)

val close_open_inverse'_patterns (i:nat)
                                 (ps:list (pattern & bool))
                                 (x:var {~ (x `Set.mem` freevars_patterns ps) })
  : Lemma 
    (ensures open_or_close_patterns' (open_or_close_patterns' ps (open_with_var x) i)
                                     (CloseVar x)
                                     i
             == ps)

val close_open_inverse'_match_returns (i:nat) (m:match_returns_ascription)
                                      (x:var{ ~(x `Set.mem` freevars_match_returns m) })
  : Lemma
    (ensures open_or_close_match_returns'
                       (open_or_close_match_returns' m (open_with_var x) i)
                       (CloseVar x)
                       i
                == m)

val close_open_inverse (e:R.term) (x:var {~ (x `Set.mem` freevars e) })
  : Lemma (close_term (open_term e x) x == e)

//
// fst has corresponding lemmas for other syntax classes
//
val close_with_not_free_var (t:R.term) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars t)))
      (ensures open_or_close_term' t (CloseVar x) i == t)

// may be it should require e1 and e2 to be ln at 0,
//   and x not in FV e1 and FV e2
val equiv_abs (#g:R.env) (#e1 #e2:R.term) (ty:R.typ) (q:R.aqualv)
  (x:var{None? (lookup_bvar g x)})
  (eq:equiv (extend_env g x ty)
            (open_or_close_term' e1 (open_with_var x) 0)
            (open_or_close_term' e2 (open_with_var x) 0))
  : equiv g (mk_abs ty q e1)
            (mk_abs ty q e2)

val equiv_arrow (#g:R.env) (#e1 #e2:R.term) (ty:R.typ) (q:R.aqualv)
  (x:var{None? (lookup_bvar g x)})
  (eq:equiv (extend_env g x ty)
            (open_or_close_term' e1 (open_with_var x) 0)
            (open_or_close_term' e2 (open_with_var x) 0))
  : equiv g (mk_arrow ty q e1)
            (mk_arrow ty q e2)

// the proof for this requires e1 and e2 to be ln
val equiv_abs_close (#g:R.env) (#e1 #e2:R.term) (ty:R.typ) (q:R.aqualv)
  (x:var{None? (lookup_bvar g x)})
  (eq:equiv (extend_env g x ty) e1 e2)
  : equiv g (mk_abs ty q (open_or_close_term' e1 (CloseVar x) 0))
            (mk_abs ty q (open_or_close_term' e2 (CloseVar x) 0))

val open_with_gt_ln (e:term) (i:nat) (t:term) (j:nat)
  : Lemma
      (requires ln' e i /\ i < j)
      (ensures open_or_close_term' e (OpenWith t) j == e)
      [SMTPat (ln' e i); SMTPat (open_or_close_term' e (OpenWith t) j)]

//
// Type of the top-level tactic that would splice-in the definitions
//

let fstar_env_fvs (g:R.env) =
  lookup_fvar g unit_fv == Some (tm_type u_zero) /\
  lookup_fvar g bool_fv == Some (tm_type u_zero) /\
  lookup_fvar g b2t_fv  == Some b2t_ty

type fstar_env = g:R.env{fstar_env_fvs g}

type fstar_top_env = g:fstar_env {
  forall x. None? (lookup_bvar g x )
}

//
// This doesn't allow for universe polymorphic definitions
//
// May be we can change it to:
//
// g:fstar_top_env -> T.tac ((us, e, t):(univ_names & term & typ){typing (push g us) e t})
//

type dsl_tac_t = g:fstar_top_env -> T.Tac (r:(R.term & R.typ){typing g (fst r) (T.E_Total, snd r)})
