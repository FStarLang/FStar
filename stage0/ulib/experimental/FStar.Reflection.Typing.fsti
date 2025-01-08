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
open FStar.Reflection.V2
module L = FStar.List.Tot
module R = FStar.Reflection.V2
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.Tactics.Types
open FStar.Tactics.Effect
module RD = FStar.Stubs.Reflection.V2.Data

(* MOVE to some helper module *)
let rec fold_left_dec #a #b
  (acc : a)
  (l : list b)
  (f : a -> (x:b{x << l}) -> a)
  : Tot a (decreases l)
  =
  match l with
  | [] -> acc
  | x::xs -> fold_left_dec (f acc x) xs f

let rec map_dec #a #b
  (l : list a)
  (f : (x:a{x << l}) -> b)
  : Tot (list b) (decreases l)
  =
  match l with
  | [] -> []
  | x::xs -> f x :: map_dec xs f

let rec zip2prop #a #b (f : a -> b -> Type0) (xs : list a) (ys : list b) : Type0 =
  match xs, ys with
  | [], [] -> True
  | x::xx, y::yy -> f x y /\ zip2prop f xx yy
  | _ -> False
(* / MOVE *)

val inspect_pack (t:R.term_view)
  : Lemma (ensures R.(inspect_ln (pack_ln t) == t))
          [SMTPat R.(inspect_ln (pack_ln t))]
  
val pack_inspect (t:R.term)
  : Lemma (requires ~(Tv_Unsupp? (inspect_ln t)))
          (ensures R.(pack_ln (inspect_ln t) == t))
          [SMTPat R.(pack_ln (inspect_ln t))]
  
val inspect_pack_namedv (t:R.namedv_view)
  : Lemma (ensures R.(inspect_namedv (pack_namedv t) == t))
          [SMTPat R.(inspect_namedv (pack_namedv t))]

val pack_inspect_namedv (t:R.namedv)
  : Lemma (ensures R.(pack_namedv (inspect_namedv t) == t))
          [SMTPat R.(pack_namedv (inspect_namedv t))]

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
  
val inspect_pack_comp (t:R.comp_view)
  : Lemma (ensures (R.inspect_comp (R.pack_comp t) == t))
          [SMTPat (R.inspect_comp (R.pack_comp t))]

val pack_inspect_comp (t:R.comp)
  : Lemma (ensures (R.pack_comp (R.inspect_comp t) == t))
          [SMTPat (R.pack_comp (R.inspect_comp t))]
  
val inspect_pack_fv (nm:R.name)
  : Lemma (ensures R.inspect_fv (R.pack_fv nm) == nm)
          [SMTPat (R.inspect_fv (R.pack_fv nm))]

val pack_inspect_fv (fv:R.fv)
  : Lemma (ensures R.pack_fv (R.inspect_fv fv) == fv)
          [SMTPat (R.pack_fv (R.inspect_fv fv))]

val inspect_pack_universe (u:R.universe_view)
  : Lemma (ensures R.inspect_universe (R.pack_universe u) == u)
          [SMTPat (R.inspect_universe (R.pack_universe u))]

val pack_inspect_universe (u:R.universe)
  : Lemma (requires ~(Uv_Unk? (inspect_universe u)))
          (ensures R.pack_universe (R.inspect_universe u) == u)
          [SMTPat (R.pack_universe (R.inspect_universe u))]

val inspect_pack_lb (lb:R.lb_view)
  : Lemma (ensures R.inspect_lb (R.pack_lb lb) == lb)
          [SMTPat (R.inspect_lb (R.pack_lb lb))]

val pack_inspect_lb (lb:R.letbinding)
  : Lemma (ensures R.pack_lb (R.inspect_lb lb) == lb)
          [SMTPat (R.pack_lb (R.inspect_lb lb))]

val inspect_pack_sigelt (sev:R.sigelt_view { ~ (Unk? sev) })
  : Lemma (ensures R.inspect_sigelt (R.pack_sigelt sev) == sev)
          [SMTPat (R.inspect_sigelt (R.pack_sigelt sev))]

val pack_inspect_sigelt (se:R.sigelt)
  : Lemma (requires ~ (Unk? (R.inspect_sigelt se)))
          (ensures R.pack_sigelt (R.inspect_sigelt se) == se)
          [SMTPat (R.pack_sigelt (R.inspect_sigelt se))]

val lookup_bvar (e:env) (x:int) : option term

val lookup_fvar_uinst (e:R.env) (x:R.fv) (us:list R.universe) : option R.term

let lookup_fvar (e:env) (x:fv) : option term = lookup_fvar_uinst e x []

let pp_name_t = FStar.Sealed.Inhabited.sealed "x"
let pp_name_default : pp_name_t = FStar.Sealed.Inhabited.seal "x"
let seal_pp_name x : pp_name_t = FStar.Sealed.Inhabited.seal x

let tun = pack_ln Tv_Unknown

let sort_t = FStar.Sealed.Inhabited.sealed tun
let sort_default : sort_t = FStar.Sealed.Inhabited.seal tun
let seal_sort x : sort_t = FStar.Sealed.Inhabited.seal x

let mk_binder (pp_name:pp_name_t) (ty:term) (q:aqualv) : binder
  = pack_binder
      { ppname = pp_name;
        qual   = q;
        attrs  = [];
        sort   = ty}

let mk_simple_binder (pp_name:pp_name_t) (ty:term) : simple_binder
  = pack_binder
      { ppname = pp_name;
        qual   = Q_Explicit;
        attrs  = [];
        sort   = ty}

let extend_env (e:env) (x:var) (ty:term) : env =
  R.push_binding e ({
    ppname = seal_pp_name "x";
    uniq   = x;
    sort   = ty;
  })
  
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

let bv_index (x:bv)
  : var
  = (inspect_bv x).index

let namedv_uniq (x:namedv)
  : var
  = (inspect_namedv x).uniq

let binder_sort (b:binder) =
  (inspect_binder b).sort

let binder_qual (b:binder) =
  let { qual = q } = inspect_binder b in q

noeq
type subst_elt =
  | DT : nat -> term -> subst_elt
  | NT : var -> term -> subst_elt
  | ND : var -> nat -> subst_elt

let shift_subst_elt (n:nat) = function
  | DT i t -> DT (i + n) t
  | NT x t -> NT x t
  | ND x i -> ND x (i + n)

let subst = list subst_elt

let shift_subst_n (n:nat) = L.map (shift_subst_elt n)

let shift_subst = shift_subst_n 1

let maybe_uniq_of_term (x:term) =
  match inspect_ln x with
  | Tv_Var namedv -> Some (namedv_uniq namedv)
  | _ -> None

let rec find_matching_subst_elt_bv (s:subst) (bv:bv) : option subst_elt =
  match s with
  | [] -> None
  | (DT j t)::ss ->
    if j = bv_index bv
    then Some (DT j t)
    else find_matching_subst_elt_bv ss bv
  | _::ss -> find_matching_subst_elt_bv ss bv

let subst_db (bv:bv) (s:subst) : term =
  match find_matching_subst_elt_bv s bv with
  | Some (DT _ t) ->
    (match maybe_uniq_of_term t with
     | None -> t
     | Some k ->
       //if we're substituting a name j for a name k, retain the pp_name of j
       let v : namedv = pack_namedv {
         sort = (inspect_bv bv).sort;
         ppname = (inspect_bv bv).ppname;
         uniq = k;
       } in
       pack_ln (Tv_Var v))
  | _ -> pack_ln (Tv_BVar bv)

let rec find_matching_subst_elt_var (s:subst) (v:namedv) : option subst_elt =
  match s with
  | [] -> None
  | (NT y _)::rest 
  | (ND y _)::rest ->
    if y = namedv_uniq v
    then Some (L.hd s)
    else find_matching_subst_elt_var rest v
  | _::rest -> find_matching_subst_elt_var rest v

let subst_var (v:namedv) (s:subst) : term =
  match find_matching_subst_elt_var s v with
  | Some (NT _ t) ->
    (match maybe_uniq_of_term t with
     | None -> t
     | Some k ->
       pack_ln (Tv_Var (pack_namedv { inspect_namedv v with uniq = k })))
  | Some (ND _ i) ->
    let bv = pack_bv {
      sort = (inspect_namedv v).sort;
      ppname = (inspect_namedv v).ppname;
      index = i;
    } in
    pack_ln (Tv_BVar bv)
  | _ -> pack_ln (Tv_Var v)

let make_bv (n:nat) : bv_view = {
  ppname = pp_name_default;
  index = n;
  sort = sort_default;
}
let make_bv_with_name (s:pp_name_t) (n:nat) : bv_view = {
  ppname = s;
  index  = n;
  sort   = sort_default;
}


let var_as_bv (v:nat) = pack_bv (make_bv v)

let make_namedv (n:nat) : namedv_view = {
  ppname = pp_name_default;
  uniq   = n;
  sort   = sort_default;
}

let make_namedv_with_name (s:pp_name_t) (n:nat) : namedv_view = {
  ppname = s;
  uniq   = n;
  sort   = sort_default;
}

let var_as_namedv (v:nat) : namedv =
  pack_namedv {
    uniq = v;
    sort = sort_default;
    ppname = pp_name_default;
  }

let var_as_term (v:var) = pack_ln (Tv_Var (var_as_namedv v))

let binder_of_t_q t q = mk_binder pp_name_default t q
let mk_abs ty qual t : R.term =  R.pack_ln (R.Tv_Abs (binder_of_t_q ty qual) t)
let mk_total t = pack_comp (C_Total t)
let mk_ghost t = pack_comp (C_GTotal t)
let mk_arrow ty qual t : R.term =
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty qual) (mk_total t))
let mk_ghost_arrow ty qual t : R.term =
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty qual) (mk_ghost t))
let bound_var i : R.term = R.pack_ln (R.Tv_BVar (R.pack_bv (make_bv i)))
let mk_let ppname (e1 t1 e2:R.term) =
  R.pack_ln (R.Tv_Let false [] (mk_simple_binder ppname t1) e1 e2)

let open_with_var_elt (x:var) (i:nat) : subst_elt =
  DT i (pack_ln (Tv_Var (var_as_namedv x)))
let open_with_var (x:var) (i:nat) : subst = [open_with_var_elt x i]

val subst_ctx_uvar_and_subst (c:ctx_uvar_and_subst) (ss:subst) 
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

    | Pat_Var _ _ -> 1

    | Pat_Cons head univs subpats ->
      binder_offset_patterns subpats

let rec subst_term (t:term) (ss:subst)
  : Tot term (decreases t)
  = match inspect_ln t with
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unsupp
    | Tv_Unknown -> t
    | Tv_Var x -> subst_var x ss
    | Tv_BVar j -> subst_db j ss
    | Tv_App hd argv ->
      pack_ln (Tv_App (subst_term hd ss)
                      (subst_term (fst argv) ss, snd argv))

    | Tv_Abs b body -> 
      let b' = subst_binder b ss in
      pack_ln (Tv_Abs b' (subst_term body (shift_subst ss)))

    | Tv_Arrow b c ->
      let b' = subst_binder b ss in
      pack_ln (Tv_Arrow b' (subst_comp c (shift_subst ss)))      

    | Tv_Refine b f ->
      let b = subst_binder b ss in
      pack_ln (Tv_Refine b (subst_term f (shift_subst ss)))

    | Tv_Uvar j c ->
      pack_ln (Tv_Uvar j (subst_ctx_uvar_and_subst c ss))
      
    | Tv_Let recf attrs b def body ->
      let b = subst_binder b ss in
      pack_ln (Tv_Let recf 
                      (subst_terms attrs ss)
                      b
                      (if recf 
                       then subst_term def (shift_subst ss)
                       else subst_term def ss)
                      (subst_term body (shift_subst ss)))

    | Tv_Match scr ret brs ->
      pack_ln (Tv_Match (subst_term scr ss)
                        (match ret with
                         | None -> None
                         | Some m -> Some (subst_match_returns m ss))
                        (subst_branches brs ss))
      
    | Tv_AscribedT e t tac b ->
      pack_ln (Tv_AscribedT (subst_term e ss)
                            (subst_term t ss)
                            (match tac with
                             | None -> None
                             | Some tac -> Some (subst_term tac ss))
                             b)

    | Tv_AscribedC e c tac b ->
      pack_ln (Tv_AscribedC (subst_term e ss)
                            (subst_comp c ss)
                            (match tac with
                             | None -> None
                             | Some tac -> Some (subst_term tac ss))
                             b)

and subst_binder (b:binder) (ss:subst)
  : Tot (b':binder{binder_is_simple b ==> binder_is_simple b'}) (decreases b)
  = let bndr  = inspect_binder b in
    pack_binder {
      ppname = bndr.ppname;
      qual   = bndr.qual;
      attrs  = subst_terms bndr.attrs ss;
      sort   = subst_term bndr.sort ss
    }

and subst_comp (c:comp) (ss:subst)
  : Tot comp (decreases c)
  = match inspect_comp c with
    | C_Total t ->
      pack_comp (C_Total (subst_term t ss))

    | C_GTotal t ->
      pack_comp (C_GTotal (subst_term t ss))

    | C_Lemma pre post pats ->
      pack_comp (C_Lemma (subst_term pre ss)
                         (subst_term post ss)
                         (subst_term pats ss))

    | C_Eff us eff_name res args decrs ->
      pack_comp (C_Eff us eff_name
                       (subst_term res ss)
                       (subst_args args ss)
                       (subst_terms decrs ss))

and subst_terms (ts:list term) (ss:subst)
  : Tot (ts':list term{Nil? ts ==> Nil? ts'}) // property useful for subst_binder
        (decreases ts)
  = match ts with
    | [] -> []
    | t::ts -> subst_term t ss :: subst_terms ts ss

and subst_args (ts:list argv) (ss:subst)
  : Tot (list argv) (decreases ts)
  = match ts with
    | [] -> []
    | (t,q)::ts -> (subst_term t ss,q) :: subst_args ts ss

and subst_patterns (ps:list (pattern & bool)) (ss:subst) 
  : Tot (list (pattern & bool))
         (decreases ps)
  = match ps with
    | [] -> ps
    | (p, b)::ps ->
      let n = binder_offset_pattern p in
      let p = subst_pattern p ss in
      let ps = subst_patterns ps (shift_subst_n n ss) in
      (p,b)::ps

and subst_pattern (p:pattern) (ss:subst) 
  : Tot pattern
         (decreases p)
  = match p with
    | Pat_Constant _ -> p

    | Pat_Cons fv us pats -> 
      let pats = subst_patterns pats ss in
      Pat_Cons fv us pats

    | Pat_Var bv s ->
      Pat_Var bv s

    | Pat_Dot_Term topt ->
      Pat_Dot_Term (match topt with
                    | None -> None
                    | Some t -> Some (subst_term t ss))

    
and subst_branch (br:branch) (ss:subst)
  : Tot branch (decreases br)
  = let p, t = br in
    let p = subst_pattern p ss in
    let j = binder_offset_pattern p in
    let t = subst_term t (shift_subst_n j ss) in
    p, t
  
and subst_branches (brs:list branch) (ss:subst)
  : Tot (list branch) (decreases brs)
  = match brs with
    | [] -> []
    | br::brs -> subst_branch br ss :: subst_branches brs ss
  
and subst_match_returns (m:match_returns_ascription) (ss:subst)
  : Tot match_returns_ascription (decreases m)
  = let b, (ret, as_, eq) = m in
    let b = subst_binder b ss in
    let ret =
      match ret with
      | Inl t -> Inl (subst_term t (shift_subst ss))
      | Inr c -> Inr (subst_comp c (shift_subst ss))
    in
    let as_ =
      match as_ with
      | None -> None
      | Some t -> Some (subst_term t (shift_subst ss))
    in
    b, (ret, as_, eq)

val open_with (t:term) (v:term) : term

val open_with_spec (t v:term)
  : Lemma (open_with t v ==
           subst_term t [ DT 0 v ])

val open_term (t:term) (v:var) : term

val open_term_spec (t:term) (v:var)
  : Lemma (open_term t v ==
           subst_term t (open_with_var v 0))
  
val close_term (t:term) (v:var) : term

val close_term_spec (t:term) (v:var)
  : Lemma (close_term t v ==
           subst_term t [ ND v 0 ])

val rename (t:term) (x y:var) : term

val rename_spec (t:term) (x y:var)
  : Lemma (rename t x y ==
           subst_term t [ NT x (var_as_term y)])
  
val bv_index_of_make_bv (n:nat)
  : Lemma (ensures bv_index (pack_bv (make_bv n)) == n)
          [SMTPat (bv_index (pack_bv (make_bv n)))]

val namedv_uniq_of_make_namedv (n:nat)
  : Lemma (ensures namedv_uniq (pack_namedv (make_namedv n)) == n)
          [SMTPat (namedv_uniq (pack_namedv (make_namedv n)))]

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
let b2t_ty : R.term = R.pack_ln (R.Tv_Arrow (mk_binder (seal "x") bool_ty Q_Explicit) (mk_total (tm_type u_zero)))


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
    | Tv_Unsupp
    | Tv_BVar _ -> Set.empty

    | Tv_Var x -> Set.singleton (namedv_uniq x)
       
    | Tv_App e1 (e2, _) ->
      Set.union (freevars e1) (freevars e2)

    | Tv_Abs b body -> 
      Set.union (freevars_binder b) (freevars body)

    | Tv_Arrow b c ->
      Set.union (freevars_binder b) (freevars_comp c)

    | Tv_Refine b f ->
       freevars (binder_sort b) `Set.union`
       freevars f
      
    | Tv_Let recf attrs b def body ->
      freevars_terms attrs `Set.union`
      freevars (binder_sort b) `Set.union`
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
    freevars bndr.sort `Set.union`
    freevars_terms bndr.attrs 

and freevars_pattern (p:pattern) 
  : Tot (Set.set var) (decreases p)
  = match p with
    | Pat_Constant _ ->
      Set.empty

    | Pat_Cons head univs subpats ->
      freevars_patterns subpats
      
    | Pat_Var bv s -> Set.empty

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


let rec ln' (e:term) (n:int)
  : Tot bool (decreases e)
  = match inspect_ln e with
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown 
    | Tv_Unsupp
    | Tv_Var _ -> true
    | Tv_BVar m -> bv_index m <= n
    | Tv_App e1 (e2, _) -> ln' e1 n && ln' e2 n
    | Tv_Abs b body -> 
      ln'_binder b n &&
      ln' body (n + 1)

    | Tv_Arrow b c ->
      ln'_binder b n &&
      ln'_comp c (n + 1)

    | Tv_Refine b f ->
      ln'_binder b n &&
      ln' f (n + 1)

    | Tv_Uvar _ _ ->
      false
      
    | Tv_Let recf attrs b def body ->
      ln'_terms attrs n &&
      ln'_binder b n &&
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
    ln' bndr.sort n &&
    ln'_terms bndr.attrs n

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

    | Pat_Cons head univs subpats ->
      ln'_patterns subpats i
      
    | Pat_Var bv s -> true

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
type comp_typ = FStar.Stubs.Tactics.Types.tot_or_ghost & typ

let close_comp_typ' (c:comp_typ) (x:var) (i:nat) =
  fst c, subst_term (snd c) [ ND x i ]

let close_comp_typ (c:comp_typ) (x:var) =
  close_comp_typ' c x 0

let open_comp_typ' (c:comp_typ) (x:var) (i:nat) =
  fst c, subst_term (snd c) (open_with_var x i)

let open_comp_typ (c:comp_typ) (x:var) =
  open_comp_typ' c x 0

let freevars_comp_typ (c:comp_typ) = freevars (snd c)

let mk_comp (c:comp_typ) : R.comp =
  match fst c with
  | E_Total -> mk_total (snd c)
  | E_Ghost -> mk_ghost (snd c)

let mk_arrow_ct ty qual (c:comp_typ) : R.term =
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty qual) (mk_comp c))
 
type relation =
  | R_Eq
  | R_Sub

let binding = var & term
let bindings = list binding
let rename_bindings bs x y = FStar.List.Tot.map (fun (v, t) -> (v, rename t x y)) bs

let rec extend_env_l (g:env) (bs:bindings)
  : env
  = match bs with
    | [] -> g
    | (x,t)::bs -> extend_env (extend_env_l g bs) x t

//
// TODO: support for erasable attribute
//
let is_non_informative_name (l:name) : bool =
  l = R.unit_lid ||
  l = R.squash_qn ||
  l = ["FStar"; "Ghost"; "erased"]

let is_non_informative_fv (f:fv) : bool =
  is_non_informative_name (inspect_fv f)

let rec __close_term_vs (i:nat) (vs : list var) (t : term) : Tot term (decreases vs) =
  match vs with
  | [] -> t
  | v::vs ->
    subst_term (__close_term_vs (i+1) vs t) [ND v i]

let close_term_vs (vs : list var) (t : term) : term =
  __close_term_vs 0 vs t

let close_term_bs (bs : list binding) (t : term) : term =
  close_term_vs (List.Tot.map fst bs) t

let bindings_to_refl_bindings (bs : list binding) : list R.binding =
  L.map (fun (v, ty) -> {uniq=v; sort=ty; ppname = pp_name_default}) bs

let refl_bindings_to_bindings (bs : list R.binding) : list binding =
  L.map (fun b -> b.uniq, b.sort) bs

[@@ no_auto_projectors]
noeq
type non_informative : env -> term -> Type0 =
  | Non_informative_type:
    g:env ->
    u:universe ->
    non_informative g (pack_ln (Tv_Type u))
  
  | Non_informative_fv:
    g:env ->
    x:fv{is_non_informative_fv x} ->
    non_informative g (pack_ln (Tv_FVar x))
  
  | Non_informative_uinst:
    g:env ->
    x:fv{is_non_informative_fv x} ->
    us:list universe ->
    non_informative g (pack_ln (Tv_UInst x us))

  | Non_informative_app:
    g:env ->
    t:term ->
    arg:argv ->
    non_informative g t ->
    non_informative g (pack_ln (Tv_App t arg))

  | Non_informative_total_arrow:
    g:env ->
    t0:term ->
    q:aqualv ->
    t1:term ->
    non_informative g t1 ->
    non_informative g (mk_arrow_ct t0 q (E_Total, t1))
  
  | Non_informative_ghost_arrow:
    g:env ->
    t0:term ->
    q:aqualv ->
    t1:term ->
    non_informative g (mk_arrow_ct t0 q (E_Ghost, t1))

  | Non_informative_token:
    g:env ->
    t:typ ->
    squash (non_informative_token g t) ->
    non_informative g t

val bindings_ok_for_pat : env -> list R.binding -> pattern -> Type0

val bindings_ok_pat_constant :
  g:env -> c:R.vconst -> Lemma (bindings_ok_for_pat g [] (Pat_Constant c))

let bindings_ok_for_branch (g:env) (bs : list R.binding) (br : branch) : Type0 =
  bindings_ok_for_pat g bs (fst br)

let bindings_ok_for_branch_N (g:env) (bss : list (list R.binding)) (brs : list branch) =
  zip2prop (bindings_ok_for_branch g) bss brs

let binding_to_namedv (b:R.binding) : Tot namedv =
  pack_namedv {
    RD.uniq   = b.uniq;
    RD.sort   = seal b.sort;
    RD.ppname = b.ppname;
  }

(* Elaborates the p pattern into a term, using the bs bindings for the
pattern variables. The resulting term is properly scoped only on an
environment which contains all of bs. See for instance the branch_typing
judg. Returns an option, since this can fail if e.g. there are not
enough bindings, and returns the list of unused binders as well, which
should be empty if the list of binding was indeed ok. *)
let rec elaborate_pat (p : pattern) (bs : list R.binding) : Tot (option (term & list R.binding)) (decreases p) =
  match p, bs with
  | Pat_Constant c, _ -> Some (pack_ln (Tv_Const c), bs)
  | Pat_Cons fv univs subpats, bs ->
    let head =
      match univs with
      | Some univs -> pack_ln (Tv_UInst fv univs)
      | None -> pack_ln (Tv_FVar fv)
    in
    fold_left_dec
      (Some (head, bs))
      subpats
      (fun st pi ->
        let (p,i) = pi in
        match st with | None -> None | Some (head, bs) ->
          match elaborate_pat p bs with | None -> None | Some (t, bs') -> Some (pack_ln (Tv_App head (t, (if i then Q_Implicit else Q_Explicit))), bs'))

  | Pat_Var _ _, b::bs ->
    Some (pack_ln (Tv_Var (binding_to_namedv b)), bs)
  | Pat_Dot_Term (Some t), _ -> Some (t, bs)
  | Pat_Dot_Term None, _ -> None
  | _ -> None

[@@ no_auto_projectors]
noeq
type typing : env -> term -> comp_typ -> Type0 =
  | T_Token :
    g:env ->
    e:term ->
    c:comp_typ ->
    squash (typing_token g e c) ->
    typing g e c

  | T_Var : 
     g:env ->
     x:namedv { Some? (lookup_bvar g (namedv_uniq x)) } ->
     typing g (pack_ln (Tv_Var x)) (E_Total, Some?.v (lookup_bvar g (namedv_uniq x)))

  | T_FVar :
     g:env ->
     x:fv { Some? (lookup_fvar g x) } -> 
     typing g (pack_ln (Tv_FVar x)) (E_Total, Some?.v (lookup_fvar g x))

  | T_UInst :
     g:env ->
     x:fv ->
     us:list universe { Some? (lookup_fvar_uinst g x us) } ->
     typing g (pack_ln (Tv_UInst x us)) (E_Total, Some?.v (lookup_fvar_uinst g x us))

  | T_Const:
     g:env ->
     v:vconst ->
     t:term ->
     constant_typing v t ->
     typing g (constant_as_term v) (E_Total, t)

  | T_Abs :
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     ty:term ->
     body:term { ~(x `Set.mem` freevars body) } ->
     body_c:comp_typ ->
     u:universe ->
     pp_name:pp_name_t ->
     q:aqualv ->
     ty_eff:tot_or_ghost ->
     typing g ty (ty_eff, tm_type u) ->
     typing (extend_env g x ty) (open_term body x) body_c ->
     typing g (pack_ln (Tv_Abs (mk_binder pp_name ty q) body))
              (E_Total,
               pack_ln (Tv_Arrow (mk_binder pp_name ty q)
                                 (mk_comp (close_comp_typ body_c x))))

  | T_App :
     g:env ->
     e1:term ->
     e2:term ->
     x:binder ->
     t:term ->
     eff:tot_or_ghost ->
     typing g e1 (eff, pack_ln (Tv_Arrow x (mk_comp (eff, t)))) ->
     typing g e2 (eff, binder_sort x) ->
     typing g (pack_ln (Tv_App e1 (e2, binder_qual x)))
              (eff, open_with t e2)

  | T_Let:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     e1:term ->
     t1:typ ->
     e2:term ->
     t2:typ ->
     eff:tot_or_ghost ->
     pp_name:pp_name_t ->
     typing g e1 (eff, t1) ->
     typing (extend_env g x t1) (open_term e2 x) (eff, t2) ->
     typing g (mk_let pp_name e1 t1 e2) (eff, open_with (close_term t2 x) e1)

  | T_Arrow:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     t1:term ->
     t2:term { ~(x `Set.mem` freevars t2) } ->
     u1:universe ->
     u2:universe ->
     pp_name:pp_name_t ->
     q:aqualv ->
     eff:tot_or_ghost ->
     t1_eff:tot_or_ghost ->
     t2_eff:tot_or_ghost ->
     typing g t1 (t1_eff, tm_type u1) ->
     typing (extend_env g x t1) (open_term t2 x) (t2_eff, tm_type u2) ->
     typing g (pack_ln (Tv_Arrow (mk_binder pp_name t1 q) (mk_comp (eff, t2))))
              (E_Total, tm_type (u_max u1 u2))

  | T_Refine:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->     
     t:term ->
     e:term { ~(x `Set.mem` freevars e) } ->
     u1:universe ->
     u2:universe ->
     t_eff:tot_or_ghost ->
     e_eff:tot_or_ghost ->
     typing g t (t_eff, tm_type u1) ->
     typing (extend_env g x t) (open_term e x) (e_eff, tm_type u2) ->
     typing g (pack_ln (Tv_Refine (mk_simple_binder pp_name_default t) e)) (E_Total, tm_type u1)

  | T_PropIrrelevance:
     g:env -> 
     e:term -> 
     t:term ->
     e_eff:tot_or_ghost ->
     t_eff:tot_or_ghost ->
     typing g e (e_eff, t) ->
     typing g t (t_eff, tm_prop) ->
     typing g (`()) (E_Total, t)
     
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
     eff:tot_or_ghost ->
     ty_eff:tot_or_ghost ->
     typing g scrutinee (eff, bool_ty) ->
     typing (extend_env g hyp (eq2 (pack_universe Uv_Zero) bool_ty scrutinee true_bool)) then_ (eff, ty) ->
     typing (extend_env g hyp (eq2 (pack_universe Uv_Zero) bool_ty scrutinee false_bool)) else_ (eff, ty) ->
     typing g ty (ty_eff, tm_type u_ty) -> //typedness of ty cannot rely on hyp
     typing g (mk_if scrutinee then_ else_) (eff, ty)

  | T_Match:
     g:env ->
     sc_u : universe ->
     sc_ty : typ ->
     sc : term ->
     ty_eff:tot_or_ghost ->
     typing g sc_ty (ty_eff, tm_type sc_u) ->
     eff:tot_or_ghost ->
     typing g sc (eff, sc_ty) ->
     branches:list branch ->
     ty:comp_typ ->
     bnds:list (list R.binding) ->
     complet : match_is_complete g sc sc_ty (List.Tot.map fst branches) bnds -> // complete patterns
     branches_typing g sc_u sc_ty sc ty branches bnds -> // each branch has proper type
     typing g (pack_ln (Tv_Match sc None branches)) ty

and related : env -> term -> relation -> term -> Type0 =
  | Rel_refl:
    g:env ->
    t:term ->
    rel:relation ->
    related g t rel t

  | Rel_sym:
    g:env ->
    t0:term ->
    t1:term ->
    related g t0 R_Eq t1 ->
    related g t1 R_Eq t0

  | Rel_trans:
    g:env ->
    t0:term ->
    t1:term ->
    t2:term ->
    rel:relation ->
    related g t0 rel t1 ->
    related g t1 rel t2 ->
    related g t0 rel t2

  | Rel_univ:
    g:env ->
    u:universe ->
    v:universe ->
    univ_eq u v ->
    related g (tm_type u) R_Eq (tm_type v)

  | Rel_beta:
    g:env ->
    t:typ ->
    q:aqualv ->
    e:term { ln' e 0 } ->
    arg:term { ln arg } ->
    related g (R.pack_ln (R.Tv_App (mk_abs t q e) (arg, q)))
            R_Eq
            (subst_term e [ DT 0 arg ])

  | Rel_eq_token:
    g:env ->
    t0:term ->
    t1:term ->
    squash (equiv_token g t0 t1) ->
    related g t0 R_Eq t1 

  | Rel_subtyping_token:
    g:env ->
    t0:term ->
    t1:term ->
    squash (subtyping_token g t0 t1) ->
    related g t0 R_Sub t1

  | Rel_equiv:
    g:env ->
    t0:term ->
    t1:term ->
    rel:relation ->
    related g t0 R_Eq t1 ->
    related g t0 rel t1

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
            (subst_term e1 (open_with_var x 0))
            R_Eq
            (subst_term e2 (open_with_var x 0)) ->
    related g (mk_abs t1 q e1) R_Eq (mk_abs t2 q e2)

  | Rel_ctxt:
    g:env ->
    t0:term ->
    t1:term ->
    ctxt:term_ctxt ->
    related g t0 R_Eq t1 ->
    related g (apply_term_ctxt ctxt t0) R_Eq (apply_term_ctxt ctxt t1)

and related_comp : env -> comp_typ -> relation -> comp_typ -> Type0 =
  | Relc_typ:
    g:env ->
    t0:term ->
    t1:term ->
    eff:tot_or_ghost ->
    rel:relation ->
    related g t0 rel t1 ->
    related_comp g (eff, t0) rel (eff, t1)
  
  | Relc_total_ghost:
    g:env ->
    t:term ->
    related_comp g (E_Total, t) R_Sub (E_Ghost, t)

  | Relc_ghost_total:
    g:env ->
    t:term ->
    non_informative g t ->
    related_comp g (E_Ghost, t) R_Sub (E_Total, t)

and branches_typing (g:env) (sc_u:universe) (sc_ty:typ) (sc:term) (rty:comp_typ)
  : (brs:list branch) -> (bnds : list (list R.binding)) -> Type0
=
  (* This judgement only enforces that branch_typing holds for every
  element of brs and its respective bnds (which must have the same
  length). *)

  | BT_Nil :
    branches_typing g sc_u sc_ty sc rty [] []

  | BT_S :

    br : branch ->
    bnds : list R.binding ->
    pf : branch_typing g sc_u sc_ty sc rty br bnds ->

    rest_br : list branch ->
    rest_bnds : list (list R.binding) ->
    rest : branches_typing g sc_u sc_ty sc rty rest_br rest_bnds ->
    branches_typing g sc_u sc_ty sc rty (br :: rest_br) (bnds :: rest_bnds)

and branch_typing (g:env) (sc_u:universe) (sc_ty:typ) (sc:term) (rty:comp_typ)
  : (br : branch) -> (bnds : list R.binding) -> Type0
=
  | BO :
    pat : pattern ->
    bnds : list R.binding{bindings_ok_for_pat g bnds pat} ->
    hyp_var:var{None? (lookup_bvar (extend_env_l g (refl_bindings_to_bindings bnds)) hyp_var)} ->

    body:term ->

    _ : squash (Some? (elaborate_pat pat bnds)) ->

    typing (extend_env
            (extend_env_l g (refl_bindings_to_bindings bnds))
             hyp_var (eq2 sc_u sc_ty sc (fst (Some?.v (elaborate_pat pat bnds))))
           )
           body rty ->

    branch_typing g sc_u sc_ty sc rty
       (pat, close_term_bs (refl_bindings_to_bindings bnds) body)
       bnds

and match_is_complete : env -> term -> typ -> list pattern -> list (list R.binding) -> Type0 =
  | MC_Tok :
    env:_ ->
    sc:_ ->
    ty:_ ->
    pats:_ ->
    bnds:_ ->
    squash (match_complete_token env sc ty pats bnds) -> match_is_complete env sc ty pats bnds

and sub_typing (g:env) (t1 t2:term) = related g t1 R_Sub t2

and sub_comp (g:env) (c1 c2:comp_typ) = related_comp g c1 R_Sub c2

and equiv (g:env) (t1 t2:term) = related g t1 R_Eq t2

type tot_typing (g:env) (e:term) (t:term) = typing g e (E_Total, t)

type ghost_typing (g:env) (e:term) (t:term) = typing g e (E_Ghost, t)

val subtyping_token_renaming (g:env)
                             (bs0:bindings)
                             (bs1:bindings)
                             (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                             (y:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) y) })
                             (t:term)
                             (t0 t1:term)
                             (d:subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1)
  : subtyping_token (extend_env_l g (rename_bindings bs1 x y@(y,t)::bs0))
                      (rename t0 x y)
                      (rename t1 x y)

val subtyping_token_weakening (g:env)
                              (bs0:bindings)
                              (bs1:bindings)
                              (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                              (t:term)
                              (t0 t1:term)
                              (d:subtyping_token (extend_env_l g (bs1@bs0)) t0 t1)
  : subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1

let simplify_umax (#g:R.env) (#t:R.term) (#u:R.universe)
                  (d:typing g t (E_Total, tm_type (u_max u u)))
   : typing g t (E_Total, tm_type u)
   = let ue
       : univ_eq (u_max u u) u
       = UN_MaxLeq u u (UNLEQ_Refl u)
     in
     let du : related g (tm_type (u_max u u)) R_Eq (tm_type u)
       = Rel_univ g (u_max u u) u ue in
     let du : related g (tm_type (u_max u u)) R_Sub (tm_type u)
       = Rel_equiv _ _ _ _ du in
     T_Sub _ _ _ _ d (Relc_typ _ _ _ E_Total _ du)

val well_typed_terms_are_ln (g:R.env) (e:R.term) (c:comp_typ) (_:typing g e c)
  : Lemma (ensures ln e /\ ln (snd c))

val type_correctness (g:R.env) (e:R.term) (c:comp_typ) (_:typing g e c)
  : GTot (u:R.universe & typing g (snd c) (E_Total, tm_type u))

val binder_offset_pattern_invariant (p:pattern) (ss:subst)
  : Lemma (binder_offset_pattern p == binder_offset_pattern (subst_pattern p ss))

val binder_offset_patterns_invariant (p:list (pattern & bool)) (ss:subst)
  : Lemma (binder_offset_patterns p == binder_offset_patterns (subst_patterns p ss))

val open_close_inverse' (i:nat) (t:term { ln' t (i - 1) }) (x:var)
  : Lemma 
       (ensures subst_term 
                  (subst_term t [ ND x i ])
                  (open_with_var x i)
                == t)

val open_close_inverse'_binder (i:nat) (b:binder { ln'_binder b (i - 1) }) (x:var)
  : Lemma (ensures subst_binder
                     (subst_binder b [ ND x i ])
                     (open_with_var x i)
                   == b)

val open_close_inverse'_terms (i:nat) (ts:list term { ln'_terms ts (i - 1) }) (x:var)
  : Lemma (ensures subst_terms
                     (subst_terms ts [ ND x i ])
                     (open_with_var x i)
                   == ts)

val open_close_inverse'_comp (i:nat) (c:comp { ln'_comp c (i - 1) }) (x:var)
  : Lemma 
    (ensures subst_comp
               (subst_comp c [ ND x i ])
               (open_with_var x i)
             == c)

val open_close_inverse'_args (i:nat) 
                            (ts:list argv { ln'_args ts (i - 1) })
                            (x:var)
  : Lemma
    (ensures subst_args
               (subst_args ts [ ND x i ])
               (open_with_var x i)
             == ts)

val open_close_inverse'_patterns (i:nat)
                                 (ps:list (pattern & bool) { ln'_patterns ps (i - 1) })
                                 (x:var)
  : Lemma 
    (ensures subst_patterns
               (subst_patterns ps [ ND x i ])
               (open_with_var x i)
             == ps)

val open_close_inverse'_pattern (i:nat) (p:pattern{ln'_pattern p (i - 1)}) (x:var)
  : Lemma 
    (ensures subst_pattern
               (subst_pattern p [ ND x i ])
               (open_with_var x i)
             == p)
    
val open_close_inverse'_branch (i:nat) (br:branch{ln'_branch br (i - 1)}) (x:var)
  : Lemma
    (ensures subst_branch
               (subst_branch br [ ND x i ])
               (open_with_var x i)
             == br)
  
val open_close_inverse'_branches (i:nat)
                                 (brs:list branch { ln'_branches brs (i - 1) })
                                 (x:var)
  : Lemma
    (ensures subst_branches
               (subst_branches brs [ ND x i ])
               (open_with_var x i)
             == brs)
  
val open_close_inverse'_match_returns (i:nat) 
                                      (m:match_returns_ascription { ln'_match_returns m (i - 1) })
                                      (x:var)
  : Lemma 
    (ensures subst_match_returns
               (subst_match_returns m [ ND x i ])
               (open_with_var x i)
             == m)

val open_close_inverse (e:R.term { ln e }) (x:var)
  : Lemma (open_term (close_term e x) x == e)


val close_open_inverse' (i:nat)
                        (t:term) 
                        (x:var { ~(x `Set.mem` freevars t) })
  : Lemma 
       (ensures subst_term 
                  (subst_term t (open_with_var x i))
                  [ ND x i ]
                == t)

val close_open_inverse'_comp (i:nat)
                             (c:comp)
                             (x:var{ ~(x `Set.mem` freevars_comp c) })
  : Lemma
       (ensures subst_comp 
                  (subst_comp c (open_with_var x i))
                  [ ND x i ]
                == c)

val close_open_inverse'_args (i:nat) (args:list argv) (x:var{ ~(x `Set.mem` freevars_args args) })
  : Lemma
       (ensures subst_args 
                  (subst_args args (open_with_var x i))
                  [ ND x i]
                == args)

val close_open_inverse'_binder (i:nat) (b:binder) (x:var{ ~(x `Set.mem` freevars_binder b) })
  : Lemma 
       (ensures subst_binder 
                  (subst_binder b (open_with_var x i))
                  [ ND x i ]
                == b)

val close_open_inverse'_terms (i:nat) (ts:list term) (x:var{ ~(x `Set.mem` freevars_terms ts) })
  : Lemma 
       (ensures subst_terms 
                  (subst_terms ts (open_with_var x i))
                  [ ND x i ]
                == ts)

val close_open_inverse'_branches (i:nat) (brs:list branch) 
                                 (x:var{ ~(x `Set.mem` freevars_branches brs) })
  : Lemma
    (ensures subst_branches
               (subst_branches brs (open_with_var x i))
               [ ND x i ]
                == brs)

val close_open_inverse'_branch (i:nat)
                               (br:branch)
                               (x:var{ ~(x `Set.mem` freevars_branch br) })
  : Lemma
    (ensures subst_branch
               (subst_branch br (open_with_var x i))
               [ ND x i ]
                == br)

val close_open_inverse'_pattern (i:nat)
                                (p:pattern)
                                (x:var{ ~(x `Set.mem` freevars_pattern p) })
  : Lemma
    (ensures subst_pattern
               (subst_pattern p (open_with_var x i))
               [ ND x i ]
                == p)

val close_open_inverse'_patterns (i:nat)
                                 (ps:list (pattern & bool))
                                 (x:var {~ (x `Set.mem` freevars_patterns ps) })
  : Lemma 
    (ensures subst_patterns
               (subst_patterns ps (open_with_var x i))
               [ ND x i ]
             == ps)

val close_open_inverse'_match_returns (i:nat) (m:match_returns_ascription)
                                      (x:var{ ~(x `Set.mem` freevars_match_returns m) })
  : Lemma
    (ensures subst_match_returns
               (subst_match_returns m (open_with_var x i))
               [ ND x i ]
                == m)

val close_open_inverse (e:R.term) (x:var {~ (x `Set.mem` freevars e) })
  : Lemma (close_term (open_term e x) x == e)

//
// fst has corresponding lemmas for other syntax classes
//
val close_with_not_free_var (t:R.term) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars t)))
      (ensures subst_term t [ ND x i ] == t)

// this also requires x to be not in freevars e1 `Set.union` freevars e2
val equiv_arrow (#g:R.env) (#e1 #e2:R.term) (ty:R.typ) (q:R.aqualv)
  (x:var { None? (lookup_bvar g x) })
  (eq:equiv (extend_env g x ty)
            (subst_term e1 (open_with_var x 0))
            (subst_term e2 (open_with_var x 0)))
  : equiv g (mk_arrow ty q e1)
            (mk_arrow ty q e2)


// the proof for this requires e1 and e2 to be ln
val equiv_abs_close (#g:R.env) (#e1 #e2:R.term) (ty:R.typ) (q:R.aqualv)
  (x:var{None? (lookup_bvar g x)})
  (eq:equiv (extend_env g x ty) e1 e2)
  : equiv g (mk_abs ty q (subst_term e1 [ ND x 0 ]))
            (mk_abs ty q (subst_term e2 [ ND x 0 ]))

val open_with_gt_ln (e:term) (i:nat) (t:term) (j:nat)
  : Lemma
      (requires ln' e i /\ i < j)
      (ensures subst_term e [ DT j t ] == e)
      [SMTPat (ln' e i); SMTPat (subst_term e [ DT j t ])]

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
// No universe polymorphism yet
//
noeq
type sigelt_typing : env -> sigelt -> Type0 =
  | ST_Let :
    g : env ->
    fv : R.fv ->
    ty : R.typ ->
    tm : R.term ->
    squash (typing g tm (E_Total, ty)) ->
    sigelt_typing g (pack_sigelt (Sg_Let false [pack_lb ({ lb_fv = fv; lb_us = []; lb_typ = ty; lb_def = tm })]))

  | ST_Let_Opaque :
    g : env ->
    fv : R.fv ->
    ty : R.typ ->
    (* no tm: only a proof of existence *)
    squash (exists (tm:R.term). typing g tm (E_Total, ty)) ->
    sigelt_typing g (pack_sigelt (Sg_Let false [pack_lb ({ lb_fv = fv; lb_us = []; lb_typ = ty; lb_def = (`_) })]))

(**
 * The type of the top-level tactic that would splice-in the definitions.
 *
 * The tactic takes as input as type environment and an optional expected type
 *
 * It returns (sigelts_before, sigelt, sigelt_after)
 *   where sigelts_before and sigelt_after are list of sigelts
 *
 * All the returned sigelts indicate via a boolean flag whether they are well-typed,
 *   in the judgment above
 *
 * If the flag is not set, F* typechecker typechecks the returned sigelts
 *
 * The sigelt in the middle, if well-typed, has the input expected type
 *
 * In addition, each sigelt can have a 'blob' attached with a given name.
 * The blob can be used later, e.g., during extraction, and passed back to the
 * extension to perform additional processing.
 *
 * The blob is stored in the sigmeta_extension_data field of the enclosing sigelt.
 *)

let blob = string & R.term

//
// t is the optional expected type
//
let sigelt_has_type (s:R.sigelt) (t:option R.term) : prop =
  let open R in
  match t with
  | None -> True
  | Some t ->
    match inspect_sigelt s with
    | Sg_Let false [lb] -> begin
      let {lb_typ} = inspect_lb lb in
      lb_typ == t
    end

    | _ -> False

//
// If checked is true, this sigelt is properly typed for the environment
// If not, we don't know and let F* re-typecheck the sigelt.
//

let sigelt_for (g:env) (t:option R.typ) =
  tup:(bool & sigelt & option blob) {
    let (checked, se, _) = tup in
    checked ==> (sigelt_typing g se /\ sigelt_has_type se t)
  }

//
// sigelts_before, sigelt, sigelts_after
//
let dsl_tac_result_t (g:env) (t:option R.typ) =
  list (sigelt_for g None) &
  (sigelt_for g t) &
  list (sigelt_for g None)

//
// The input option R.typ is the expected type
//
type dsl_tac_t =
  gt:(fstar_top_env & option R.typ) ->
  Tac (dsl_tac_result_t (fst gt) (snd gt))

val if_complete_match (g:env) (t:term)
  : match_complete_token g t bool_ty [
       Pat_Constant C_True;
       Pat_Constant C_False;
    ] [[]; []]

// Derived rule for if

val mkif
    (g:fstar_env)
    (scrutinee:term)
    (then_:term)
    (else_:term)
    (ty:term)
    (u_ty:universe)
    (hyp:var { None? (lookup_bvar g hyp) /\ ~(hyp `Set.mem` (freevars then_ `Set.union` freevars else_)) })
    (eff:tot_or_ghost)
    (ty_eff:tot_or_ghost)
    (ts : typing g scrutinee (eff, bool_ty))
    (tt : typing (extend_env g hyp (eq2 (pack_universe Uv_Zero) bool_ty scrutinee true_bool)) then_ (eff, ty))
    (te : typing (extend_env g hyp (eq2 (pack_universe Uv_Zero) bool_ty scrutinee false_bool)) else_ (eff, ty))
    (tr : typing g ty (ty_eff, tm_type u_ty))
: typing g (mk_if scrutinee then_ else_) (eff, ty)

(* Helper to return a single let definition in a splice_t tactic. *)
let mk_checked_let (g:R.env) (cur_module:name) (nm:string) (tm:R.term) (ty:R.typ{typing g tm (E_Total, ty)})
  : sigelt_for g (Some ty) =
  let fv = pack_fv (cur_module @ [nm]) in
  let lb = R.pack_lb ({ lb_fv = fv; lb_us = []; lb_typ = ty; lb_def = tm }) in
  let se = R.pack_sigelt (R.Sg_Let false [lb]) in
  let pf : sigelt_typing g se =
    ST_Let g fv ty tm ()
  in
  ( true, se, None )

let mk_unchecked_let (g:R.env) (cur_module:name) (nm:string) (tm:R.term) (ty:R.typ)
  : bool & sigelt & option blob =
  let fv = pack_fv (cur_module @ [nm]) in
  let lb = R.pack_lb ({ lb_fv = fv; lb_us = []; lb_typ = ty; lb_def = tm }) in
  let se = R.pack_sigelt (R.Sg_Let false [lb]) in
  ( false, se, None )

(* Turn a typing derivation into a token. This is useful
to call primitives that require a proof of typing, like
`call_subtac`, since they do not take derivations nor can
they even be mentioned in that module due to dependencies.
Probably the right thing to do is refactor and avoid this, though. *)
val typing_to_token (#g:env) (#e:term) (#c:comp_typ)
  : typing g e c -> typing_token g e c
