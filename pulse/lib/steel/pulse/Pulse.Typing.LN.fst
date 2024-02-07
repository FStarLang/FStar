(*
   Copyright 2023 Microsoft Research

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

module Pulse.Typing.LN
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing

//
// TODO: this is needed only for the E_Total flag,
//       may be the flag should move to reflection
//
module T = FStar.Tactics.V2

let well_typed_terms_are_ln (g:R.env) (e:R.term) (t:R.term) (#eff:_) (d:RT.typing g e (eff, t))
  : Lemma (ensures RT.ln e /\ RT.ln t) =

  RT.well_typed_terms_are_ln g e (eff, t) d

let rt_equiv_ln (g:R.env) (e1 e2:R.term) (d:RT.equiv g e1 e2)
  : Lemma (RT.ln e1 /\ RT.ln e2) = admit ()

assume
val elab_ln_inverse (e:term)
  : Lemma 
    (requires RT.ln (elab_term e))
    (ensures ln e)

assume
val open_term_ln_host' (t:host_term) (x:R.term) (i:index)
  : Lemma 
    (requires RT.ln' (RT.subst_term t [ RT.DT i x ]) (i - 1))
    (ensures RT.ln' t i)

let rec open_term_ln' (e:term)
                      (x:term)
                      (i:index)
  : Lemma 
    (requires ln' (open_term' e x i) (i - 1))
    (ensures ln' e i)
    (decreases e)
  = match e.t with
    | Tm_Emp
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Unknown -> ()

    | Tm_Inv p ->
      open_term_ln' p x i

    | Tm_Pure p ->
      open_term_ln' p x i

    | Tm_AddInv l r
    | Tm_Star l r ->
      open_term_ln' l x i;
      open_term_ln' r x i

    | Tm_ExistsSL _ t b
    | Tm_ForallSL _ t b ->
      open_term_ln' t.binder_ty x i;    
      open_term_ln' b x (i + 1)

    | Tm_FStar t ->
      open_term_ln_host' t (elab_term x) i

let open_comp_ln' (c:comp)
                  (x:term)
                  (i:index)
  : Lemma 
    (requires ln_c' (open_comp' c x i) (i - 1))
    (ensures ln_c' c i)
  = match c with
    | C_Tot t ->
      open_term_ln' t x i

    | C_ST s
    | C_STGhost s ->
      open_term_ln' s.res x i;
      open_term_ln' s.pre x i;      
      open_term_ln' s.post x (i + 1)

    | C_STAtomic n _ s ->    
      open_term_ln' n x i;    
      open_term_ln' s.res x i;
      open_term_ln' s.pre x i;      
      open_term_ln' s.post x (i + 1)

let open_term_ln_opt' (t:option term) (x:term) (i:index)
  : Lemma
    (requires ln_opt' ln' (open_term_opt' t x i) (i - 1))
    (ensures ln_opt' ln' t i)
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> open_term_ln' t x i

// aux
let __brs_of (t:st_term{Tm_Match? t.term}) : list branch =
  let Tm_Match {brs} = t.term in
  brs

let rec open_term_ln_list' (t:list term) (x:term) (i:index)
  : Lemma
    (requires ln_list' (open_term_list' t x i) (i - 1))
    (ensures ln_list' t i)
    (decreases t)
  = match t with
    | [] -> ()
    | hd::tl ->
      open_term_ln' hd x i;
      open_term_ln_list' tl x i      

let open_term_pairs' (t:list (term & term)) (v:term) (i:index)
  : Tot (list (term & term))
  = subst_term_pairs t [ DT i v ]

let rec open_term_ln_pairs (t:list (term & term)) (x:term) (i:index)
  : Lemma
    (requires ln_terms' (open_term_pairs' t x i) (i - 1))
    (ensures ln_terms' t i)
    (decreases t)
  = match t with
    | [] -> ()
    | (l, r)::tl ->
      open_term_ln' l x i;
      open_term_ln' r x i;
      open_term_ln_pairs tl x i

let open_proof_hint_ln (t:proof_hint_type) (x:term) (i:index)
  : Lemma
    (requires ln_proof_hint' (open_proof_hint' t x i) (i - 1))
    (ensures ln_proof_hint' t i)
  = match t with
    | ASSERT { p }
    | FOLD { p }
    | UNFOLD { p } ->
      open_term_ln' p x i
    | RENAME { pairs; goal } ->
      open_term_ln_pairs pairs x i;
      open_term_ln_opt' goal x i
    | REWRITE { t1; t2 } ->
      open_term_ln' t1 x i;
      open_term_ln' t2 x i
    | WILD
    | SHOW_PROOF_STATE _ -> ()

let open_pattern'  (p:pattern) (v:term) (i:index) =
  subst_pat p [DT i v]
let close_pattern' (p:pattern) (x:var) (i:index) =
  subst_pat p [ND x i]
let open_pattern_args' (ps:list (pattern & bool)) (v:term) (i:index) =
  subst_pat_args ps [DT i v]
let close_pattern_args' (ps:list (pattern & bool)) (x:var) (i:index) =
  subst_pat_args ps [ND x i]

let rec pattern_shift_subst_invariant (p:pattern) (s:subst)
  : Lemma
    (ensures pattern_shift_n p == pattern_shift_n (subst_pat p s))
    [SMTPat (pattern_shift_n (subst_pat p s))]
  = match p with
    | Pat_Cons _ subpats -> admit()
    | _ -> ()
and pattern_args_shift_subst_invariant (ps:list (pattern & bool)) (s:subst)
  : Lemma
    (ensures pattern_args_shift_n ps == pattern_args_shift_n (subst_pat_args ps s))
  = match ps with
    | [] -> ()
    | (hd, _)::tl ->
      pattern_shift_subst_invariant hd s;
      pattern_args_shift_subst_invariant tl (shift_subst_n (pattern_shift_n hd) s)

let rec open_pattern_ln (p:pattern) (x:term) (i:index)
  : Lemma 
    (requires ln_pattern' (open_pattern' p x i) (i - 1))
    (ensures ln_pattern' p i)
    (decreases p)
  = match p with
    | Pat_Constant _
    | Pat_Var _ _
    | Pat_Dot_Term None -> ()
    | Pat_Dot_Term (Some e) ->
      open_term_ln' e x i
    | Pat_Cons _ subpats ->
      open_pattern_args_ln subpats x i

and open_pattern_args_ln (pats:list (pattern & bool)) (x:term) (i:index)
  : Lemma 
    (requires ln_pattern_args' (open_pattern_args' pats x i) (i - 1))
    (ensures ln_pattern_args' pats i)
    (decreases pats)
  = match pats with
    | [] -> ()
    | (hd, b)::tl ->
      open_pattern_ln hd x i;
      open_pattern_args_ln tl x (i + pattern_shift_n hd)

let map_opt_lemma_2 ($f: (x:'a -> y:'b -> z:'c -> Lemma (requires 'p x y z) (ensures 'q x y z)))
                    (x:option 'a) 
                    (y:'b)
                    (z:'c)
   : Lemma (requires Some? x ==> 'p (Some?.v x) y z)
           (ensures Some? x ==> 'q (Some?.v x) y z)
   = match x with
     | None -> ()
     | Some x -> f x y z

#push-options "--z3rlimit 20"
let rec open_st_term_ln' (e:st_term)
                         (x:term)
                         (i:index)
  : Lemma 
    (requires ln_st' (open_st_term' e x i) (i - 1))
    (ensures ln_st' e i)
    (decreases e)
  = match e.term with
    | Tm_Return { expected_type; term = e } ->
      open_term_ln' expected_type x i;
      open_term_ln' e x i
      
    | Tm_STApp { head=l; arg=r } ->
      open_term_ln' l x i;
      open_term_ln' r x i

    | Tm_Abs { b; ascription=c; body } ->
      open_term_ln' b.binder_ty x i;
      map_opt_lemma_2 open_comp_ln' c.annotated x (i + 1);
      map_opt_lemma_2 open_comp_ln' c.elaborated x (i + 1);
      open_st_term_ln' body x (i + 1)
      
    | Tm_Bind { binder; head; body } ->
      open_term_ln' binder.binder_ty x i;
      open_st_term_ln' head x i;
      open_st_term_ln' body x (i + 1)
   
    | Tm_TotBind { binder; head; body } ->
      open_term_ln' binder.binder_ty x i;
      open_term_ln' head x i;
      open_st_term_ln' body x (i + 1)
      
    | Tm_If { b; then_; else_; post } ->
      open_term_ln' b x i;    
      open_st_term_ln' then_ x i;    
      open_st_term_ln' else_ x i;          
      open_term_ln_opt' post x (i + 1)

    | Tm_Match {sc;returns_;brs} ->
      open_term_ln' sc x i;
      open_term_ln_opt' returns_ x i;
      assert (__brs_of e == brs);
      open_branches_ln' e brs x i;
      ()

    | Tm_IntroPure { p }
    | Tm_ElimExists { p } ->
      open_term_ln' p x i

    | Tm_IntroExists { p; witnesses } ->
      open_term_ln' p x i;
      open_term_ln_list' witnesses x i

    | Tm_While { invariant; condition; body } ->
      open_term_ln' invariant x (i + 1);
      open_st_term_ln' condition x i;
      open_st_term_ln' body x i

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      open_term_ln' pre1 x i;
      open_st_term_ln' body1 x i;
      open_term_ln' post1 x (i + 1);
      open_term_ln' pre2 x i;
      open_st_term_ln' body2 x i;
      open_term_ln' post2 x (i + 1)

    | Tm_Rewrite { t1; t2 } ->
      open_term_ln' t1 x i;
      open_term_ln' t2 x i

    | Tm_WithLocal { binder; initializer; body } ->
      open_term_ln' binder.binder_ty x i;
      open_term_ln' initializer x i;
      open_st_term_ln' body x (i + 1)
    
    | Tm_WithLocalArray { binder; initializer; length; body } ->
      open_term_ln' binder.binder_ty x i;
      open_term_ln' initializer x i;
      open_term_ln' length x i;
      open_st_term_ln' body x (i + 1)

    | Tm_Admit { typ; post } ->
      open_term_ln' typ x i;
      open_term_ln_opt' post x (i + 1)

    | Tm_Unreachable -> ()

    | Tm_ProofHintWithBinders { binders; hint_type; t } ->
      let n = L.length binders in
      open_proof_hint_ln hint_type x (i + n);
      open_st_term_ln' t x (i + n)

    | Tm_WithInv { name; body; returns_inv } ->
      open_term_ln' name x i;
      open_st_term_ln' body x i;
      match returns_inv with
      | None -> ()
      | Some (b, r) ->
        open_term_ln' b.binder_ty x i;
        open_term_ln' r x (i + 1)

// The Tm_Match? and __brs_of conditions are to prove that the ln_branches' below
// satisfies the termination refinment.
and open_branches_ln' (t:st_term{Tm_Match? t.term})
                      (brs:list branch{brs << t /\ __brs_of t == brs})
                      (x:term)
                      (i:index)
  : Lemma 
    (requires (
      assert (subst_branches t [DT i x] brs == __brs_of (subst_st_term t [DT i x])); // hint
      ln_branches' (open_st_term' t x i) (subst_branches t [DT i x] brs) (i - 1)))
    (ensures ln_branches' t brs i)
    (decreases brs)
  = match brs with
    | [] -> ()
    | br::brs ->
      assume (ln_branch' (subst_branch [DT i x] br) (i - 1)); // Should be immediate. Unfold
      open_branch_ln' br x i;
      admit ()

and open_branch_ln' (br : branch) (x:term) (i:index)
  : Lemma
    (requires ln_branch' (subst_branch [DT i x] br) (i - 1))
    (ensures ln_branch' br i)
  = let (p, e) = br in
    open_pattern_ln p x i;
    open_st_term_ln' e x (i + pattern_shift_n p)

let open_term_ln (e:term) (v:var)
  : Lemma 
    (requires ln (open_term e v))
    (ensures ln' e 0)
  = open_term_ln' e (term_of_no_name_var v) 0


let open_st_term_ln (e:st_term) (v:var)
  : Lemma 
    (requires ln_st (open_st_term e v))
    (ensures ln_st' e 0)
  = open_st_term_ln' e (term_of_no_name_var v) 0

assume
val r_ln_weakening (e:R.term) (i j:int)
  : Lemma 
    (requires RT.ln' e i /\ i <= j)
    (ensures RT.ln' e j)

let rec ln_weakening (e:term) (i j:int)
  : Lemma 
    (requires ln' e i /\ i <= j)
    (ensures ln' e j)      
    (decreases e)
    [SMTPat (ln' e j);
     SMTPat (ln' e i)]
  = match e.t with
    | Tm_Emp
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Unknown -> ()
    | Tm_Inv p ->
      ln_weakening p i j
    | Tm_Pure p ->
      ln_weakening p i j
      
    // | Tm_PureApp l _ r
    | Tm_AddInv l r
    | Tm_Star l r ->
      ln_weakening l i j;
      ln_weakening r i j

    | Tm_ExistsSL _ t b
    | Tm_ForallSL _ t b ->
      ln_weakening t.binder_ty i j;    
      ln_weakening b (i + 1) (j + 1)

    | Tm_FStar t ->
      r_ln_weakening t i j
#pop-options

let ln_weakening_comp (c:comp) (i j:int)
  : Lemma 
    (requires ln_c' c i /\ i <= j)
    (ensures ln_c' c j)
  = match c with
    | C_Tot t ->
      ln_weakening t i j

    | C_ST s
    | C_STGhost s ->
      ln_weakening s.res i j;
      ln_weakening s.pre i j;      
      ln_weakening s.post (i + 1) (j + 1)

    | C_STAtomic n _ s ->    
      ln_weakening n i j;    
      ln_weakening s.res i j;
      ln_weakening s.pre i j;      
      ln_weakening s.post (i + 1) (j + 1)

let ln_weakening_opt (t:option term) (i j:int)
  : Lemma
    (requires ln_opt' ln' t i /\ i <= j)
    (ensures ln_opt' ln' t j)
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> ln_weakening t i j


let rec ln_weakening_list (t:list term) (i j:int)
  : Lemma
    (requires ln_list' t i /\ i <= j)
    (ensures ln_list' t j)
    (decreases t)
  = match t with
    | [] -> ()
    | hd::tl ->
      ln_weakening hd i j;
      ln_weakening_list tl i j

let rec ln_weakening_pairs (t:list (term & term)) (i j:int)
  : Lemma
    (requires ln_terms' t i /\ i <= j)
    (ensures ln_terms' t j)
    (decreases t)
  = match t with
    | [] -> ()
    | (l, r)::tl ->
      ln_weakening l i j;
      ln_weakening r i j;
      ln_weakening_pairs tl i j

let ln_weakening_proof_hint (t:proof_hint_type) (i j:int)
  : Lemma
    (requires ln_proof_hint' t i /\ i <= j)
    (ensures ln_proof_hint' t j)
  = match t with
    | ASSERT { p }
    | FOLD { p }
    | UNFOLD { p } ->
      ln_weakening p i j 
    | RENAME { pairs; goal } ->
      ln_weakening_pairs pairs i j;
      ln_weakening_opt goal i j
    | REWRITE { t1; t2 } ->
      ln_weakening t1 i j;
      ln_weakening t2 i j
    | WILD
    | SHOW_PROOF_STATE _ -> ()

let rec ln_weakening_st (t:st_term) (i j:int)
  : Lemma
    (requires ln_st' t i /\ i <= j)
    (ensures ln_st' t j)
    (decreases t)
  = match t.term with
    | Tm_Return { expected_type; term } ->
      ln_weakening expected_type i j;
      ln_weakening term i j

    | Tm_IntroPure { p }
    | Tm_ElimExists { p } ->
      ln_weakening p i j
      
    | Tm_IntroExists { p; witnesses } ->
      ln_weakening p i j;
      ln_weakening_list witnesses i j

    | Tm_While { invariant; condition; body } ->
      ln_weakening invariant (i + 1) (j + 1);
      ln_weakening_st condition i j;
      ln_weakening_st body i j
    
    | Tm_If { b; then_; else_; post } ->
      ln_weakening b i j;    
      ln_weakening_st then_ i j;    
      ln_weakening_st else_ i j;          
      ln_weakening_opt post (i + 1) (j + 1)

    | Tm_Match _ ->
      admit ()

    | Tm_STApp { head; arg } ->
      ln_weakening head i j;
      ln_weakening arg i j      

    | Tm_Bind { binder; head; body } ->
      ln_weakening binder.binder_ty i j;
      ln_weakening_st head i j;
      ln_weakening_st body (i + 1) (j + 1)

    | Tm_TotBind { binder; head; body } ->
      ln_weakening binder.binder_ty i j;
      ln_weakening head i j;
      ln_weakening_st body (i + 1) (j + 1)

    | Tm_Abs { b; ascription=c; body } ->
      ln_weakening b.binder_ty i j;
      map_opt_lemma_2 ln_weakening_comp c.annotated (i + 1) (j + 1);
      map_opt_lemma_2 ln_weakening_comp c.elaborated (i + 1) (j + 1);
      ln_weakening_st body (i + 1) (j + 1)

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      ln_weakening pre1 i j;
      ln_weakening_st body1 i j;
      ln_weakening post1 (i + 1) (j + 1);
      ln_weakening pre2 i j;
      ln_weakening_st body2 i j;
      ln_weakening post2 (i + 1) (j + 1)

    | Tm_Rewrite { t1; t2 } ->
      ln_weakening t1 i j;
      ln_weakening t2 i j

    | Tm_WithLocal { initializer; body } ->
      ln_weakening initializer i j;
      ln_weakening_st body (i + 1) (j + 1)

    | Tm_WithLocalArray { initializer; length; body } ->
      ln_weakening initializer i j;
      ln_weakening length i j;
      ln_weakening_st body (i + 1) (j + 1)
   
    | Tm_Admit { typ; post } ->
      ln_weakening typ i j;
      ln_weakening_opt post (i + 1) (j + 1)
    
    | Tm_Unreachable -> ()

    | Tm_ProofHintWithBinders { binders; hint_type; t } ->
      let n = L.length binders in
      ln_weakening_proof_hint hint_type (i + n) (j + n);
      ln_weakening_st t (i + n) (j + n)

    | Tm_WithInv { name; body; returns_inv } ->
      ln_weakening name i j;
      ln_weakening_st body i j;
      match returns_inv with
      | None -> ()
      | Some (b, r) ->
        ln_weakening b.binder_ty i j;
        ln_weakening r (i + 1) (j + 1)

assume
val r_open_term_ln_inv' (e:R.term) (x:R.term { RT.ln x }) (i:index)
  : Lemma 
    (requires RT.ln' e i)
    (ensures RT.ln' (RT.subst_term e [ RT.DT i x ]) (i - 1))

let rec open_term_ln_inv' (e:term)
                          (x:term { ln x })
                          (i:index)
  : Lemma 
    (requires ln' e i)
    (ensures ln' (open_term' e x i) (i - 1))
    (decreases e)
  = match e.t with
    | Tm_Emp
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Unknown ->
      ln_weakening x (-1) (i - 1)

    | Tm_Inv p ->
      open_term_ln_inv' p x i
    | Tm_Pure p ->
      open_term_ln_inv' p x i

    // | Tm_PureApp l _ r
    | Tm_AddInv l r
    | Tm_Star l r ->
      open_term_ln_inv' l x i;
      open_term_ln_inv' r x i

    | Tm_ExistsSL _ t b
    | Tm_ForallSL _ t b ->
      open_term_ln_inv' t.binder_ty x i;    
      open_term_ln_inv' b x (i + 1)

    | Tm_FStar t ->
      Pulse.Elaborate.elab_ln x (-1);
      r_open_term_ln_inv' t (elab_term x) i

let open_comp_ln_inv' (c:comp)
                      (x:term { ln x })
                      (i:index)
  : Lemma 
    (requires ln_c' c i)
    (ensures ln_c' (open_comp' c x i) (i - 1))
  = match c with
    | C_Tot t ->
      open_term_ln_inv' t x i

    | C_ST s
    | C_STGhost s ->
      open_term_ln_inv' s.res x i;
      open_term_ln_inv' s.pre x i;      
      open_term_ln_inv' s.post x (i + 1)

    | C_STAtomic n _ s ->    
      open_term_ln_inv' n x i;    
      open_term_ln_inv' s.res x i;
      open_term_ln_inv' s.pre x i;      
      open_term_ln_inv' s.post x (i + 1)

let open_term_ln_inv_opt' (t:option term)
                          (x:term { ln x })
                          (i:index)
  : Lemma
    (requires ln_opt' ln' t i)
    (ensures ln_opt' ln' (open_term_opt' t x i) (i - 1))
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> open_term_ln_inv' t x i

let rec open_term_ln_inv_list' (t:list term)
                               (x:term { ln x })
                               (i:index)
  : Lemma
    (requires ln_list' t i)
    (ensures ln_list' (open_term_list' t x i) (i - 1))
    (decreases t)
  = match t with
    | [] -> ()
    | hd::tl ->
      open_term_ln_inv' hd x i;
      open_term_ln_inv_list' tl x i      

let rec open_term_ln_inv_pairs (t:list (term & term))
                               (x:term { ln x })
                               (i:index)
  : Lemma
    (requires ln_terms' t i)
    (ensures ln_terms' (open_term_pairs' t x i) (i - 1))
    (decreases t)
  = match t with
    | [] -> ()
    | (l, r)::tl ->
      open_term_ln_inv' l x i;
      open_term_ln_inv' r x i;
      open_term_ln_inv_pairs tl x i

let open_proof_hint_ln_inv (ht:proof_hint_type) (x:term { ln x }) (i:index)
  : Lemma
    (requires ln_proof_hint' ht i)
    (ensures ln_proof_hint' (open_proof_hint' ht x i) (i - 1))
  = match ht with
    | ASSERT { p }
    | FOLD { p }
    | UNFOLD { p } ->
      open_term_ln_inv' p x i
    | RENAME { pairs; goal } ->
      open_term_ln_inv_pairs pairs x i;
      open_term_ln_inv_opt' goal x i
    | REWRITE { t1; t2 } ->
      open_term_ln_inv' t1 x i;
      open_term_ln_inv' t2 x i
    | WILD
    | SHOW_PROOF_STATE _ -> ()

#push-options "--z3rlimit_factor 2 --fuel 2 --ifuel 2"
let rec open_term_ln_inv_st' (t:st_term)
                             (x:term { ln x })
                             (i:index)
  : Lemma
    (requires ln_st' t i)
    (ensures ln_st' (open_st_term' t x i) (i - 1))
    (decreases t)
  = match t.term with
    | Tm_Return { expected_type; term } ->
      open_term_ln_inv' expected_type x i;
      open_term_ln_inv' term x i

    | Tm_IntroPure { p }
    | Tm_ElimExists { p } ->
      open_term_ln_inv' p x i

    | Tm_IntroExists { p; witnesses } ->
      open_term_ln_inv' p x i;
      open_term_ln_inv_list' witnesses x i

    | Tm_While { invariant; condition; body } ->
      open_term_ln_inv' invariant x (i + 1);
      open_term_ln_inv_st' condition x i;
      open_term_ln_inv_st' body x i

    | Tm_If { b; then_; else_; post } ->
      open_term_ln_inv' b x i;    
      open_term_ln_inv_st' then_ x i;    
      open_term_ln_inv_st' else_ x i;          
      open_term_ln_inv_opt' post x (i + 1)      

    | Tm_Match _ ->
      admit ()

    | Tm_Bind { binder; head; body } ->
      open_term_ln_inv' binder.binder_ty x i;
      open_term_ln_inv_st' head x i;
      open_term_ln_inv_st' body x (i + 1)

    | Tm_TotBind { binder; head; body } ->
      open_term_ln_inv' binder.binder_ty x i;
      open_term_ln_inv' head x i;
      open_term_ln_inv_st' body x (i + 1)

    | Tm_STApp { head; arg} ->
      open_term_ln_inv' head x i;
      open_term_ln_inv' arg x i

    | Tm_Abs { b; ascription=c; body } ->
      open_term_ln_inv' b.binder_ty x i;
      map_opt_lemma_2 open_comp_ln_inv' c.annotated x (i + 1);
      map_opt_lemma_2 open_comp_ln_inv' c.elaborated x (i + 1);
      open_term_ln_inv_st' body x (i + 1)

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      open_term_ln_inv' pre1 x i;
      open_term_ln_inv_st' body1 x i;
      open_term_ln_inv' post1 x (i + 1);
      open_term_ln_inv' pre2 x i;
      open_term_ln_inv_st' body2 x i;
      open_term_ln_inv' post2 x (i + 1)

    | Tm_Rewrite { t1; t2 } ->
      open_term_ln_inv' t1 x i;
      open_term_ln_inv' t2 x i

    | Tm_WithLocal { binder; initializer; body } ->
      open_term_ln_inv' binder.binder_ty x i;
      open_term_ln_inv' initializer x i;
      open_term_ln_inv_st' body x (i + 1)

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      open_term_ln_inv' binder.binder_ty x i;
      open_term_ln_inv' initializer x i;
      open_term_ln_inv' length x i;
      open_term_ln_inv_st' body x (i + 1)

    | Tm_Admit { typ; post } ->
      open_term_ln_inv' typ x i;
      open_term_ln_inv_opt' post x (i + 1)

    | Tm_Unreachable -> ()

    | Tm_ProofHintWithBinders { binders; hint_type; t } ->
      let n = L.length binders in
      open_proof_hint_ln_inv hint_type x (i + n);
      open_term_ln_inv_st' t x (i + n)

    | Tm_WithInv { name; body; returns_inv } ->
      open_term_ln_inv' name x i;
      open_term_ln_inv_st' body x i;
      match returns_inv with
      | None -> ()
      | Some (b, r) ->
        open_term_ln_inv' b.binder_ty x i;
        open_term_ln_inv' r x (i + 1)

#pop-options

assume
val r_close_term_ln' (e:R.term) (x:var) (i:index)
  : Lemma 
    (requires RT.ln' e (i - 1))
    (ensures RT.ln' (RT.subst_term e [ RT.ND x i ]) i)

let rec close_term_ln' (e:term)
                       (x:var)
                       (i:index)
  : Lemma 
    (requires ln' e (i - 1))
    (ensures ln' (close_term' e x i) i)
    (decreases e)
  = match e.t with
    | Tm_Emp
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Unknown -> ()

    | Tm_Inv p ->
      close_term_ln' p x i
    | Tm_Pure p ->
      close_term_ln' p x i

    | Tm_AddInv l r
    | Tm_Star l r ->
      close_term_ln' l x i;
      close_term_ln' r x i

    | Tm_ExistsSL _ t b
    | Tm_ForallSL _ t b ->
      close_term_ln' t.binder_ty x i;    
      close_term_ln' b x (i + 1)

    | Tm_FStar t ->
      r_close_term_ln' t x i

let close_comp_ln' (c:comp)
                   (x:var)
                   (i:index)
  : Lemma 
    (requires ln_c' c (i - 1))
    (ensures ln_c' (close_comp' c x i) i)
  = match c with
    | C_Tot t ->
      close_term_ln' t x i

    | C_ST s
    | C_STGhost s ->
      close_term_ln' s.res x i;
      close_term_ln' s.pre x i;      
      close_term_ln' s.post x (i + 1)

    | C_STAtomic n _ s ->    
      close_term_ln' n x i;    
      close_term_ln' s.res x i;
      close_term_ln' s.pre x i;      
      close_term_ln' s.post x (i + 1)

let close_term_ln_opt' (t:option term) (x:var) (i:index)
  : Lemma
    (requires ln_opt' ln' t (i - 1))
    (ensures ln_opt' ln' (close_term_opt' t x i) i)
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> close_term_ln' t x i

let rec close_term_ln_list' (t:list term) (x:var) (i:index)
  : Lemma
    (requires ln_list' t (i - 1))
    (ensures ln_list' (close_term_list' t x i) i)
    (decreases t)
  = match t with
    | [] -> ()
    | hd::tl ->
      close_term_ln' hd x i;
      close_term_ln_list' tl x i

let close_term_pairs' (t:list (term & term)) (v:var) (i:index)
  : Tot (list (term & term))
  = subst_term_pairs t [ ND v i ]

let rec close_term_ln_pairs (t:list (term & term)) (x:var) (i:index)
  : Lemma
    (requires ln_terms' t (i - 1))
    (ensures ln_terms' (close_term_pairs' t x i) i)
    (decreases t)
  = match t with
    | [] -> ()
    | (l, r)::tl ->
      close_term_ln' l x i;
      close_term_ln' r x i;
      close_term_ln_pairs tl x i

let close_proof_hint_ln (ht:proof_hint_type) (v:var) (i:index)
  : Lemma
    (requires ln_proof_hint' ht (i - 1))
    (ensures ln_proof_hint' (close_proof_hint' ht v i) i)
  = match ht with
    | ASSERT { p }
    | FOLD { p }
    | UNFOLD { p } ->
      close_term_ln' p v i
    | RENAME { pairs; goal } ->
      close_term_ln_pairs pairs v i;
      close_term_ln_opt' goal v i
    | REWRITE { t1; t2 } ->
      close_term_ln' t1 v i;
      close_term_ln' t2 v i
    | WILD
    | SHOW_PROOF_STATE _ -> ()

#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 2"
let rec close_st_term_ln' (t:st_term) (x:var) (i:index)
  : Lemma
    (requires ln_st' t (i - 1))
    (ensures ln_st' (close_st_term' t x i) i)
    (decreases t)
  = match t.term with
    | Tm_Return { expected_type; term } ->
      close_term_ln' expected_type x i;
      close_term_ln' term x i

    | Tm_IntroPure { p }
    | Tm_ElimExists { p } ->
      close_term_ln' p x i
      
    | Tm_IntroExists { p; witnesses } ->
      close_term_ln' p x i;
      close_term_ln_list' witnesses x i

    | Tm_While { invariant; condition; body } ->
      close_term_ln' invariant x (i + 1);
      close_st_term_ln' condition x i;
      close_st_term_ln' body x i

    | Tm_If { b; then_; else_; post } ->
      close_term_ln' b x i;    
      close_st_term_ln' then_ x i;    
      close_st_term_ln' else_ x i;          
      close_term_ln_opt' post x (i + 1)      

    | Tm_Match _ ->
      admit ()

    | Tm_Bind { binder; head; body } ->
      close_term_ln' binder.binder_ty x i;
      close_st_term_ln' head x i;
      close_st_term_ln' body x (i + 1)

    | Tm_TotBind { binder; head; body } ->
      close_term_ln' binder.binder_ty x i;
      close_term_ln' head x i;
      close_st_term_ln' body x (i + 1)

    | Tm_STApp { head; arg } ->
      close_term_ln' head x i;
      close_term_ln' arg x i

    | Tm_Abs { b; ascription=c; body } ->
      close_term_ln' b.binder_ty x i;
      map_opt_lemma_2 close_comp_ln' c.annotated x (i + 1);
      map_opt_lemma_2 close_comp_ln' c.elaborated x (i + 1);
      close_st_term_ln' body x (i + 1)

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      close_term_ln' pre1 x i;
      close_st_term_ln' body1 x i;
      close_term_ln' post1 x (i + 1);
      close_term_ln' pre2 x i;
      close_st_term_ln' body2 x i;
      close_term_ln' post2 x (i + 1)

    | Tm_Rewrite { t1; t2 } ->
      close_term_ln' t1 x i;
      close_term_ln' t2 x i
      
    | Tm_WithLocal { binder; initializer; body } ->
      close_term_ln' binder.binder_ty x i;
      close_term_ln' initializer x i;
      close_st_term_ln' body x (i + 1)

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      close_term_ln' binder.binder_ty x i;
      close_term_ln' initializer x i;
      close_term_ln' length x i;
      close_st_term_ln' body x (i + 1)

    | Tm_Admit { typ; post } ->
      close_term_ln' typ x i;
      close_term_ln_opt' post x (i + 1)

    | Tm_Unreachable -> ()

    | Tm_ProofHintWithBinders { binders; hint_type; t } ->
      let n = L.length binders in
      close_proof_hint_ln hint_type x (i + n);
      close_st_term_ln' t x (i + n)
      
    | Tm_WithInv { name; body; returns_inv } ->
      close_term_ln' name x i;
      close_st_term_ln' body x i;
      match returns_inv with
      | None -> ()
      | Some (ret_ty, returns_inv) ->
        close_term_ln' ret_ty.binder_ty x i;
        close_term_ln' returns_inv x (i + 1)
#pop-options
let close_comp_ln (c:comp) (v:var)
  : Lemma 
    (requires ln_c c)
    (ensures ln_c' (close_comp c v) 0)
  = close_comp_ln' c v 0

#push-options "--ifuel 2 --z3rlimit_factor 4 --z3cliopt 'smt.qi.eager_threshold=100'"

let lift_comp_ln #g #c1 #c2 (d:lift_comp g c1 c2)
  : Lemma
    (requires ln_c c1)
    (ensures ln_c c2)    
  = ()

let tot_or_ghost_typing_ln
  (#g:_) (#e:_) (#t:_) (#eff:_)
  (d:typing g e eff t)
  : Lemma 
    (ensures ln e /\ ln t)
  = let E dt = d in
    well_typed_terms_are_ln _ _ _ dt;
    elab_ln_inverse e;
    elab_ln_inverse t

let tot_typing_ln
  (#g:_) (#e:_) (#t:_)
  (d:tot_typing g e t)
  : Lemma 
    (ensures ln e /\ ln t)
  = tot_or_ghost_typing_ln d

let rec vprop_equiv_ln (#g:_) (#t0 #t1:_) (v:vprop_equiv g t0 t1)
  : Lemma (ensures ln t0 <==> ln t1)
          (decreases v)
  = match v with
    | VE_Refl _ _ -> ()
    | VE_Sym _ _ _ v' -> 
      vprop_equiv_ln v'
    | VE_Trans g t0 t2 t1 v02 v21 ->
      vprop_equiv_ln v02;
      vprop_equiv_ln v21
    | VE_Ctxt g s0 s1 s0' s1' v0 v1 ->
      vprop_equiv_ln v0;
      vprop_equiv_ln v1
    | VE_Unit g t -> ()
    | VE_Comm g t0 t1 -> ()
    | VE_Assoc g t0 t1 t2 -> ()
    | VE_Ext g t0 t1 token ->
      let d0, d1 = vprop_eq_typing_inversion _ _ _ token in
      tot_or_ghost_typing_ln d0;
      tot_or_ghost_typing_ln d1
    | VE_Fa g x u b t0' t1' d ->
      vprop_equiv_ln d;
      let xtm = (term_of_nvar (v_as_nv x)) in
      introduce ln t0 ==> ln t1
      with _ . (
        open_term_ln_inv' t0' xtm 0;
        open_term_ln t0' x;
        open_term_ln t1' x
      );
      introduce ln t1 ==> ln t0
      with _ . (
        open_term_ln_inv' t1' xtm 0;
        open_term_ln t1' x;
        open_term_ln t0' x
      )
      

let st_equiv_ln #g #c1 #c2 (d:st_equiv g c1 c2)
  : Lemma 
    (requires ln_c c1)
    (ensures ln_c c2)
  = match d with
    | ST_VPropEquiv _ _ _ x (E dpre) _dres _dpost eq_res eq_pre eq_post ->
      vprop_equiv_ln eq_pre;
      open_term_ln_inv' (comp_post c1) (term_of_no_name_var x) 0;
      vprop_equiv_ln eq_post;
      rt_equiv_ln _ _ _ eq_res;
      elab_ln_inverse (comp_res c2);
      open_term_ln' (comp_post c2) (term_of_no_name_var x) 0

    | ST_TotEquiv g t1 t2 u t1_typing eq ->
      let t2_typing = Pulse.Typing.Metatheory.Base.rt_equiv_typing eq t1_typing._0 in
      tot_or_ghost_typing_ln (E (Ghost.reveal t2_typing))
    
let prop_valid_must_be_ln (g:env) (t:term) (d:prop_validity g t)
  : Lemma (ensures ln t) =
  admit()

let rec st_sub_ln #g #c1 #c2 (d:st_sub g c1 c2)
  : Lemma
    (requires ln_c c1)
    (ensures ln_c c2)
    (decreases d)
  = match d with
    | STS_Refl _ _ -> ()

    | STS_Trans _ _ _ _ d1 d2 ->
      st_sub_ln d1;
      st_sub_ln d2

    | STS_AtomicInvs g stc is1 is2 _ _ tok ->
      prop_valid_must_be_ln g (tm_inames_subset is1 is2) tok;
      assume (ln (tm_inames_subset is1 is2) ==> ln is2)

let bind_comp_ln #g #x #c1 #c2 #c (d:bind_comp g x c1 c2 c)
  : Lemma 
    (requires ln_c c1 /\ ln_c c2)
    (ensures ln_c c)
  = ()

let st_comp_typing_ln (#g:_) (#st:_) (d:st_comp_typing g st)
  : Lemma (ensures ln_st_comp st (-1)) =
  
  let STC _ {post} x res_typing pre_typing post_typing = d in
  tot_or_ghost_typing_ln res_typing;
  tot_or_ghost_typing_ln pre_typing;
  tot_or_ghost_typing_ln post_typing;
  open_term_ln' post (null_var x) 0

let comp_typing_ln (#g:_) (#c:_) (#u:_) (d:comp_typing g c u)
  : Lemma (ensures ln_c c) =

  match d with
  | CT_Tot _ _ _ t_typing -> tot_or_ghost_typing_ln t_typing
  | CT_ST _ _ st_typing
  | CT_STGhost _ _ st_typing -> st_comp_typing_ln st_typing
  | CT_STAtomic _ _ _ _ inames_typing st_typing ->
    tot_or_ghost_typing_ln inames_typing;
    st_comp_typing_ln st_typing
#pop-options

let ln_mk_reveal (u:universe) (t:term) (e:term) (n:int)
  : Lemma
      (requires ln' t n /\ ln' e n)
      (ensures ln' (mk_reveal u t e) n) =
  admit ()

let ln_mk_fst (u:universe) (aL aR e:term) (n:int)
  : Lemma
      (requires ln' aL n /\ ln' aR n /\ ln' e n)
      (ensures ln' (mk_fst u u aL aR e) n) =
  admit ()

let ln_mk_snd (u:universe) (aL aR e:term) (n:int)
  : Lemma
      (requires ln' aL n /\ ln' aR n /\ ln' e n)
      (ensures ln' (mk_snd u u aL aR e) n) =
  admit ()

let ln_mk_ref (t:term) (n:int)
  : Lemma
      (requires ln' t n)
      (ensures ln' (mk_ref t) n) =
  admit ()

let ln_mk_array (t:term) (n:int)
  : Lemma
      (requires ln' t n)
      (ensures ln' (mk_array t) n) =
  admit ()

#push-options "--z3rlimit_factor 12 --fuel 4 --ifuel 1 --query_stats"
let rec st_typing_ln (#g:_) (#t:_) (#c:_)
                     (d:st_typing g t c)
  : Lemma 
    (ensures ln_st t /\ ln_c c)
    (decreases d)
  = match d with
    | T_Abs _g x _q ty _u body c dt db ->
      tot_or_ghost_typing_ln dt;
      st_typing_ln db;
      open_st_term_ln body x;
      close_comp_ln c x;
      Pulse.Elaborate.elab_ln ty.binder_ty (-1);
      Pulse.Elaborate.elab_ln_comp (close_comp c x) 0

    | T_STApp _ _ _ _ res arg st at
    | T_STGhostApp _ _ _ _ res arg _ st _ at ->
      tot_or_ghost_typing_ln st;
      tot_or_ghost_typing_ln at;
      // We have RT.ln' (elab_comp res),
      //   from that we need to derive the following
      assume (ln_c' res 0);
      open_comp_ln_inv' res arg 0;
      Pulse.Elaborate.elab_ln_comp (open_comp_with res arg) (-1)

    | T_Lift _ _ _ _ d1 l ->
      st_typing_ln d1;
      lift_comp_ln l

    | T_Return _ c use_eq u t e post x t_typing e_typing post_typing ->
      tot_or_ghost_typing_ln t_typing;
      tot_or_ghost_typing_ln e_typing;
      tot_or_ghost_typing_ln post_typing;
      open_term_ln' post (term_of_no_name_var x) 0;
      open_term_ln_inv' post e 0;
      if not use_eq
      then ()
      else begin
        // Add some lemmas about ln' of tm_pureapp etc.
        assume (ln' (mk_eq2 u t (null_var x) e) (-1));
        let e = tm_star
          (open_term' post (null_var x) 0)
          (tm_pure (mk_eq2 u t (null_var x) e)) in
        close_term_ln' e x 0
      end

    | T_Bind _ _ e2 _ _ _ x _ d1 dc1 d2 bc ->
      st_typing_ln d1;
      tot_or_ghost_typing_ln dc1;
      st_typing_ln d2;
      open_st_term_ln e2 x;
      bind_comp_ln bc

    | T_BindFn _g _e1 e2 _c1 _c2 _b x d1 _u dc1 d2 c ->
      st_typing_ln d1;
      tot_or_ghost_typing_ln dc1;
      st_typing_ln d2;
      open_st_term_ln e2 x;
      comp_typing_ln c

    | T_If _ _ _ _ _ _ tb d1 d2 _ ->
      tot_or_ghost_typing_ln tb;
      st_typing_ln d1;
      st_typing_ln d2

    | T_Match _ _ _ sc _ scd c _ _ _ _ ->
      tot_or_ghost_typing_ln scd;
      admit ()

    | T_Frame _ _ _ _ df dc ->
      tot_or_ghost_typing_ln df;
      st_typing_ln dc

    | T_IntroPure _ _ t _ ->
      tot_or_ghost_typing_ln t

    | T_ElimExists _ u t p x dt dv ->
      tot_or_ghost_typing_ln dt;
      tot_or_ghost_typing_ln dv;
      let x_tm = tm_var {nm_index=x;nm_ppname=ppname_default} in
      ln_mk_reveal u t x_tm (-1);
      open_term_ln_inv' p (Pulse.Typing.mk_reveal u t x_tm) 0;
      close_term_ln' (open_term' p (Pulse.Typing.mk_reveal u t x_tm) 0) x 0


    | T_IntroExists _ u t p e dt dv dw ->
      tot_or_ghost_typing_ln dt;
      tot_or_ghost_typing_ln dv;
      tot_or_ghost_typing_ln dw;
      open_term_ln_inv' p e 0

    | T_Equiv _ _ _ _ d2 deq ->
      st_typing_ln d2;
      st_equiv_ln deq

    | T_While _ inv _ _ inv_typing cond_typing body_typing ->
      tot_or_ghost_typing_ln inv_typing;
      st_typing_ln cond_typing;
      st_typing_ln body_typing;
      open_term_ln_inv' inv tm_false 0

    | T_Par _ _ cL _ cR x _ _ eL_typing eR_typing ->
      let x_tm = term_of_no_name_var x in
      let u = comp_u cL in
      let aL = comp_res cL in
      let aR = comp_res cR in
      st_typing_ln eL_typing;
      st_typing_ln eR_typing;
      ln_mk_fst u aL aR x_tm (-1);
      ln_mk_snd u aL aR x_tm (-1);
      open_term_ln_inv' (comp_post cL) (Pulse.Typing.mk_fst u u aL aR x_tm) 0;
      close_term_ln' (open_term' (comp_post cL) (Pulse.Typing.mk_fst u u aL aR x_tm) 0) x 0;
      open_term_ln_inv' (comp_post cR) (Pulse.Typing.mk_snd u u aL aR x_tm) 0;
      close_term_ln' (open_term' (comp_post cR) (Pulse.Typing.mk_snd u u aL aR x_tm) 0) x 0

    | T_Rewrite _ _ _ p_typing equiv_p_q ->
      tot_or_ghost_typing_ln p_typing;
      vprop_equiv_ln equiv_p_q

    | T_WithLocal g _ init body init_t c x init_typing init_t_typing c_typing body_typing ->
      tot_or_ghost_typing_ln init_typing;
      st_typing_ln body_typing;
      open_st_term_ln' body (null_var x) 0;
      comp_typing_ln c_typing;
      tot_or_ghost_typing_ln init_t_typing;
      ln_mk_ref init_t (-1)

    | T_WithLocalArray g _ init len body init_t c x init_typing len_typing init_t_typing c_typing body_typing ->
      tot_or_ghost_typing_ln init_typing;
      tot_or_ghost_typing_ln len_typing;
      st_typing_ln body_typing;
      open_st_term_ln' body (null_var x) 0;
      comp_typing_ln c_typing;
      tot_or_ghost_typing_ln init_t_typing;
      ln_mk_array init_t (-1)

    | T_Admit _ s _ (STC _ _ x t_typing pre_typing post_typing)
    | T_Unreachable _ s _ (STC _ _ x t_typing pre_typing post_typing) _ ->
      tot_or_ghost_typing_ln t_typing;
      tot_or_ghost_typing_ln pre_typing;
      tot_or_ghost_typing_ln post_typing;
      open_term_ln' s.post (term_of_no_name_var x) 0

    | T_Sub _ e c c' d d_sub ->
      st_typing_ln d;
      st_sub_ln d_sub

    | T_WithInv _ _ _ _ _ _ _ _ _ ->
      admit() // IOU

#pop-options
