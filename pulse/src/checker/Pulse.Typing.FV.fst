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

module Pulse.Typing.FV
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate

// let vars_of_rt_env (g:R.env) = Set.intension (fun x -> Some? (RT.lookup_bvar g x))

let freevars_close_term_host_term (t:term) (x:var) (i:index)
  : Lemma
    (ensures (freevars (close_term' (wr t FStar.Range.range_0) x i)
            `Set.equal`
             (freevars (wr t FStar.Range.range_0) `set_minus` x)))
  = admit()

#push-options "--z3rlimit_factor 2"
let freevars_close_term' (e:term) (x:var) (i:index)
  : Lemma 
    (ensures freevars (close_term' e x i) `Set.equal`
             (freevars e `set_minus` x))
  = freevars_close_term_host_term e x i

let freevars_close_comp (c:comp)
                        (x:var)
                        (i:index)
  : Lemma 
    (ensures freevars_comp (close_comp' c x i) `Set.equal`
             (freevars_comp c `set_minus` x))
    [SMTPat (freevars_comp (close_comp' c x i))]
  = match c with
    | C_Tot t ->
      freevars_close_term' t x i

    | C_ST s ->
      freevars_close_term' s.res x i;
      freevars_close_term' s.pre x i;      
      freevars_close_term' s.post x (i + 1)
    | C_STGhost n s
    | C_STAtomic n _ s ->
      freevars_close_term' n x i;    
      freevars_close_term' s.res x i;
      freevars_close_term' s.pre x i;      
      freevars_close_term' s.post x (i + 1)

let freevars_close_term_opt' (t:option term) (x:var) (i:index)
  : Lemma
    (ensures (freevars_term_opt (close_term_opt' t x i) `Set.equal`
             (freevars_term_opt t `set_minus` x)))
    (decreases t)
  = match t with
    | None -> ()
    | Some t -> freevars_close_term' t x i

let rec freevars_close_term_list' (t:list term) (x:var) (i:index)
  : Lemma
    (ensures (freevars_list (close_term_list' t x i) `Set.equal`
             (freevars_list t `set_minus` x)))
    (decreases t)
  = match t with
    | [] -> ()
    | hd::tl ->
      freevars_close_term' hd x i;
      freevars_close_term_list' tl x i

let rec freevars_close_term_pairs' (t:list (term & term)) (x:var) (i:index)
  : Lemma
    (ensures (freevars_pairs (close_term_pairs' t x i) `Set.equal`
             (freevars_pairs t `set_minus` x)))
    (decreases t)
  = match t with
    | [] -> ()
    | (u, v)::tl ->
      freevars_close_term' u x i;
      freevars_close_term' v x i;
      freevars_close_term_pairs' tl x i

let freevars_close_proof_hint' (ht:proof_hint_type) (x:var) (i:index)
  : Lemma
    (ensures (freevars_proof_hint (close_proof_hint' ht x i) `Set.equal`
             (freevars_proof_hint ht `set_minus` x)))
  = match ht with
    | ASSERT { p }
    | FOLD { p }
    | UNFOLD { p } ->
      freevars_close_term' p x i
    | RENAME { pairs; goal; tac_opt } ->
      freevars_close_term_pairs' pairs x i;
      freevars_close_term_opt' goal x i;
      freevars_close_term_opt' tac_opt x i
    | REWRITE { t1; t2; tac_opt } ->
      freevars_close_term' t1 x i;
      freevars_close_term' t2 x i;
      freevars_close_term_opt' tac_opt x i
    | WILD
    | SHOW_PROOF_STATE _ -> ()

// Needs a bit more rlimit sometimes. Also splitting is too expensive
#push-options "--z3rlimit 20 --split_queries always"
#restart-solver
let rec freevars_close_st_term' (t:st_term) (x:var) (i:index)
  : Lemma
    (ensures (freevars_st (close_st_term' t x i) `Set.equal`
             (freevars_st t `set_minus` x)))
    (decreases t)
  = match t.term with
    | Tm_Return { expected_type; term } ->
      freevars_close_term' expected_type x i;
      freevars_close_term' term x i

    | Tm_ST { t; args } -> 
      freevars_close_term' t x i;
      admit ()
    
    | Tm_Abs { b; ascription=c; body } ->
      freevars_close_term' b.binder_ty x i;
      (
        match c.annotated with
        | None -> ()
        | Some c ->
          freevars_close_comp c x (i + 1)
      );
      (
        match c.elaborated with
        | None -> ()
        | Some c ->
          freevars_close_comp c x (i + 1)
      );
      freevars_close_st_term' body x (i + 1)
    
    | Tm_Bind { binder; head; body } ->
      freevars_close_term' binder.binder_ty x i;
      freevars_close_st_term' head x i;
      freevars_close_st_term' body x (i + 1)
    
    | Tm_TotBind { binder; head; body } ->
      freevars_close_term' binder.binder_ty x i;
      freevars_close_term' head x i;
      freevars_close_st_term' body x (i + 1)

    | Tm_If { b; then_; else_; post } ->
      freevars_close_term' b x i;    
      freevars_close_st_term' then_ x i;    
      freevars_close_st_term' else_ x i;          
      freevars_close_term_opt' post x (i + 1)      

    | Tm_Match _ ->
      admit ()

    | Tm_IntroPure { p } 
    | Tm_ElimExists { p } ->
      freevars_close_term' p x i
      
    | Tm_IntroExists { p; witnesses } ->
      freevars_close_term' p x i;
      freevars_close_term_list' witnesses x i

    | Tm_While { invariant; loop_requires; meas; condition; body } ->
      freevars_close_term' invariant x i;
      freevars_close_term' loop_requires x i;
      freevars_close_term_list' meas x i;
      freevars_close_st_term' condition x i;
      freevars_close_st_term' body x i

    | Tm_Rewrite { t1; t2; tac_opt } ->
      freevars_close_term' t1 x i;
      freevars_close_term' t2 x i;
      freevars_close_term_opt' tac_opt x i

    | Tm_WithLocal { binder; initializer; body } ->
      freevars_close_term' binder.binder_ty x i;
      freevars_close_term_opt' initializer x i;
      freevars_close_st_term' body x (i + 1)

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      freevars_close_term' binder.binder_ty x i;
      freevars_close_term_opt' initializer x i;
      freevars_close_term' length x i;
      freevars_close_st_term' body x (i + 1)

    | Tm_Admit { typ; post } ->
      freevars_close_term' typ x i;
      freevars_close_term_opt' post x (i + 1)
    
    | Tm_Unreachable {c} ->
      freevars_close_comp c x i

    | Tm_ProofHintWithBinders { binders; hint_type; t } ->
      let n = L.length binders in
      freevars_close_proof_hint' hint_type x (i + n);
      freevars_close_st_term' t x (i + n)

    | Tm_PragmaWithOptions { body } ->
      freevars_close_st_term' body x i

    | Tm_ForwardJumpLabel { lbl; body; post } ->
      freevars_close_comp post x i;
      freevars_close_st_term' body x (i + 1);
      admit ()
    
    | Tm_Goto { lbl; arg } ->
      freevars_close_term' lbl x i;
      freevars_close_term' arg x i
#pop-options

let freevars_close_term (e:term) (x:var) (i:index)
  : Lemma 
    (ensures freevars (close_term' e x i) `Set.equal`
             (freevars e `set_minus` x))
  = freevars_close_term' e x i

let freevars_open_term_inv (e:term) 
                           (x:var {~ (x `Set.mem` freevars e) })
  : Lemma 
    (ensures freevars e `Set.equal` (freevars (open_term e x) `set_minus` x))
    [SMTPat (freevars (open_term e x))]
  = calc (==) {
     freevars e;
     (==) {  close_open_inverse e x }
     freevars (close_term (open_term e x) x);
     (==) {  freevars_close_term (open_term e x) x 0 }
     freevars (open_term e x) `set_minus` x;
    }

assume
val freevars_open_term (e:term) (x:term) (i:index)
  : Lemma (freevars (open_term' e x i) `Set.subset` 
           (freevars e `Set.union` freevars x))
    [SMTPat (freevars (open_term' e x i))]

let freevars_open_term_both (x:var) (t:term)
: Lemma (freevars (open_term t x) `Set.subset` (freevars t `Set.union` Set.singleton x) /\
         freevars t `Set.subset` freevars (open_term t x))
= admit()

let freevars_close_st_term e x i = freevars_close_st_term' e x i

let contains_r (g:R.env) (x:var) = Some? (RT.lookup_bvar g x)
assume val vars_of_env_r (g:R.env) :
  s:Set.set var { forall x. Set.mem x s <==> contains_r g x } // = Set.intension (contains_r g)

assume
val refl_typing_freevars (#g:R.env) (#e:R.term) (#t:R.term) (#eff:_) 
                         (_:RT.typing g e (eff, t))
  : Lemma 
    (ensures RT.freevars e `Set.subset` (vars_of_env_r g) /\
             RT.freevars t `Set.subset` (vars_of_env_r g))

assume
val refl_equiv_freevars (#g:R.env) (#e1 #e2:R.term) (d:RT.equiv g e1 e2)
  : Lemma (RT.freevars e1 `Set.subset` (vars_of_env_r g) /\
           RT.freevars e2 `Set.subset` (vars_of_env_r g))



assume
val freevars_open_comp (c:comp) (x:term) (i:index)
  : Lemma 
    (ensures
      freevars_comp (open_comp' c x i) `Set.subset` 
      (freevars_comp c `Set.union` freevars x))
    [SMTPat (freevars_comp (open_comp' c x i))]

#push-options "--fuel 2 --ifuel 2"
let tot_or_ghost_typing_freevars
  (g:env) (t:term) (ty:term) (eff:FStar.Tactics.V2.tot_or_ghost)
  : Lemma 
    (ensures freevars t `Set.subset` vars_of_env g /\
             freevars ty `Set.subset` vars_of_env g)
  = admit ()

let tot_typing_freevars
  (g:env) (t:term) (ty:term)
  : Lemma 
    (ensures freevars t `Set.subset` vars_of_env g /\
             freevars ty `Set.subset` vars_of_env g)
  = admit ()

let bind_comp_freevars (g:env) (x:var) (c1:comp) (c2:comp) (c:comp)
  : Lemma 
    (requires freevars_comp c1 `Set.subset` vars_of_env g /\
              freevars_comp c2 `Set.subset` (Set.union (vars_of_env g) (Set.singleton x)))
    (ensures freevars_comp c `Set.subset` vars_of_env g)
  = admit ()

let slprop_equiv_freevars (g:env) (t0:term) (t1:term)
  : Lemma (ensures (freevars t0 `Set.subset` vars_of_env g) <==>
                   (freevars t1 `Set.subset` vars_of_env g))
  = admit ()



let st_equiv_freevars (g:env) (c1:comp) (c2:comp)
  : Lemma
    (requires freevars_comp c1 `Set.subset` vars_of_env g)
    (ensures freevars_comp c2 `Set.subset` vars_of_env g)    
  = admit ()
    
let prop_validity_fv (g:env) (p:term)
  : Lemma
    (requires prop_validity g p)
    (ensures freevars p `Set.subset` vars_of_env g)
  = admit()

let st_sub_freevars (g:env) (c1:comp) (c2:comp)
  : Lemma
    (requires freevars_comp c1 `Set.subset` vars_of_env g)
    (ensures freevars_comp c2 `Set.subset` vars_of_env g)
  = admit ()

let src_typing_freevars_t (d':'a) =
    (g:env) -> (t:st_term) -> (c:comp) ->
    Lemma 
    (ensures freevars_st t `Set.subset` vars_of_env g /\
             freevars_comp c `Set.subset` vars_of_env g)

let st_comp_typing_freevars (g:env) (st:st_comp)
  : Lemma
    (ensures freevars_st_comp st `Set.subset` vars_of_env g)
  = admit ()

let comp_typing_freevars  (g:env) (c:comp) (u:universe)
  : Lemma 
    (ensures freevars_comp c `Set.subset` vars_of_env g)
  = admit ()

let freevars_open_st_term_inv (e:st_term) 
                              (x:var {~ (x `Set.mem` freevars_st e) })
  : Lemma 
    (ensures freevars_st e `Set.equal` (freevars_st (open_st_term e x) `set_minus` x))
    [SMTPat (freevars_st (open_st_term e x))]
  = calc (==) {
     freevars_st e;
     (==) {  close_open_inverse_st e x }
     freevars_st (close_st_term (open_st_term e x) x);
     (==) {  freevars_close_st_term' (open_st_term e x) x 0 }
     freevars_st (open_st_term e x) `set_minus` x;
    }
#pop-options
#pop-options

let freevars_tm_arrow (b:binder) (q:option qualifier) (c:comp)
  : Lemma (freevars (tm_arrow b q c) ==
           Set.union (freevars b.binder_ty)
                     (freevars_comp c)) =
  admit ()

let freevars_mk_eq2 (u:universe) (t e0 e1:term)
  : Lemma (freevars (mk_eq2 u t e0 e1) ==
           Set.union (freevars t)
                     (Set.union (freevars e0)
                                (freevars e1))) =
  admit()

let freevars_mk_reveal (u:universe) (t x_tm:term)
  : Lemma (freevars (Pulse.Typing.mk_reveal u t x_tm) ==
           Set.union (freevars t) (freevars x_tm)) =
  admit ()

let freevars_mk_erased (u:universe) (t:term)
  : Lemma (freevars (mk_erased u t) == freevars t) =
  admit ()

let freevars_mk_fst (uL uR:universe) (aL aR x_tm:term)
  : Lemma (freevars (Pulse.Typing.mk_fst uL uR aL aR x_tm) ==
           Set.union (freevars aL)
                     (Set.union (freevars aR)
                                (freevars x_tm))) =
  admit ()

let freevars_mk_snd (uL uR:universe) (aL aR x_tm:term)
  : Lemma (freevars (Pulse.Typing.mk_snd uL uR aL aR x_tm) ==
           Set.union (freevars aL)
                     (Set.union (freevars aR)
                                (freevars x_tm))) =
  admit ()

let freevars_mk_tuple2 (uL uR:universe) (aL aR:term)
  : Lemma (freevars (mk_tuple2 uL uR aL aR) ==
           Set.union (freevars aL) (freevars aR)) =
  admit ()

let freevars_ref (t:term)
  : Lemma (freevars (mk_ref t) == freevars t)
  = admit()

let freevars_array (t:term)
  : Lemma (freevars (mk_array t) == freevars t)
  = admit()


(*****************************************************************************)

(** Big lemma follows. We have to split it to make it digestible to SMT. *)

let st_typing_freevars
  (g:env) (t:st_term) (c:comp)
: Lemma
  (ensures freevars_st t `Set.subset` vars_of_env g /\
           freevars_comp c `Set.subset` vars_of_env g)
= admit ()