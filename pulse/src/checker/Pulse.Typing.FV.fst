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
open Pulse.Soundness.Common

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

    | Tm_While { invariant; condition; body } ->
      freevars_close_term' invariant x (i + 1);
      freevars_close_st_term' condition x i;
      freevars_close_st_term' body x i

    | Tm_NuWhile { invariant; condition; body } ->
      freevars_close_term' invariant x i;
      freevars_close_st_term' condition x i;
      freevars_close_st_term' body x i

    | Tm_Rewrite { t1; t2; tac_opt } ->
      freevars_close_term' t1 x i;
      freevars_close_term' t2 x i;
      freevars_close_term_opt' tac_opt x i

    | Tm_WithLocal { binder; initializer; body } ->
      freevars_close_term' binder.binder_ty x i;
      freevars_close_term' initializer x i;
      freevars_close_st_term' body x (i + 1)

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      freevars_close_term' binder.binder_ty x i;
      freevars_close_term' initializer x i;
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
  (#g:_) (#t:_) (#ty:_) (#eff:_)
  (d:typing g t eff ty)
  : Lemma 
    (ensures freevars t `Set.subset` vars_of_env g /\
             freevars ty `Set.subset` vars_of_env g)
  = let E d = d in
    refl_typing_freevars d;
    assert (vars_of_env_r (elab_env g) `Set.equal` (vars_of_env g))

let tot_typing_freevars
  (#g:_) (#t:_) (#ty:_)
  (d:tot_typing g t ty)
  : Lemma 
    (ensures freevars t `Set.subset` vars_of_env g /\
             freevars ty `Set.subset` vars_of_env g)
  = tot_or_ghost_typing_freevars d

let bind_comp_freevars (#g:_) (#x:_) (#c1 #c2 #c:_)
                       (d:bind_comp g x c1 c2 c)
  : Lemma 
    (requires freevars_comp c1 `Set.subset` vars_of_env g /\
              freevars_comp c2 `Set.subset` (Set.union (vars_of_env g) (Set.singleton x)))
    (ensures freevars_comp c `Set.subset` vars_of_env g)
  = match d with
    | Bind_comp _ _ _ _ dt _ _ -> tot_or_ghost_typing_freevars dt

let rec slprop_equiv_freevars (#g:_) (#t0 #t1:_) (v:slprop_equiv g t0 t1)
  : Lemma (ensures (freevars t0 `Set.subset` vars_of_env g) <==>
                   (freevars t1 `Set.subset` vars_of_env g))
          (decreases v)
  = assume False;  // TODO: AR
    match v with
    | VE_Refl _ _ -> ()
    | VE_Sym _ _ _ v' -> 
      slprop_equiv_freevars v'
    | VE_Trans g t0 t2 t1 v02 v21 ->
      slprop_equiv_freevars v02;
      slprop_equiv_freevars v21
    | VE_Ctxt g s0 s1 s0' s1' v0 v1 ->
      slprop_equiv_freevars v0;
      slprop_equiv_freevars v1
    | VE_Unit g t -> ()
    | VE_Comm g t0 t1 -> ()
    | VE_Assoc g t0 t1 t2 -> ()
    | VE_Ext g t0 t1 token ->
      let d0, d1 = slprop_eq_typing_inversion _ _ _ token in
      tot_or_ghost_typing_freevars d0;
      tot_or_ghost_typing_freevars d1
    | VE_Fa g x u b t0 t1 d ->
      slprop_equiv_freevars d;
      close_open_inverse t0 x



let st_equiv_freevars #g (#c1 #c2:_)
                      (d:st_equiv g c1 c2)
  : Lemma
    (requires freevars_comp c1 `Set.subset` vars_of_env g)
    (ensures freevars_comp c2 `Set.subset` vars_of_env g)    
  = match d with
    | ST_SLPropEquiv _ _ _ x _ _ _ eq_res eq_pre eq_post -> (
      slprop_equiv_freevars eq_pre;
      slprop_equiv_freevars eq_post;
      freevars_open_term_inv (comp_post c1) x;
      freevars_open_term_inv (comp_post c2) x;
      refl_equiv_freevars eq_res
    )
    | ST_TotEquiv _ t1 t2 u t1_typing eq ->
      let t2_typing = Pulse.Typing.Metatheory.Base.rt_equiv_typing eq t1_typing._0 in
      tot_or_ghost_typing_freevars (E (Ghost.reveal t2_typing))
    
let prop_validity_fv (g:env) (p:term)
  : Lemma
    (requires prop_validity g p)
    (ensures freevars p `Set.subset` vars_of_env g)
  = admit()

let rec st_sub_freevars #g (#c1 #c2:_)
                      (d:st_sub g c1 c2)
  : Lemma
    (requires freevars_comp c1 `Set.subset` vars_of_env g)
    (ensures freevars_comp c2 `Set.subset` vars_of_env g)
    (decreases d)
=
  match d with
  | STS_Refl _ _ -> ()
  | STS_Trans _ _ _ _ d1 d2 ->
    st_sub_freevars d1;
    st_sub_freevars d2
  | STS_GhostInvs _ _ is1 is2 tok
  | STS_AtomicInvs _ _ is1 is2 _ _ tok ->
    assume (freevars is2 `Set.subset` freevars (tm_inames_subset is1 is2));
    prop_validity_fv g (tm_inames_subset is1 is2)

let src_typing_freevars_t (d':'a) =
    (#g:_) -> (#t:_) -> (#c:_) -> (d:st_typing g t c { d << d' }) ->
    Lemma 
    (ensures freevars_st t `Set.subset` vars_of_env g /\
             freevars_comp c `Set.subset` vars_of_env g)

let st_comp_typing_freevars #g #st (d:st_comp_typing g st)
  : Lemma
    (ensures freevars_st_comp st `Set.subset` vars_of_env g)
    (decreases d)
  = let STC _ _ x dt pre post = d in
    tot_or_ghost_typing_freevars dt;
    tot_or_ghost_typing_freevars pre;
    tot_or_ghost_typing_freevars post

let comp_typing_freevars  (#g:_) (#c:_) (#u:_)
                          (d:comp_typing g c u)
  : Lemma 
    (ensures freevars_comp c `Set.subset` vars_of_env g)
    (decreases d)
  = match d with
    | CT_Tot _ _ _ dt ->
      tot_or_ghost_typing_freevars dt

    | CT_ST _ _ dst -> 
      st_comp_typing_freevars dst

    | CT_STGhost _ _ _ it dst
    | CT_STAtomic _ _ _ _ it dst -> 
      tot_or_ghost_typing_freevars it;
      st_comp_typing_freevars dst

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

let st_typing_freevars_cb_t
  (#g0:_) (#t0:_) (#c0:_)
  (d0:st_typing g0 t0 c0)
=
  (#g:_) -> (#t:_) -> (#c:_) ->
  (d:st_typing g t c{d << d0}) ->
  Lemma (ensures freevars_st t `Set.subset` vars_of_env g /\
                 freevars_comp c `Set.subset` vars_of_env g)
  (decreases d)

let st_typing_freevars_case
  (pred : (
    (#g:_) -> (#t:_) -> (#c:_) ->
    st_typing g t c -> GTot bool))
  : Type =
  (#g:_) -> (#t:_) -> (#c:_) ->
  (d : st_typing g t c{pred d}) ->
  (cb : st_typing_freevars_cb_t d) ->
  Lemma (freevars_st t `Set.subset` vars_of_env g /\ freevars_comp c `Set.subset` vars_of_env g)

let st_typing_freevars_abs : st_typing_freevars_case T_Abs? =
fun d cb ->
  match d with
  | T_Abs _  x q ty _ body cres dt db ->
    tot_or_ghost_typing_freevars dt;
    cb db;
    freevars_close_comp cres x 0;
    freevars_open_st_term_inv body x;
    freevars_tm_arrow ty q (close_comp cres x)

#push-options "--z3rlimit_factor 20 --fuel 3 --ifuel 2 --split_queries no"
#restart-solver
let st_typing_freevars_return : st_typing_freevars_case T_Return? =
fun d cb ->
  match d with
  | T_Return _ c use_eq u t e post x t_typing e_typing post_typing ->
    tot_or_ghost_typing_freevars t_typing;
    tot_or_ghost_typing_freevars e_typing;
    tot_or_ghost_typing_freevars post_typing;
    let post_maybe_eq =
      if use_eq
      then let post = open_term' post (null_var x) 0 in
          let post = tm_star post (tm_pure (mk_eq2 u t (null_var x) e)) in
          let post = close_term post x in
          post
      else post
    in
    freevars_open_term post (null_var x) 0;
    freevars_mk_eq2 u t (null_var x) e;
    freevars_close_term
      (tm_star (open_term' post (null_var x) 0) (tm_pure (mk_eq2 u t (null_var x) e)))
      x 0;
    freevars_open_term post e 0
#pop-options
#restart-solver
#push-options "--z3rlimit_factor 4 --fuel 1 --ifuel 1 --split_queries always"
let st_typing_freevars_bind : st_typing_freevars_case T_Bind? =
fun d cb ->
  match d with
  | T_Bind _ e1 e2 _ _ _ x c d1 dc1 d2 bc ->
    cb d1;
    tot_or_ghost_typing_freevars dc1;
    cb d2;
    bind_comp_freevars bc;
    freevars_open_st_term_inv e2 x

let st_typing_freevars_bind_fn : st_typing_freevars_case T_BindFn? =
fun d cb ->
  match d with
  | T_BindFn _g _e1 e2 _c1 _c2 _b x d1 _u dc1 d2 c ->
    cb d1;
    tot_or_ghost_typing_freevars dc1;
    cb d2;
    comp_typing_freevars c;
    freevars_open_st_term_inv e2 x

let st_typing_freevars_if : st_typing_freevars_case T_If? =
fun #g #t #c d cb ->
  match d with
  | T_If _ _b e1 e2 _c hyp tb d1 d2 (E ct) ->
    assert (t.term == (Tm_If { b = _b; then_=e1; else_=e2; post=None }));
    calc (Set.subset) {
      freevars_st t;
    (==) {}
      ((Set.union (freevars _b) (freevars_st e1)) `Set.union`
      (freevars_st e2 `Set.union` freevars_term_opt None));
    (Set.equal) {}
      (freevars _b `Set.union` (freevars_st e1 `Set.union` freevars_st e2));
    (Set.subset) { tot_or_ghost_typing_freevars tb }
      (vars_of_env g `Set.union` (freevars_st e1 `Set.union` freevars_st e2));
    (Set.subset) { cb d1 ; cb d2 }
      vars_of_env g;
    };
    comp_typing_freevars ct
#pop-options
#restart-solver
#push-options "--z3rlimit_factor 8"
let st_typing_freevars_frame : st_typing_freevars_case T_Frame? =
fun d cb ->
  match d with
  | T_Frame _ _ _ _ df dc ->
    tot_or_ghost_typing_freevars df;
    cb dc
#pop-options

#restart-solver
#push-options "--z3rlimit_factor 4 --fuel 2 --ifuel 1"
let st_typing_freevars_elimexists : st_typing_freevars_case T_ElimExists? =
fun #g #t #c d cb ->
  match d with
  | T_ElimExists _ u t p x dt dv ->
    let x_tm = tm_var {nm_index=x;nm_ppname=ppname_default} in
    tot_or_ghost_typing_freevars dt;
    tot_or_ghost_typing_freevars dv;
    freevars_mk_reveal u t x_tm;
    assert (Set.equal (freevars (Pulse.Typing.mk_reveal u t x_tm))
                      (Set.union (freevars t) (Set.singleton x)));
    freevars_open_term p (Pulse.Typing.mk_reveal u t x_tm) 0;
    assert (Set.subset (freevars (open_term' p (Pulse.Typing.mk_reveal u t x_tm) 0))
                      (Set.union (freevars p)
                                (Set.union (freevars t)
                                            (Set.singleton x))));
    assert (~ (Set.mem x (freevars t)));
    assert (~ (Set.mem x (freevars p)));
    assert (Set.subset (set_minus (freevars (open_term' p (Pulse.Typing.mk_reveal u t x_tm) 0)) x)
                      (Set.union (freevars p)
                                (freevars t)));
    assert (Set.subset
              (set_minus (freevars (open_term' p (Pulse.Typing.mk_reveal u t x_tm) 0)) x)
              (vars_of_env g));
    freevars_mk_erased u t

let st_typing_freevars_introexists : st_typing_freevars_case T_IntroExists? =
fun #g #t #c d cb ->
  match d with
  | T_IntroExists _ u b p w dt dv dw ->
    tot_or_ghost_typing_freevars dt;
    tot_or_ghost_typing_freevars dv;
    tot_or_ghost_typing_freevars dw;
    assert (freevars_st t `Set.subset` vars_of_env g);
    calc (Set.subset) {
      freevars_comp c;
    (Set.equal) {}
      freevars_comp (comp_intro_exists u b p w);
    (Set.equal) {}
      freevars tm_emp_inames `Set.union`
      (freevars tm_unit `Set.union`
      (freevars (open_term' p w 0) `Set.union`
        freevars (tm_exists_sl u b p)));
    (Set.equal) {}
      (freevars (open_term' p w 0) `Set.union`
        freevars (tm_exists_sl u b p));
    (Set.subset) { freevars_open_term p w 0 }
      (freevars p `Set.union`
        freevars w `Set.union`
        freevars_st t `Set.union`
        freevars p);
    }

#push-options "--z3rlimit 20"
let st_typing_freevars_while : st_typing_freevars_case T_While? =
fun d cb ->
  match d with
  | T_While _ inv _ _ inv_typing cond_typing body_typing ->
    tot_or_ghost_typing_freevars inv_typing;
    cb cond_typing;
    cb body_typing;
    assert (freevars tm_false `Set.equal` Set.empty);
    freevars_open_term inv tm_false 0;
    assert (freevars (open_term' inv tm_false 0) `Set.subset` freevars inv)

let st_typing_freevars_nuwhile : st_typing_freevars_case T_NuWhile? =
fun d cb ->
  match d with
  | T_NuWhile _ inv post _ _ inv_typing post_typing cond_typing body_typing ->
    tot_or_ghost_typing_freevars inv_typing;
    tot_or_ghost_typing_freevars post_typing;
    cb cond_typing;
    cb body_typing;
    assert (freevars tm_false `Set.equal` Set.empty);
    freevars_open_term inv tm_false 0;
    assert (freevars (open_term' inv tm_false 0) `Set.subset` freevars inv)
#pop-options

let st_typing_freevars_rewrite : st_typing_freevars_case T_Rewrite? =
fun d cb ->
  match d with
  | T_Rewrite _ _ _ p_typing equiv_p_q ->
    tot_or_ghost_typing_freevars p_typing;
    slprop_equiv_freevars equiv_p_q

let st_typing_freevars_withlocal : st_typing_freevars_case T_WithLocal? =
fun d cb ->
  match d with
  | T_WithLocal _ _ init body init_t c x init_typing u_typing c_typing body_typing ->
    tot_or_ghost_typing_freevars init_typing;
    cb body_typing;
    freevars_open_st_term_inv body x;
    comp_typing_freevars c_typing;
    tot_or_ghost_typing_freevars u_typing;
    freevars_ref init_t

let st_typing_freevars_withlocalarray : st_typing_freevars_case T_WithLocalArray? =
fun d cb ->
  match d with
  | T_WithLocalArray _ _ init len body init_t c x init_typing len_typing u_typing c_typing body_typing ->
    tot_or_ghost_typing_freevars init_typing;
    tot_or_ghost_typing_freevars len_typing;
    cb body_typing;
    freevars_open_st_term_inv body x;
    comp_typing_freevars c_typing;
    tot_or_ghost_typing_freevars u_typing;
    freevars_array init_t

let st_typing_freevars_admit : st_typing_freevars_case T_Admit? =
fun d cb ->
  match d with
  | T_Admit _ c c_typing ->
    comp_typing_freevars c_typing;
    let st_typing, _ = Pulse.Typing.Metatheory.Base.comp_typing_inversion c_typing in
    let STC _ _ x t_typing pre_typing post_typing = st_typing in
    tot_or_ghost_typing_freevars t_typing;
    tot_or_ghost_typing_freevars post_typing;
    freevars_open_term (comp_post c) (term_of_no_name_var x) 0

let st_typing_freevars_unreachable : st_typing_freevars_case T_Unreachable? =
fun d cb ->
  match d with
  | T_Unreachable _ c c_typing _ ->
    comp_typing_freevars c_typing;
    let st_typing, _ = Pulse.Typing.Metatheory.Base.comp_typing_inversion c_typing in
    let STC _ _ x t_typing pre_typing post_typing = st_typing in
    tot_or_ghost_typing_freevars t_typing;
    tot_or_ghost_typing_freevars post_typing;
    freevars_open_term (comp_post c) (term_of_no_name_var x) 0

let rec st_typing_freevars
  (#g:_) (#t:_) (#c:_)
  (d:st_typing g t c)
: Lemma
  (ensures freevars_st t `Set.subset` vars_of_env g /\
           freevars_comp c `Set.subset` vars_of_env g)
  (decreases d)
= match d with
  | T_Abs .. ->
    st_typing_freevars_abs d st_typing_freevars
  | T_ST ..
  | T_STGhost .. -> admit()
  | T_Return .. ->
    st_typing_freevars_return d st_typing_freevars
  | T_Lift _ _ _ _ d1 _ ->
    st_typing_freevars d1
  | T_Bind .. ->
    st_typing_freevars_bind d st_typing_freevars
  | T_BindFn .. ->
    st_typing_freevars_bind_fn d st_typing_freevars
  | T_If .. ->
    st_typing_freevars_if d st_typing_freevars
  | T_Match .. ->
    admit () // IOU
  | T_Frame .. ->
    st_typing_freevars_frame d st_typing_freevars
  | T_IntroPure _ p prop_typing _ ->
    tot_or_ghost_typing_freevars prop_typing
  | T_ElimExists _ u t p x dt dv ->
    st_typing_freevars_elimexists d st_typing_freevars
  | T_IntroExists _ u b p w dt dv dw ->
    st_typing_freevars_introexists d st_typing_freevars
  | T_Equiv _ _ _ _ d2 deq ->
    st_typing_freevars d2;
    st_equiv_freevars deq
  | T_While .. ->
    st_typing_freevars_while d st_typing_freevars
  | T_NuWhile .. ->
    st_typing_freevars_nuwhile d st_typing_freevars
  | T_Rewrite .. ->
    st_typing_freevars_rewrite d st_typing_freevars
  | T_WithLocal .. ->
    st_typing_freevars_withlocal d st_typing_freevars
  | T_WithLocalArray .. ->
    st_typing_freevars_withlocalarray d st_typing_freevars
  | T_Admit .. ->
    st_typing_freevars_admit d st_typing_freevars
  | T_Unreachable _ c c_typing _ ->
    st_typing_freevars_unreachable d st_typing_freevars
  | T_Sub _ _ _ _ d_t d_sub ->
    st_typing_freevars d_t;
    st_sub_freevars d_sub