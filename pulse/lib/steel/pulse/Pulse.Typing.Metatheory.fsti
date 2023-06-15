module Pulse.Typing.Metatheory
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

let comp_typing_u (g:env) (c:comp_st) = comp_typing g c (comp_u c)

val admit_comp_typing (g:env) (c:comp_st)
  : comp_typing_u g c
  
val st_typing_correctness (#g:env) (#t:st_term) (#c:comp_st) 
                          (_:st_typing g t c)
  : comp_typing_u g c

val comp_typing_inversion (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
  : st_comp_typing g (st_comp_of_comp c)

let fresh_wrt (x:var) (g:env) (vars:_) = 
    None? (lookup g x) /\  ~(x `Set.mem` vars)
    
val st_comp_typing_inversion_cofinite (#g:env) (#st:_) (ct:st_comp_typing g st)
  : (universe_of g st.res st.u &
     tot_typing g st.pre Tm_VProp &
     (x:var{fresh_wrt x g (freevars st.post)} -> //this part is tricky, to get the quantification on x
       tot_typing (push_binding g x st.res) (open_term st.post x) Tm_VProp))

val st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st)
  : (universe_of g st.res st.u &
     tot_typing g st.pre Tm_VProp &
     x:var{fresh_wrt x g (freevars st.post)} &
     tot_typing (push_binding g x st.res) (open_term st.post x) Tm_VProp)

val tm_exists_inversion (#g:env) (#u:universe) (#ty:term) (#p:term) 
                        (_:tot_typing g (Tm_ExistsSL u (as_binder ty) p) Tm_VProp)
                        (x:var { fresh_wrt x g (freevars p) } )
  : universe_of g ty u &
    tot_typing (push_binding g x ty) p Tm_VProp

val tot_typing_weakening (#g:env) (#t:term) (#ty:term)
                         (x:var { fresh_wrt x g Set.empty })
                         (x_t:typ)
                         (_:tot_typing g t ty)
   : tot_typing (push_binding g x x_t) t ty

val pure_typing_inversion (#g:env) (#p:term) (_:tot_typing g (Tm_Pure p) Tm_VProp)
   : tot_typing g p (Tm_FStar FStar.Reflection.Typing.tm_prop Range.range_0)


let comp_st_with_post (c:comp_st) (post:term) : c':comp_st { st_comp_of_comp c' == ({ st_comp_of_comp c with post} <: st_comp) } =
  match c with
  | C_ST st -> C_ST { st with post }
  | C_STGhost i st -> C_STGhost i { st with post }
  | C_STAtomic i st -> C_STAtomic i {st with post}

let comp_st_with_pre (c:comp_st) (pre:term) : comp_st =
  match c with
  | C_ST st -> C_ST { st with pre }
  | C_STGhost i st -> C_STGhost i { st with pre }
  | C_STAtomic i st -> C_STAtomic i {st with pre }


let vprop_equiv_x g t p1 p2 =
  x:var { fresh_wrt x g (freevars p1) } ->
  vprop_equiv (push_binding g x t)
              (open_term p1 x)
              (open_term p2 x)

let st_typing_equiv_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                         (#post:term )//{ freevars post `Set.subset` freevars (comp_post c)}
                         (veq: vprop_equiv_x g (comp_res c) (comp_post c) post)
  : st_typing g t (comp_st_with_post c post)
  = admit()

let st_typing_equiv_pre (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                        (#pre:term )
                        (veq: vprop_equiv g (comp_pre c) pre)
  : st_typing g t (comp_st_with_pre c pre)
  = admit()


///// Substitution lemma /////

module Psubst = Pulse.Prover.Substs

module L = FStar.List.Tot
let map_opt (#a #b:Type) (f:a -> b) (x:option a) : option b =
  match x with
  | None -> None
  | Some x -> Some (f x)

let subst_flip ss t = subst_term t ss

val subst_env (en:env) (ss:subst)
  : en':env { fstar_env en == fstar_env en' /\
              dom en == dom en' }
  //             (forall (x:var).{:pattern lookup en' x}
  //                              lookup en' x ==
  //                              map_opt (subst_flip ss) (lookup en x)) }
  // = admit ()

module RT = FStar.Reflection.Typing
let subst_env_mk_env (f:RT.fstar_top_env) (ss:subst)
  : Lemma (subst_env (mk_env f) ss == mk_env f)
          [SMTPat (subst_env (mk_env f) ss)] = admit ()

let well_typed_ss (#g:env) (g':env) (ss:Psubst.t g) =

  forall (x:var).{:pattern Set.mem x (Psubst.dom ss) }
  Set.mem x (Psubst.dom ss) ==> (x `Set.mem` dom g' /\
                                (let Some t = lookup g' x in
                                 tot_typing g (Psubst.lookup ss x)
                                              (Psubst.subst_term ss t)))

let pairwise_disjoint (g g' g'':env) =
  disjoint g g' /\ disjoint g' g'' /\ disjoint g g''

let singleton_env (f:_) (x:var) (t:typ) = push_binding (mk_env f) x t

let nt (x:var) (t:term) = [ NT x t ]

let st_typing_subst
  (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
(e_typing:tot_typing g e t)
  (#e1:st_term) (#c1:comp_st)
  (e1_typing:st_typing (push_env g (push_env (singleton_env (fstar_env g) x t) g')) e1 c1)

  : st_typing (push_env g (subst_env g' (nt x e)))
              (subst_st_term e1 (nt x e))
              (subst_comp c1 (nt x e)) =
  
  admit ()

let psubst_env (#g0:_) (g:env) (ss:Psubst.t g0) =
  subst_env g (Psubst.as_subst ss)

// different from extends, g1 may have dropped bindings from anywhere, not just the end
let subenv (g1 g2:env) =
  fstar_env g1 == fstar_env g2 /\
  (forall (x:var).{:pattern Set.mem x (dom g1)}
                  Set.mem x (dom g1) ==>
                  (Set.mem x (dom g2) /\
                   lookup g1 x == lookup g2 x))

let rec filter_ss (#g0:env) (g:env) (ss:Psubst.t g0)
  : Tot (g':env { subenv g' g /\ Set.disjoint (dom g') (Psubst.dom ss) })
        (decreases bindings g) =

  match bindings g with
  | [] -> mk_env (fstar_env g)
  | _ ->
    let ( x, t, g ) = remove_latest_binding g in
    let g = filter_ss g ss in
    if Set.mem x (Psubst.dom ss) then g
    else push_binding g x t

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y === x} = x

let push_subst_env (#g:_) (s1 s2:Psubst.t g) (g':env)
  : Lemma (requires Set.disjoint (Psubst.dom s1) (Psubst.dom s2))
          (ensures psubst_env g' (Psubst.push s1 s2) ==
                   psubst_env (psubst_env g' s1) s2)
          [SMTPat (psubst_env (psubst_env g' s1) s2)] = admit ()

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec apply_partial_psubs_aux (g0:env) (t:st_term) (c:comp_st)
  (uvs:env { disjoint uvs g0 })
  (ss:Psubst.t g0 { well_typed_ss uvs ss })

  (ss_consumed:Psubst.t g0)
  (ss_remaining:Psubst.t g0 { Set.disjoint (Psubst.dom ss_consumed) (Psubst.dom ss_remaining) /\
                              ss == Psubst.push ss_consumed ss_remaining })

  (uvs_seen:env { Set.subset (Psubst.dom ss_consumed) (dom uvs_seen) })
  (uvs_remaining:env { disjoint uvs_seen uvs_remaining /\
                       uvs == push_env uvs_seen uvs_remaining /\
                       Psubst.dom ss_remaining `Set.subset` dom uvs_remaining })

  (uvs_unresolved:env { uvs_unresolved == filter_ss uvs_seen ss_consumed })

  (t_typing:
     st_typing (push_env g0 (psubst_env (push_env uvs_unresolved uvs_remaining) ss_consumed))
               (Psubst.subst_st_term ss_consumed t)
               (Psubst.subst_comp ss_consumed c))
  
  : Tot (uvs_unresolved:env { uvs_unresolved == filter_ss uvs ss } &
         st_typing (push_env g0 (psubst_env uvs_unresolved ss))
                   (Psubst.subst_st_term ss t)
                   (Psubst.subst_comp ss c))
        (decreases List.Tot.length (bindings uvs_remaining)) =
  
  match bindings uvs_remaining with
  | [] ->
    assert (equal uvs_remaining (mk_env (fstar_env g0)));
    assert (Psubst.equal ss_remaining (Psubst.empty g0));
    assert (Psubst.equal (Psubst.push ss_consumed (Psubst.empty g0)) ss_consumed);
    assert (Psubst.equal ss_consumed ss);
    assert (equal uvs_seen uvs);
    assert (equal (push_env uvs_unresolved uvs_remaining) uvs_unresolved);
    (| uvs_unresolved, t_typing |)
  | _ ->
    let (x, ty, uvs_remaining_new) = remove_binding uvs_remaining in
    let g_x_t = push_binding (mk_env (fstar_env uvs_remaining)) x ty in
    // assert (uvs_remaining == push_env g_x_t uvs_remaining_new);
      
    let uvs_seen_new = push_binding uvs_seen x ty in
      
    push_env_assoc uvs_seen g_x_t uvs_remaining_new;
    assert (equal uvs (push_env uvs_seen_new uvs_remaining_new));
    assert (disjoint uvs_seen_new uvs_remaining_new);
    assume (List.Tot.length (bindings uvs_remaining_new) <
            List.Tot.length (bindings uvs_remaining));


    if not (x `Set.mem` Psubst.dom ss_remaining)
    then begin
      let uvs_unresolved_new = push_binding uvs_unresolved x ty in

      push_env_assoc uvs_unresolved g_x_t uvs_remaining_new;
      assert (equal (push_env uvs_unresolved uvs_remaining)
                    (push_env uvs_unresolved_new uvs_remaining_new));

      // assert (~ (x `Set.mem` Psubst.dom (ss_consumed)));
      // (assert (let x', ty', g' = remove_latest_binding uvs_seen_new in
      //          x == x' /\ ty == ty' /\ equal g' uvs_seen));
      // This should be easy, with the commented assert above,
      //   but my guess is some z3 loop
      assume (equal uvs_unresolved_new (filter_ss uvs_seen_new ss_consumed));

      let t_typing:
        st_typing (push_env g0 (psubst_env (push_env uvs_unresolved_new uvs_remaining_new) ss_consumed))
                  (Psubst.subst_st_term ss_consumed t)
                  (Psubst.subst_comp ss_consumed c) =
        coerce_eq t_typing () in

      apply_partial_psubs_aux g0 t c uvs ss ss_consumed ss_remaining
        uvs_seen_new uvs_remaining_new uvs_unresolved_new t_typing
    end
    else begin
      let e = Psubst.lookup ss_remaining x in
      assume (freevars e `Set.subset` dom g0);

      assert (equal (psubst_env (push_env uvs_unresolved uvs_remaining) ss_consumed)
                    (psubst_env (push_env uvs_unresolved (push_env g_x_t uvs_remaining_new)) ss_consumed));

      let g_x_ss_t =
        push_binding (mk_env (fstar_env uvs_remaining)) x (Psubst.subst_term ss_consumed ty)  in

      assume (psubst_env (push_env uvs_unresolved (push_env g_x_t uvs_remaining_new)) ss_consumed ==
              push_env (psubst_env uvs_unresolved ss_consumed)
                       (push_env g_x_ss_t (psubst_env uvs_remaining_new ss_consumed)));

      push_env_assoc g0 (psubst_env uvs_unresolved ss_consumed)
                        (push_env g_x_ss_t (psubst_env uvs_remaining_new ss_consumed));

      assert (equal (push_env g0 (psubst_env (push_env uvs_unresolved uvs_remaining) ss_consumed))
                    (push_env (push_env g0 (psubst_env uvs_unresolved ss_consumed))
                              (push_env g_x_ss_t (psubst_env uvs_remaining_new ss_consumed))));

      assert (equal g_x_ss_t (singleton_env (fstar_env g0) x (Psubst.subst_term ss_consumed ty)));

      // Needs psubst enhancement
      let s_x_e = Psubst.singleton g0 x e in
      assume (Psubst.as_subst s_x_e == nt x e);

      let t_typing:
        st_typing (push_env (push_env g0 (psubst_env uvs_unresolved ss_consumed))
                            (psubst_env (psubst_env uvs_remaining_new ss_consumed)
                                        s_x_e))
                  (Psubst.subst_st_term s_x_e (Psubst.subst_st_term ss_consumed t))
                  (Psubst.subst_comp s_x_e (Psubst.subst_comp ss_consumed c)) =
        st_typing_subst (push_env g0 (psubst_env uvs_unresolved ss_consumed))
                        x
                        (Psubst.subst_term ss_consumed ty)
                        (psubst_env uvs_remaining_new ss_consumed)
                        #e
                        (magic ())  // tricky, how do we know typedness of (ss_consumed ty)
                                    // may be need a refined notion of well-typedness of substitution
                        #(Psubst.subst_st_term ss_consumed t)
                        #(Psubst.subst_comp ss_consumed c)
                        (coerce_eq t_typing ()) in

      assume (Set.disjoint (Psubst.dom s_x_e) (Psubst.dom ss_consumed));
      let ss_consumed_new = Psubst.push ss_consumed s_x_e in

      // // This requires some more work, we need to say prefix is closed
      assume (psubst_env uvs_unresolved ss_consumed ==
              psubst_env uvs_unresolved ss_consumed_new);

      let t_typing:
        st_typing (push_env (push_env g0 (psubst_env uvs_unresolved ss_consumed_new))
                            (psubst_env uvs_remaining_new ss_consumed_new))
                  (Psubst.subst_st_term ss_consumed_new t)
                  (Psubst.subst_comp ss_consumed_new c) = coerce_eq t_typing () in
      
      push_env_assoc g0 (psubst_env uvs_unresolved ss_consumed_new)
                        (psubst_env uvs_remaining_new ss_consumed_new);

      assume (push_env (psubst_env uvs_unresolved ss_consumed_new)
                       (psubst_env uvs_remaining_new ss_consumed_new) ==
              psubst_env (push_env uvs_unresolved uvs_remaining_new) ss_consumed_new);

      let t_typing:
        st_typing (push_env g0 (psubst_env (push_env uvs_unresolved uvs_remaining_new) ss_consumed_new))
                  (Psubst.subst_st_term ss_consumed_new t)
                  (Psubst.subst_comp ss_consumed_new c) = coerce_eq t_typing () in
      
      let ss_remaining_new = Psubst.diff ss_remaining s_x_e in

      assert (Set.disjoint (Psubst.dom ss_consumed_new) (Psubst.dom ss_remaining_new));
      assert (Psubst.equal ss (Psubst.push ss_consumed_new ss_remaining_new));
      assert (Psubst.dom ss_remaining_new `Set.subset` dom uvs_remaining_new);
      assume (equal uvs_unresolved (filter_ss uvs_seen_new ss_consumed_new));

      apply_partial_psubs_aux g0 t c uvs ss
        ss_consumed_new ss_remaining_new uvs_seen_new uvs_remaining_new uvs_unresolved t_typing
    end

let apply_partial_subs (g0:env) (t:st_term) (c:comp_st)
  (uvs:env { disjoint uvs g0 })
  (ss:Psubst.t g0 { well_typed_ss uvs ss })
  (t_typing:st_typing (push_env g0 uvs) t c)

  : uvs_unresolved:env { uvs_unresolved == filter_ss uvs ss } &
    st_typing (push_env g0 (psubst_env uvs_unresolved ss))
              (Psubst.subst_st_term ss t)
              (Psubst.subst_comp ss c) =
  
  let ss_consumed = Psubst.empty g0 in
  let ss_remaining = ss in
  let uvs_seen = mk_env (fstar_env uvs) in
  let uvs_remaining = uvs in
  let uvs_unresolved = mk_env (fstar_env uvs) in

  assert (Set.disjoint (Psubst.dom ss_consumed) (Psubst.dom ss_remaining));
  assert (Psubst.equal ss (Psubst.push ss_consumed ss_remaining));
  assert (Set.subset (Psubst.dom ss_consumed) (dom uvs_seen));
  assert (disjoint uvs_seen uvs_remaining);
  assert (equal uvs (push_env uvs_seen uvs_remaining));
  assert (Psubst.dom ss_remaining `Set.subset` dom uvs_remaining);
  assert (equal uvs_unresolved (filter_ss uvs_seen ss_consumed));
  assert (equal (push_env uvs_unresolved uvs_remaining) uvs);
  assume (psubst_env uvs ss_consumed == uvs);
  assume (Psubst.subst_st_term ss_consumed t == t);
  assume (Psubst.subst_comp ss_consumed c == c);
  apply_partial_psubs_aux g0 t c uvs ss ss_consumed ss_remaining
    uvs_seen uvs_remaining uvs_unresolved t_typing


// let ss_covers_g' (ss:nt_subst) (g':env) =
//   forall (x:var). x `Set.mem` dom g' ==> Some? (lookup_nt_subst ss x)

// let tot_typing_subst (g:env) (g':env) (g'':env { pairwise_disjoint g g' g'' })
//   (#e1:term) (#t1:typ)
//   (e1_typing:tot_typing (push_env g (push_env g' g'')) e1 t1)
//   (ss:nt_subst { well_typed_ss g g' ss /\ ss_covers_g' ss g' })
//   : tot_typing (push_env g (subst_env g'' ss)) (subst_term e1 ss) (subst_term t1 ss) = admit ()
  
// let rec st_typing_subst (g:env) (g':env) (g'':env { pairwise_disjoint g g' g'' })
//   (#e1:st_term) (#c1:comp_st)
//   (e1_typing:st_typing (push_env g (push_env g' g'')) e1 c1)
//   (ss:nt_subst { well_typed_ss g g' ss /\ ss_covers_g' ss g' })
//   : st_typing (push_env g (subst_env g'' ss)) (subst_st_term e1 ss) (subst_comp c1 ss) =

//   match e1_typing with
//   | T_Abs _ x q b u body c b_ty_typing body_typing ->
//     let b_ty_typing
//       : tot_typing (push_env g g'')
//                    (subst_term b.binder_ty ss)
//                    (tm_type u) = tot_typing_subst g g' g'' b_ty_typing ss in
    
//     let g1 : env = push_binding (push_env g (push_env g' g'')) x (subst_term b.binder_ty ss) in
//     let g2 : env = push_env g (push_env g' (push_binding g'' x (subst_term b.binder_ty ss))) in
//     assume (bindings g1 == bindings g2);
  
//     let body_typing
//       : st_typing g1 (open_st_term_nv (subst_st_term body ss) (b.binder_ppname, x)) (subst_comp c ss)
//       = st_typing_subst g g' (push_binding g'' x (subst_term b.binder_ty ss)) body_typing ss in

//     T_Abs _ x q (subst_binder b ss) u (subst_st_term body ss) (subst_comp c ss)
//           b_ty_typing body_typing

//   | T_STApp _ head ty q res arg head_typing arg_typing ->
//     assume (subst_term (tm_arrow (as_binder ty) q res) ss ==
//             tm_arrow (as_binder (subst_term ty ss)) q (subst_comp res ss));
//     assume (subst_comp (open_comp_with res arg) ss ==
//             open_comp_with (subst_comp res ss) (subst_term arg ss));
//     T_STApp _ (subst_term head ss) (subst_term ty ss) q
//               (subst_comp res ss) (subst_term arg ss)
//               (tot_typing_subst g g' g'' head_typing ss)
//               (tot_typing_subst g g' g'' arg_typing ss)

//   | _ -> admit ()

// let veq_subst (g:env) (g':env) (g'':env { pairwise_disjoint g g' g'' })
//   (#p1 #p2:vprop)
//   (veq:vprop_equiv (push_env g (push_env g' g'')) p1 p2)
//   (ss:nt_subst { well_typed_ss g g' ss /\ ss_covers_g' ss g' })
//   : vprop_equiv (push_env g (subst_env g'' ss)) (subst_term p1 ss) (subst_term p2 ss) = admit ()

// let st_subst_partial (g:env) (g':env) (g'':env { pairwise_disjoint g g' g'' })
//   (#e1:st_term) (#c1:comp_st)
//   (e1_typing:st_typing (push_env g (push_env g' g'')) e1 c1)
//   (ss:nt_subst { well_typed_ss g g' ss })
//   : st_typing (push_env g (push_env g' (subst_env g'' ss))) (subst_st_term e1 ss) (subst_comp c1 ss) =
//   admit ()

// let veq_subst_partial (g:env) (g':env) (g'':env { pairwise_disjoint g g' g'' })
//   (#p1 #p2:vprop)
//   (veq:vprop_equiv (push_env g (push_env g' g'')) p1 p2)
//   (ss:nt_subst { well_typed_ss g g' ss })
//   : vprop_equiv (push_env g (push_env g' (subst_env g'' ss))) (subst_term p1 ss) (subst_term p2 ss) = admit ()

// val ss_extends (s1 s2:nt_subst) : bool

// val ss_extends_subst (g:env) (g':env) (g'':env { g'' `env_extends` g' /\
//                                                  disjoint g g' /\
//                                                  disjoint g g'' })
//   (s':nt_subst)
//   (s'':nt_subst { s'' `ss_extends` s' /\
//                   well_typed_ss g g' s' /\
//                   well_typed_ss g g'' s'' })
//   (t:term { freevars (subst_term t s') `Set.subset` dom g })
//   : Lemma (subst_term t s' == subst_term t s'')

