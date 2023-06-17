module Pulse.Prover.Util

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory

module L = FStar.List.Tot
module T = FStar.Tactics
module RT = FStar.Reflection.Typing
module Psubst = Pulse.Prover.Substs

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
    let g_x_t = push_binding_def (mk_env (fstar_env uvs_remaining)) x ty in
    // assert (uvs_remaining == push_env g_x_t uvs_remaining_new);
      
    let uvs_seen_new = push_binding_def uvs_seen x ty in
      
    push_env_assoc uvs_seen g_x_t uvs_remaining_new;
    assert (equal uvs (push_env uvs_seen_new uvs_remaining_new));
    assert (disjoint uvs_seen_new uvs_remaining_new);
    assume (List.Tot.length (bindings uvs_remaining_new) <
            List.Tot.length (bindings uvs_remaining));


    if not (x `Set.mem` Psubst.dom ss_remaining)
    then begin
      let uvs_unresolved_new = push_binding_def uvs_unresolved x ty in

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
        push_binding_def (mk_env (fstar_env uvs_remaining)) x (Psubst.subst_term ss_consumed ty)  in

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

let apply_partial_subs (#g0:env) (#t:st_term) (#c:comp_st)
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

let apply_partial_subs_veq (#g0:env) (#p1 #p2:vprop)
  (uvs:env { disjoint uvs g0 })
  (ss:Psubst.t g0 { well_typed_ss uvs ss })
  (veq:vprop_equiv (push_env g0 uvs) p1 p2)

  : uvs_unresolved:env { uvs_unresolved == filter_ss uvs ss } &
    vprop_equiv (push_env g0 (psubst_env uvs_unresolved ss))
                (Psubst.subst_term ss p1)
                (Psubst.subst_term ss p2) = admit ()

let idem_steps (g:env) (ctxt:vprop)
  : t:st_term &
    st_typing g t (ghost_comp ctxt (Tm_Star (list_as_vprop (vprop_as_list ctxt))
                                            Tm_Emp)) = admit ()
