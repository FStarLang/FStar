module Pulse.Prover.Util

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv

module L = FStar.List.Tot
module T = FStar.Tactics
module RT = FStar.Reflection.Typing
module Psubst = Pulse.Prover.Substs

let subst_env_mk_env (f:RT.fstar_top_env) (ss:subst)
  : Lemma (subst_env (mk_env f) ss == mk_env f)
          [SMTPat (subst_env (mk_env f) ss)] = admit ()

let well_typed_ss (#g:env) (g':env) (ss:Psubst.t g) =

  forall (x:var).{:pattern Set.mem x (Psubst.dom ss) }
  Set.mem x (Psubst.dom ss) ==> (x `Set.mem` dom g' /\
                                (let Some t = lookup g' x in
                                 tot_typing g (Psubst.lookup ss x)
                                              (Psubst.subst_term ss t)))


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
    else push_binding g x ppname_default t

val push_subst_env (#g:_) (s1 s2:Psubst.t g) (g':env)
  : Lemma (requires Set.disjoint (Psubst.dom s1) (Psubst.dom s2))
          (ensures psubst_env g' (Psubst.push s1 s2) ==
                   psubst_env (psubst_env g' s1) s2)
          [SMTPat (psubst_env (psubst_env g' s1) s2)]

val apply_partial_subs (#g0:env) (#t:st_term) (#c:comp_st)
  (uvs:env { disjoint uvs g0 })
  (ss:Psubst.t g0 { well_typed_ss uvs ss })
  (t_typing:st_typing (push_env g0 uvs) t c)

  : uvs_unresolved:env { uvs_unresolved == filter_ss uvs ss } &
    st_typing (push_env g0 (psubst_env uvs_unresolved ss))
              (Psubst.subst_st_term ss t)
              (Psubst.subst_comp ss c)

val apply_partial_subs_veq (#g0:env) (#p1 #p2:vprop)
  (uvs:env { disjoint uvs g0 })
  (ss:Psubst.t g0 { well_typed_ss uvs ss })
  (veq:vprop_equiv (push_env g0 uvs) p1 p2)

  : uvs_unresolved:env { uvs_unresolved == filter_ss uvs ss } &
    vprop_equiv (push_env g0 (psubst_env uvs_unresolved ss))
                (Psubst.subst_term ss p1)
                (Psubst.subst_term ss p2)

let ghost_comp pre post : c:comp_st { comp_pre c == pre /\ comp_post c == post } = 
  C_STGhost Tm_EmpInames { u=u_zero; res=tm_unit; pre; post }


val idem_steps (g:env) (ctxt:vprop)
  : t:st_term &
    st_typing g t (ghost_comp ctxt (Tm_Star (list_as_vprop (vprop_as_list ctxt))
                                            Tm_Emp))
