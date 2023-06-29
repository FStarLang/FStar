module Pulse.Prover.Util

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv

module L = FStar.List.Tot
module T = FStar.Tactics
module RT = FStar.Reflection.Typing
module Psubst = Pulse.Prover.Substs

type nt_substs = l:list subst_elt { forall elt. L.memP elt l ==> NT? elt }

let compose_nt_substs (ss1 ss2:nt_substs) : nt_substs =
  assume (forall elt. L.memP elt (ss1@ss2) <==> (L.memP elt ss1 \/ L.memP elt ss2));
  ss1 @ ss2

let nt_subst_term (t:term) (ss:nt_substs) : term =
  L.fold_left (fun t elt -> subst_term t [elt]) t ss

let nt_subst_st_term (t:st_term) (ss:nt_substs) : st_term =
  L.fold_left (fun t elt -> subst_st_term t [elt]) t ss

let nt_subst_comp (c:comp) (ss:nt_substs) : comp =
  L.fold_left (fun c elt -> subst_comp c [elt]) c ss

let nt_subst_env (g:env) (ss:nt_substs) : g':env { fstar_env g' == fstar_env g /\
                                                   dom g' == dom g } =
  admit ();
  L.fold_left (fun g elt -> subst_env g [elt]) g ss

let rec nt_subst_term_compose (t:term) (ss1 ss2:nt_substs)
: Lemma (ensures nt_subst_term (nt_subst_term t ss1) ss2 ==
                 nt_subst_term t (compose_nt_substs ss1 ss2))
        (decreases L.length ss1) =

match ss1 with
| [] -> ()
| (NT x e)::tl -> nt_subst_term_compose (subst_term t [ NT x e ]) tl ss2

let rec nt_subst_st_term_compose (t:st_term) (ss1 ss2:nt_substs)
: Lemma (ensures nt_subst_st_term (nt_subst_st_term t ss1) ss2 ==
                 nt_subst_st_term t (compose_nt_substs ss1 ss2))
        (decreases L.length ss1) =

match ss1 with
| [] -> ()
| (NT x e)::tl -> nt_subst_st_term_compose (subst_st_term t [ NT x e ]) tl ss2

let rec nt_subst_comp_compose (c:comp) (ss1 ss2:nt_substs)
: Lemma (ensures nt_subst_comp (nt_subst_comp c ss1) ss2 ==
                 nt_subst_comp c (compose_nt_substs ss1 ss2))
        (decreases L.length ss1) =

match ss1 with
| [] -> ()
| (NT x e)::tl -> nt_subst_comp_compose (subst_comp c [ NT x e ]) tl ss2

let rec well_typed_ss (g:env) (uvs:env) (ss:nt_substs) : Tot Type0 (decreases L.length ss) =
  match bindings uvs, ss with
  | [], [] -> True
  | _::_, (NT x e)::ss_rest ->
    let y, ty, rest_uvs = remove_binding uvs in
    x == y /\
    tot_typing g e ty /\
    well_typed_ss g (subst_env rest_uvs [ NT x e ]) ss_rest
  | _, _ -> False


let coerce_eq (#a #b:Type) (x:a) (_:squash (a === b)) : y:b{y == x} = x

let rec st_typing_nt_substs
  (g:env) (uvs:env) (g':env { pairwise_disjoint g uvs g' })
  (#t:st_term) (#c:comp_st) (t_typing:st_typing (push_env g (push_env uvs g')) t c)
  (ss:nt_substs { well_typed_ss g uvs ss })
: Tot (st_typing (push_env g (nt_subst_env g' ss)) (nt_subst_st_term t ss) (nt_subst_comp c ss))
      (decreases L.length ss) =

match bindings uvs with
| [] ->
  assert (equal (push_env uvs g') g');
  t_typing

| _ ->
  let x, ty, uvs' = remove_binding uvs in
  let (NT y e)::ss' = ss in
  let e_typing = FStar.IndefiniteDescription.elim_squash #(tot_typing g e ty) () in
  push_env_assoc (singleton_env (fstar_env uvs) x ty) uvs' g';
  let t_typing
    : st_typing (push_env g (push_env (singleton_env (fstar_env g) x ty) (push_env uvs' g'))) t c
    = coerce_eq t_typing () in
  let t_typing
    : st_typing (push_env g (subst_env (push_env uvs' g') [ NT y e ]))
                (subst_st_term t [ NT y e ])
                (subst_comp c [ NT y e ])
    = st_typing_subst g x ty (push_env uvs' g') e_typing t_typing in

  assume (subst_env (push_env uvs' g') [ NT y e ] ==
          push_env (subst_env uvs' [ NT y e ]) (subst_env g' [ NT y e ]));

  st_typing_nt_substs g
    (subst_env uvs' [ NT y e ])
    (subst_env g' [ NT y e ])
    t_typing ss'




// let subst_env_mk_env (f:RT.fstar_top_env) (ss:subst)
//   : Lemma (subst_env (mk_env f) ss == mk_env f)
//           [SMTPat (subst_env (mk_env f) ss)] = admit ()

// let well_typed_ss (#g:env) (g':env) (ss:Psubst.t g) =

//   forall (x:var).{:pattern Set.mem x (Psubst.dom ss) }
//   Set.mem x (Psubst.dom ss) ==> (x `Set.mem` dom g' /\
//                                 (let Some t = lookup g' x in
//                                  tot_typing g (Psubst.lookup ss x)
//                                               (Psubst.subst_term ss t)))


// let psubst_env (#g0:_) (g:env) (ss:Psubst.t g0) =
//   subst_env g (Psubst.as_subst ss)

// // different from extends, g1 may have dropped bindings from anywhere, not just the end
// let subenv (g1 g2:env) =
//   fstar_env g1 == fstar_env g2 /\
//   (forall (x:var).{:pattern Set.mem x (dom g1)}
//                   Set.mem x (dom g1) ==>
//                   (Set.mem x (dom g2) /\
//                    lookup g1 x == lookup g2 x))

// let rec filter_ss (#g0:env) (g:env) (ss:Psubst.t g0)
//   : Tot (g':env { subenv g' g /\ Set.disjoint (dom g') (Psubst.dom ss) })
//         (decreases bindings g) =

//   match bindings g with
//   | [] -> mk_env (fstar_env g)
//   | _ ->
//     let ( x, t, g ) = remove_latest_binding g in
//     let g = filter_ss g ss in
//     if Set.mem x (Psubst.dom ss) then g
//     else push_binding g x ppname_default t

// val push_subst_env (#g:_) (s1 s2:Psubst.t g) (g':env)
//   : Lemma (requires Set.disjoint (Psubst.dom s1) (Psubst.dom s2))
//           (ensures psubst_env g' (Psubst.push s1 s2) ==
//                    psubst_env (psubst_env g' s1) s2)
//           [SMTPat (psubst_env (psubst_env g' s1) s2)]

// val apply_partial_subs (#g0:env) (#t:st_term) (#c:comp_st)
//   (uvs:env { disjoint uvs g0 })
//   (ss:Psubst.t g0 { well_typed_ss uvs ss })
//   (t_typing:st_typing (push_env g0 uvs) t c)

//   : uvs_unresolved:env { uvs_unresolved == filter_ss uvs ss } &
//     st_typing (push_env g0 (psubst_env uvs_unresolved ss))
//               (Psubst.subst_st_term ss t)
//               (Psubst.subst_comp ss c)

// val apply_partial_subs_veq (#g0:env) (#p1 #p2:vprop)
//   (uvs:env { disjoint uvs g0 })
//   (ss:Psubst.t g0 { well_typed_ss uvs ss })
//   (veq:vprop_equiv (push_env g0 uvs) p1 p2)

//   : uvs_unresolved:env { uvs_unresolved == filter_ss uvs ss } &
//     vprop_equiv (push_env g0 (psubst_env uvs_unresolved ss))
//                 (Psubst.subst_term ss p1)
//                 (Psubst.subst_term ss p2)

// let ghost_comp pre post : c:comp_st { comp_pre c == pre /\ comp_post c == post } = 
//   C_STGhost tm_emp_inames { u=u_zero; res=tm_unit; pre; post }


// val idem_steps (g:env) (ctxt:vprop)
//   : t:st_term &
//     st_typing g t (ghost_comp ctxt (tm_star (list_as_vprop (vprop_as_list ctxt))
//                                             tm_emp))
