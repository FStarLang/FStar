module Pulse.Checker.Prover.Substs

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing.Env
open Pulse.Typing

module L = FStar.List.Tot
module T = FStar.Tactics

module Env = Pulse.Typing.Env

val ss_t : Type0

val as_map (ss:ss_t) : Map.t var term

let dom (ss:ss_t) = Map.domain (as_map ss)
let contains (ss:ss_t) (x:var) = Map.contains (as_map ss) x
let sel (ss:ss_t) (x:var { contains ss x }) = Map.sel (as_map ss) x

val empty : ss_t

val push (ss:ss_t) (x:var { ~ (contains ss x) }) (t:term) : ss_t

val push_ss (ss1:ss_t) (ss2:ss_t { Set.disjoint (dom ss1) (dom ss2) }) : ss_t

val check_disjoint (ss1 ss2:ss_t) : b:bool { b ==> Set.disjoint (dom ss1) (dom ss2) }

val push_as_map (ss1 ss2:ss_t)
  : Lemma (requires Set.disjoint (dom ss1) (dom ss2))
          (ensures as_map (push_ss ss1 ss2) == Map.concat (as_map ss1) (as_map ss2))
          [SMTPat (as_map (push_ss ss1 ss2))]

val ss_term (t:term) (ss:ss_t) : term
val ss_st_term (t:st_term) (ss:ss_t) : st_term
val ss_st_comp (s:st_comp) (ss:ss_t) : st_comp
val ss_comp (c:comp) (ss:ss_t) : comp
val ss_binder (b:binder) (ss:ss_t) : binder
val ss_env (g:env) (ss:ss_t)
  : g':env { fstar_env g' == fstar_env g /\
             Env.dom g' == Env.dom g }

val ss_st_comp_commutes (s:st_comp) (ss:ss_t)
  : Lemma (ensures
             ss_st_comp s ss ==
             { s with res = ss_term s.res ss;
                      pre = ss_term s.pre ss;
                      post = ss_term s.post ss; })  // no shifting required
          [SMTPat (ss_st_comp s ss)]

val ss_comp_commutes (c:comp) (ss:ss_t)
  : Lemma (ensures
             (let r = ss_comp c ss in
              (C_Tot? c ==> r == C_Tot (ss_term (comp_res c) ss)) /\
              (C_ST? c ==> r == C_ST (ss_st_comp (st_comp_of_comp c) ss)) /\
              (C_STAtomic? c ==> r == C_STAtomic (ss_term (comp_inames c) ss)
                                                 (ss_st_comp (st_comp_of_comp c) ss)) /\
              (C_STGhost? c ==> r == C_STGhost (ss_term (comp_inames c) ss)
                                               (ss_st_comp (st_comp_of_comp c) ss))))
          [SMTPat (ss_comp c ss)]

type nt_substs = l:list subst_elt { forall elt. L.memP elt l ==> NT? elt }

let nt_subst_term (t:term) (ss:nt_substs) : term =
  L.fold_left (fun t elt -> subst_term t [elt]) t ss

let nt_subst_binder (b:binder) (ss:nt_substs) : binder =
  L.fold_left (fun b elt -> subst_binder b [elt]) b ss

let nt_subst_st_term (t:st_term) (ss:nt_substs) : st_term =
  L.fold_left (fun t elt -> subst_st_term t [elt]) t ss

let nt_subst_st_comp (s:st_comp) (ss:nt_substs) : st_comp =
  L.fold_left (fun s elt -> subst_st_comp s [elt]) s ss

let nt_subst_comp (c:comp) (ss:nt_substs) : comp =
  L.fold_left (fun c elt -> subst_comp c [elt]) c ss

let nt_subst_env (g:env) (ss:nt_substs) : g':env { Env.dom g' == Env.dom g /\
                                                   Env.fstar_env g' == Env.fstar_env g } =
  let g' = L.fold_left (fun g elt -> subst_env g [elt]) g ss in
  assume (Env.dom g' == Env.dom g /\ Env.fstar_env g' == Env.fstar_env g);
  g'

val nt_substs_st_comp_commutes (s:st_comp) (nts:nt_substs)
  : Lemma (ensures
             nt_subst_st_comp s nts ==
             { s with res = nt_subst_term s.res nts;
                      pre = nt_subst_term s.pre nts;
                      post = nt_subst_term s.post nts; })  // no shifting required
          [SMTPat (nt_subst_st_comp s nts)]

val nt_subst_comp_commutes (c:comp) (nts:nt_substs)
  : Lemma (ensures
             (let r = nt_subst_comp c nts in
              (C_Tot? c ==> r == C_Tot (nt_subst_term (comp_res c) nts)) /\
              (C_ST? c ==> r == C_ST (nt_subst_st_comp (st_comp_of_comp c) nts)) /\
              (C_STAtomic? c ==> r == C_STAtomic (nt_subst_term (comp_inames c) nts)
                                                 (nt_subst_st_comp (st_comp_of_comp c) nts)) /\
              (C_STGhost? c ==> r == C_STGhost (nt_subst_term (comp_inames c) nts)
                                               (nt_subst_st_comp (st_comp_of_comp c) nts))))
          [SMTPat (nt_subst_comp c nts)]

let rec well_typed_nt_substs (g:env) (uvs:env) (nts:nt_substs)
  : Tot Type0 (decreases L.length nts) =
  
  match bindings uvs, nts with
  | [], [] -> True
  | _::_, (NT x e)::nts_rest ->
    let y, ty, rest_uvs = remove_binding uvs in
    x == y /\
    tot_typing g e ty /\
    well_typed_nt_substs g (subst_env rest_uvs [ NT x e ]) nts_rest
  | _, _ -> False

val is_permutation (nts:nt_substs) (ss:ss_t) : Type0

val ss_to_nt_substs (g:env) (uvs:env) (ss:ss_t)
  : T.Tac (option (nts:nt_substs { well_typed_nt_substs g uvs nts /\
                                   is_permutation nts ss }))

val well_typed_nt_substs_prefix (g:env) (uvs:env) (nts:nt_substs)
  (uvs1:env)
  : Pure nt_substs
         (requires well_typed_nt_substs g uvs nts /\ env_extends uvs uvs1)
         (ensures fun nts1 -> well_typed_nt_substs g uvs1 nts1)

val ss_nt_subst (g:env) (uvs:env) (ss:ss_t) (nts:nt_substs)
  : Lemma (requires disjoint uvs g /\ well_typed_nt_substs g uvs nts /\ is_permutation nts ss)
          (ensures
             (forall (t:term). nt_subst_term t nts == ss_term t ss) /\
             (forall (b:binder). nt_subst_binder b nts == ss_binder b ss) /\
             (forall (t:st_term). nt_subst_st_term t nts == ss_st_term t ss) /\
             (forall (c:comp). nt_subst_comp c nts == ss_comp c ss) /\
             (forall (s:st_comp). nt_subst_st_comp s nts == ss_st_comp s ss))
          [SMTPat (well_typed_nt_substs g uvs nts); SMTPat (is_permutation nts ss)]


val st_typing_nt_substs
  (g:env) (uvs:env) (g':env { pairwise_disjoint g uvs g' })
  (#t:st_term) (#c:comp_st) (t_typing:st_typing (push_env g (push_env uvs g')) t c)
  (ss:nt_substs { well_typed_nt_substs g uvs ss })
: st_typing (push_env g (nt_subst_env g' ss)) (nt_subst_st_term t ss) (nt_subst_comp c ss)

val st_typing_subst (g:env) (uvs:env { disjoint uvs g }) (t:st_term) (c:comp_st)
  (d:st_typing (push_env g uvs) t c)
  (ss:ss_t)

  : T.Tac (option (st_typing g (ss_st_term t ss) (ss_comp c ss)))

val st_typing_nt_substs_derived
  (g:env) (uvs:env { disjoint uvs g })
  (#t:st_term) (#c:comp_st) (t_typing:st_typing (push_env g uvs) t c)
  (ss:nt_substs { well_typed_nt_substs g uvs ss })
: st_typing g (nt_subst_st_term t ss) (nt_subst_comp c ss)

val vprop_equiv_nt_substs_derived
  (g:env) (uvs:env { disjoint g uvs })
  (#p1 #p2:vprop) (veq:vprop_equiv (push_env g uvs) p1 p2)
  (ss:nt_substs { well_typed_nt_substs g uvs ss })
: vprop_equiv g (nt_subst_term p1 ss) (nt_subst_term p2 ss)
