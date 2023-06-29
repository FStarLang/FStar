module Pulse.Prover.Substs

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing.Env
open Pulse.Typing
open Pulse.Typing.Metatheory

module L = FStar.List.Tot
module T = FStar.Tactics

module Env = Pulse.Typing.Env

type nt_substs = l:list subst_elt { forall elt. L.memP elt l ==> NT? elt }

let compose_nt_substs (ss1 ss2:nt_substs) : nt_substs =
  assume (forall elt. L.memP elt (ss1@ss2) <==> (L.memP elt ss1 \/ L.memP elt ss2));
  ss1 @ ss2

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

val nt_subst_st_comp_commutes (s:st_comp) (ss:nt_substs)
  : Lemma (nt_subst_st_comp s ss ==
           { s with res = nt_subst_term s.res ss;
                    pre = nt_subst_term s.pre ss;
                    post = nt_subst_term s.post ss; })  // note no shifting needed
          [SMTPat (nt_subst_st_comp s ss)]

val nt_subst_comp_commutes (c:comp) (ss:nt_substs)
  : Lemma (let r = nt_subst_comp c ss in
           (C_Tot? c ==> r == C_Tot (nt_subst_term (comp_res c) ss)) /\
           (C_ST? c ==> r == C_ST (nt_subst_st_comp (st_comp_of_comp c) ss)) /\
           (C_STAtomic? c ==> r == C_STAtomic (nt_subst_term (comp_inames c) ss)
                                              (nt_subst_st_comp (st_comp_of_comp c) ss)) /\
           (C_STGhost? c ==> r == C_STGhost (nt_subst_term (comp_inames c) ss)
                                            (nt_subst_st_comp (st_comp_of_comp c) ss)))
          [SMTPat (nt_subst_comp c ss)]

let nt_subst_env (g:env) (ss:nt_substs) : g':env { fstar_env g' == fstar_env g /\
                                                   dom g' == dom g } =
  admit ();
  L.fold_left (fun g elt -> subst_env g [elt]) g ss

val nt_subst_term_compose (t:term) (ss1 ss2:nt_substs)
: Lemma (ensures nt_subst_term (nt_subst_term t ss1) ss2 ==
                 nt_subst_term t (compose_nt_substs ss1 ss2))

val nt_subst_st_term_compose (t:st_term) (ss1 ss2:nt_substs)
: Lemma (ensures nt_subst_st_term (nt_subst_st_term t ss1) ss2 ==
                 nt_subst_st_term t (compose_nt_substs ss1 ss2))

val nt_subst_comp_compose (c:comp) (ss1 ss2:nt_substs)
: Lemma (ensures nt_subst_comp (nt_subst_comp c ss1) ss2 ==
                 nt_subst_comp c (compose_nt_substs ss1 ss2))

let rec well_typed_ss (g:env) (uvs:env) (ss:nt_substs) : Tot Type0 (decreases L.length ss) =
  match bindings uvs, ss with
  | [], [] -> True
  | _::_, (NT x e)::ss_rest ->
    let y, ty, rest_uvs = remove_binding uvs in
    x == y /\
    tot_typing g e ty /\
    well_typed_ss g (subst_env rest_uvs [ NT x e ]) ss_rest
  | _, _ -> False

val st_typing_nt_substs
  (g:env) (uvs:env) (g':env { pairwise_disjoint g uvs g' })
  (#t:st_term) (#c:comp_st) (t_typing:st_typing (push_env g (push_env uvs g')) t c)
  (ss:nt_substs { well_typed_ss g uvs ss })
: st_typing (push_env g (nt_subst_env g' ss)) (nt_subst_st_term t ss) (nt_subst_comp c ss)

val vprop_equiv_nt_substs
  (g:env) (uvs:env) (g':env { pairwise_disjoint g uvs g' })
  (#p1 #p2:vprop) (veq:vprop_equiv (push_env g (push_env uvs g')) p1 p2)
  (ss:nt_substs { well_typed_ss g uvs ss })
: vprop_equiv (push_env g (nt_subst_env g' ss)) (nt_subst_term p1 ss) (nt_subst_term p2 ss)


val t : Type0

val as_nt_substs (s:t) : nt_substs

val as_map (s:t) : Map.t var term

let sel (s:t) (x:var) = Map.sel (as_map s) x
let contains (s:t) (x:var) = Map.contains (as_map s) x
let dom (s:t) : Set.set var = Map.domain (as_map s)

let subst_term (e:term) (s:t) = nt_subst_term e (as_nt_substs s)
let subst_st_term (e:st_term) (s:t) = nt_subst_st_term e (as_nt_substs s)
let subst_comp (c:comp) (s:t) = nt_subst_comp c (as_nt_substs s)
let subst_st_comp (c:st_comp) (s:t) = nt_subst_st_comp c (as_nt_substs s)

// let relates_to (g:env) (s:subst) (m:Map.t var term) =
//   (forall (elt:subst_elt).{:pattern L.memP elt s}
//           L.memP elt s ==> (NT? elt /\
//                             (let NT x t = elt in
//                              Map.contains m x /\
//                              Map.sel m x == t))) /\
  
//   (forall (x:var).{:pattern Map.contains m x}
//                   Map.contains m x ==> (L.memP (NT x (Map.sel m x)) s)) /\

//   (forall (x:var).{:pattern Map.contains m x}
//                   Map.contains m x ==> ((~ (Set.mem x (dom g))) /\
//                                         freevars (Map.sel m x) `Set.subset` dom g))

// val subst_as_map (#g:env) (s:t g)
//   : Lemma (relates_to g (as_subst s) (as_map s))
//           [SMTPat (as_subst s); SMTPat (as_map s)]

// let lookup (#g:_) (s:t g) (x:var { x `Set.mem` dom s }) : term =
//   Map.sel (as_map s) x

// let equal (#g:env) (s1 s2:t g) =
//   Set.equal (dom s1) (dom s2) /\
//   (forall (x:var).{:pattern Set.mem x (dom s1)} Set.mem x (dom s1) ==> lookup s1 x == lookup s2 x)

// val equal_elim (#g:_) (s1 s2:t g)
//   : Lemma (requires equal s1 s2)
//           (ensures s1 == s2)
//           [SMTPat (equal s1 s2)]

val empty : t

val empty_dom (_:unit)
  : Lemma (dom empty == Set.empty)

// val singleton (g:env)
//   (x:var { ~ (Set.mem x (Env.dom g)) })
//   (e:term { freevars e `Set.subset` Env.dom g })
//   : t g

// val singleton_dom (#g:_)
//   (x:var { ~ (Set.mem x (Env.dom g)) })
//   (e:term { freevars e `Set.subset` Env.dom g })
//   : Lemma (ensures dom (singleton g x e) == Set.singleton x)
//           [SMTPat (dom (singleton g x e))]

val push (s1:t) (s2:t { Set.disjoint (dom s1) (dom s2)})
  : t

val push_as_map (s1 s2:t)
  : Lemma (requires Set.disjoint (dom s1) (dom s2))
          (ensures as_map (push s1 s2) == Map.concat (as_map s1) (as_map s2))
          [SMTPat (as_map (push s1 s2))]

val check_well_typedness (g:env) (uvs:env) (ss:t)
  : T.Tac (b:bool { b ==> well_typed_ss g uvs (as_nt_substs ss) })

// val push_substs_as_map (#g:_) (s1 s2:t g)
//   : Lemma (requires Set.disjoint (dom s1) (dom s2))
//           (ensures as_map (push s1 s2) == Map.concat (as_map s1) (as_map s2))
//           [SMTPat (as_map (push s1 s2))]

// let subst_extends (#g:_) (s1 s2:t g) =
//   exists s3. s1 == push s2 s3

// let subst_term (#g:_) (s:t g) (t:term) =
//   subst_term t (as_subst s)

// let subst_st_term (#g:_) (s:t g) (t:st_term) =
//   subst_st_term t (as_subst s)

// let subst_comp (#g:_) (s:t g) (c:comp) =
//   subst_comp c (as_subst s)

// val push_subst_term (#g:_) (s1 s2:t g) (t:term)
//   : Lemma (requires Set.disjoint (dom s1) (dom s2))
//           (ensures subst_term (push s1 s2) t ==
//                    subst_term s2 (subst_term s1 t))
//           [SMTPat (subst_term s2 (subst_term s1 t))]

// val push_subst_st_term (#g:_) (s1 s2:t g) (t:st_term)
//   : Lemma (requires Set.disjoint (dom s1) (dom s2))
//           (ensures subst_st_term (push s1 s2) t ==
//                    subst_st_term s2 (subst_st_term s1 t))
//           [SMTPat (subst_st_term s2 (subst_st_term s1 t))]

// val push_subst_comp (#g:_) (s1 s2:t g) (c:comp)
//   : Lemma (requires Set.disjoint (dom s1) (dom s2))
//           (ensures subst_comp (push s1 s2) c ==
//                    subst_comp s2 (subst_comp s1 c))
//           [SMTPat (subst_comp s2 (subst_comp s1 c))]

// val subst_closed_term (#g:_) (s:t g) (t:term)
//   : Lemma (requires freevars t `Set.subset` Env.dom g)
//           (ensures subst_term s t == t)

// val subst_closed_st_term (#g:_) (s:t g) (t:st_term)
//   : Lemma (requires freevars_st t `Set.subset` Env.dom g)
//           (ensures subst_st_term s t == t)

// val subst_closed_comp (#g:_) (s:t g) (c:comp)
//   : Lemma (requires freevars_comp c `Set.subset` Env.dom g)
//           (ensures subst_comp s c == c)

// val diff (#g:_) (s1:t g) (s2:t g { Set.subset (dom s2) (dom s1) })
//   : s3:t g { Set.disjoint (dom s3) (dom s2) }

// val diff_push (#g:_) (s1 s2:t g)
//   : Lemma (requires Set.subset (dom s2) (dom s1))
//           (ensures push (diff s1 s2) s2 == s1)
//           [SMTPat (diff s1 s2)]
