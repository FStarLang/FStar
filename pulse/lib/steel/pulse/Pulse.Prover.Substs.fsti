module Pulse.Prover.Substs

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing.Env

module L = FStar.List.Tot

module RT = FStar.Reflection.Typing
module T = FStar.Tactics

module Env = Pulse.Typing.Env

val t (g:env) : Type0

val as_subst (#g:env) (s:t g) : subst

val as_map (#g:env) (s:t g) : Map.t var term

let relates_to (g:env) (s:subst) (m:Map.t var term) =
  (forall (elt:subst_elt).{:pattern L.memP elt s}
          L.memP elt s ==> (NT? elt /\
                            (let NT x t = elt in
                             Map.contains m x /\
                             Map.sel m x == t))) /\
  
  (forall (x:var).{:pattern Map.contains m x}
                  Map.contains m x ==> (L.memP (NT x (Map.sel m x)) s)) /\

  (forall (x:var).{:pattern Map.contains m x}
                  Map.contains m x ==> ((~ (Set.mem x (dom g))) /\
                                        freevars (Map.sel m x) `Set.subset` dom g))

val subst_as_map (#g:env) (s:t g)
  : Lemma (relates_to g (as_subst s) (as_map s))
          [SMTPat (as_subst s); SMTPat (as_map s)]

let dom (#g:_) (s:t g) : Set.set var = Map.domain (as_map s)

let lookup (#g:_) (s:t g) (x:var { x `Set.mem` dom s }) : term =
  Map.sel (as_map s) x

let equal (#g:env) (s1 s2:t g) =
  Set.equal (dom s1) (dom s2) /\
  (forall (x:var).{:pattern Set.mem x (dom s1)} Set.mem x (dom s1) ==> lookup s1 x == lookup s2 x)

val equal_elim (#g:_) (s1 s2:t g)
  : Lemma (requires equal s1 s2)
          (ensures s1 == s2)
          [SMTPat (equal s1 s2)]

val empty (g:env) : t g

val empty_dom (g:_)
  : Lemma (dom (empty g) == Set.empty)
          [SMTPat (dom (empty g))]

val singleton (g:env)
  (x:var { ~ (Set.mem x (Env.dom g)) })
  (e:term { freevars e `Set.subset` Env.dom g })
  : t g

val singleton_dom (#g:_)
  (x:var { ~ (Set.mem x (Env.dom g)) })
  (e:term { freevars e `Set.subset` Env.dom g })
  : Lemma (ensures dom (singleton g x e) == Set.singleton x)
          [SMTPat (dom (singleton g x e))]

val push (#g:_) (s1:t g) (s2:t g { Set.disjoint (dom s1) (dom s2)})
  : t g

val push_substs_as_map (#g:_) (s1 s2:t g)
  : Lemma (requires Set.disjoint (dom s1) (dom s2))
          (ensures as_map (push s1 s2) == Map.concat (as_map s1) (as_map s2))
          [SMTPat (as_map (push s1 s2))]

let subst_extends (#g:_) (s1 s2:t g) =
  exists s3. s1 == push s2 s3

let subst_term (#g:_) (s:t g) (t:term) =
  subst_term t (as_subst s)

let subst_st_term (#g:_) (s:t g) (t:st_term) =
  subst_st_term t (as_subst s)

let subst_comp (#g:_) (s:t g) (c:comp) =
  subst_comp c (as_subst s)

val push_subst_term (#g:_) (s1 s2:t g) (t:term)
  : Lemma (requires Set.disjoint (dom s1) (dom s2))
          (ensures subst_term (push s1 s2) t ==
                   subst_term s2 (subst_term s1 t))
          [SMTPat (subst_term s2 (subst_term s1 t))]

val push_subst_st_term (#g:_) (s1 s2:t g) (t:st_term)
  : Lemma (requires Set.disjoint (dom s1) (dom s2))
          (ensures subst_st_term (push s1 s2) t ==
                   subst_st_term s2 (subst_st_term s1 t))
          [SMTPat (subst_st_term s2 (subst_st_term s1 t))]

val push_subst_comp (#g:_) (s1 s2:t g) (c:comp)
  : Lemma (requires Set.disjoint (dom s1) (dom s2))
          (ensures subst_comp (push s1 s2) c ==
                   subst_comp s2 (subst_comp s1 c))
          [SMTPat (subst_comp s2 (subst_comp s1 c))]

val subst_closed_term (#g:_) (s:t g) (t:term)
  : Lemma (requires freevars t `Set.subset` Env.dom g)
          (ensures subst_term s t == t)

val subst_closed_st_term (#g:_) (s:t g) (t:st_term)
  : Lemma (requires freevars_st t `Set.subset` Env.dom g)
          (ensures subst_st_term s t == t)

val subst_closed_comp (#g:_) (s:t g) (c:comp)
  : Lemma (requires freevars_comp c `Set.subset` Env.dom g)
          (ensures subst_comp s c == c)

val diff (#g:_) (s1:t g) (s2:t g { Set.subset (dom s2) (dom s1) })
  : s3:t g { Set.disjoint (dom s3) (dom s2) }

val diff_push (#g:_) (s1 s2:t g)
  : Lemma (requires Set.subset (dom s2) (dom s1))
          (ensures push (diff s1 s2) s2 == s1)
          [SMTPat (diff s1 s2)]
