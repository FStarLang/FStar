module Steel.Semantics.Instantiate

module S = Steel.Semantics.Hoare.MST
open Steel.Memory

type state0 : S.st0 =
  { S.heap = heap;
    S.mem = mem;
    S.locks_preorder = mem_evolves;
    S.hprop = hprop;
    S.heap_of_mem = heap_of_mem;
    S.locks_invariant = locks_invariant;

    S.m_disjoint = m_disjoint;
    S.disjoint = disjoint;
    S.join = join;
    S.upd_joined_heap = upd_joined_heap;

    S.interp = interp;

    S.emp = emp;
    S.star = star;

    S.equals = equiv
  }

val state_obeys_st_laws (_:unit) : Lemma (S.st_laws state0)

let state : S.st = state_obeys_st_laws (); state0
