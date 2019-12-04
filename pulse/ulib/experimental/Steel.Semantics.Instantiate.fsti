module Steel.Semantics.Instantiate

module S = Steel.Semantics
open Steel.Memory

#set-options "--z3rlimit 20"

let equals (p1 p2:hprop) : prop = equiv p1 p2 /\ True

let state0 : S.st0 =
  { S.heap = heap;
    S.mem = mem;
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
    S.refine = refine;

    S.equals = equals
  }

val lemma_symmetry (u:unit) : Lemma (S.symmetry state0.S.equals)

val lemma_transitive (u:unit) : Lemma (S.transitive state0.S.equals)

val lemma_interp_extensionality (u:unit)
  : Lemma (S.interp_extensionality state0.S.equals state0.S.interp)

val lemma_interp_depends_only (u:unit) : Lemma (S.interp_depends_only state0)

val lemma_associative (u:unit) : Lemma (S.associative state0.S.equals state0.S.star)

val lemma_commutative (u:unit) : Lemma (S.commutative state0.S.equals state0.S.star)

val lemma_is_unit (u:unit) : Lemma (S.is_unit state0.S.emp state0.S.equals state0.S.star)

val lemma_equals_ext (u:unit) : Lemma (S.equals_ext state0.S.equals state0.S.star)

val lemma_affine (u:unit) : Lemma (S.affine state0)

val lemma_emp_valid (u:unit) : Lemma (S.emp_valid state0)

val lemma_disjoint_sym (u:unit) : Lemma (S.disjoint_sym state0)

val lemma_disjoint_join (u:unit) : Lemma (S.disjoint_join state0)

val lemma_join_commutative (u:unit) : Lemma (lemma_disjoint_sym (); S.join_commutative state0)

val lemma_join_associative (u:unit) : Lemma (lemma_disjoint_join(); S.join_associative state0)

val lemma_weaken_depends_only_on (u:unit) : Lemma (S.weaken_depends_only_on state0)

val lemma_refine_equiv (u:unit) : Lemma (S.refine_equiv state0)

val lemma_refine_star (u:unit) : Lemma (lemma_weaken_depends_only_on(); S.refine_star state0)

val lemma_m_implies_disjoint (u:unit) : Lemma (S.m_implies_disjoint state0)

val lemma_mem_valid_locks_invariant (u:unit) : Lemma (S.mem_valid_locks_invariant state0)

val lemma_valid_upd_heap (u:unit) : Lemma (lemma_m_implies_disjoint(); S.valid_upd_heap state0)

let st_laws_lemma () : Lemma (S.st_laws state0) =
  lemma_symmetry();
  lemma_transitive();
  lemma_interp_extensionality();
  lemma_interp_depends_only ();
  lemma_associative();
  lemma_commutative();
  lemma_is_unit();
  lemma_equals_ext();
  lemma_affine();
  lemma_emp_valid();
  lemma_disjoint_sym();
  lemma_disjoint_join();
  lemma_join_commutative();
  lemma_join_associative();
  lemma_weaken_depends_only_on();
  lemma_refine_equiv();
  lemma_refine_star();
  lemma_m_implies_disjoint();
  lemma_mem_valid_locks_invariant();
  lemma_valid_upd_heap()

let state : S.st = st_laws_lemma (); state0
