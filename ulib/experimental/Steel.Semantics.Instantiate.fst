module Steel.Semantics.Instantiate

friend Steel.Memory

#set-options "--z3rlimit 20"

let lemma_symmetry () = ()
let lemma_transitive () = ()
let lemma_interp_extensionality () = ()
let lemma_interp_depends_only () = ()

let lemma_associative () = ()
let lemma_commutative () = ()

let lemma_is_unit () =
  let lem (y:hprop) : Lemma (star emp y `equals` y /\ star y emp `equals` y)
    = emp_unit y; star_commutative emp y
  in
  Classical.forall_intro lem

let lemma_equals_ext () = ()

let lemma_affine () = ()
let lemma_emp_valid () = ()

let lemma_disjoint_sym () = ()
let lemma_disjoint_join () = ()

let lemma_join_commutative () = ()
let lemma_join_associative () = ()

let lemma_weaken_depends_only_on () = ()
let lemma_refine_equiv () = ()
let lemma_refine_star () = ()

let lemma_m_implies_disjoint () = ()
let lemma_mem_valid_locks_invariant () = ()
let lemma_valid_upd_heap () = ()
