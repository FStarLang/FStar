module Steel.Semantics.Instantiate

friend Steel.Memory

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

let lemma_symmetry () = ()
let lemma_transitive () = ()
let lemma_interp_extensionality () = ()
let lemma_interp_depends_only () = ()

let lemma_associative () = Classical.forall_intro_3 star_associative
let lemma_commutative () = Classical.forall_intro_2 star_commutative

let lemma_is_unit () =
  let lem (y:hprop) : Lemma (star emp y `equals` y /\ star y emp `equals` y)
    = emp_unit y; star_commutative emp y
  in
  Classical.forall_intro lem

#push-options "--max_ifuel 1 --max_fuel 1"

let lemma_equals_ext () = ()

#pop-options

let lemma_affine () = Classical.forall_intro_3 affine_star
let lemma_emp_valid () = Classical.forall_intro intro_emp

let lemma_disjoint_sym () = ()
let lemma_disjoint_join () = ()

let lemma_join_commutative () = ()
let lemma_join_associative () = ()

#push-options "--max_fuel 1 --max_ifuel 1"

let lemma_weaken_depends_only_on () = ()
let lemma_refine_equiv () = ()
let lemma_refine_star () = Classical.forall_intro_3 refine_star

let lemma_m_implies_disjoint () = ()
let lemma_mem_valid_locks_invariant () = ()
let lemma_valid_upd_heap () = ()

#pop-options
