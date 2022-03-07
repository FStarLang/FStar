module Bug2475

open FStar.Tactics

// Some dumb function and dumb lemmas
let f_inv_unsquash (#a:Type0) (f:(a -> a)) = ((forall (x:a). f (f x) == x))
let f_inv (#a:Type0) (f:(a -> a)) = squash (f_inv_unsquash f)

val f: (int & int) -> (int & int)
let f (a, b) = (b, a)

// Theorem to work with `apply_lemma` to split a forall on a pair
val tuple2_ind: #a:Type0 -> #b:Type0 -> p:((a & b) -> Type0) -> squash (forall (x:a) (y:b). p (x, y)) -> Lemma (forall xy. p xy)
let tuple2_ind #a #b p _ = ()

// First test, get a goal using `assert` (things work fine)
let test_direct () =
  assert(f_inv_unsquash f) by (
    compute ();
    apply_lemma (`tuple2_ind)
  )

let test_unshelve () =
  assert(True) by (
    // Construct the proof state
    let proof = uvar_env (top_env ()) (Some (mk_app (`f_inv) [(`(int & int)), Q_Implicit;  (`f), Q_Explicit])) in
    unshelve proof;
    // Work on the goal
    compute ();
    apply_lemma (`tuple2_ind)
  )

let test_unshelve_workaround () =
  assert(True) by (
    let proof = uvar_env (top_env ()) (Some (mk_app (`f_inv) [(`(tuple2 u#0 u#0 int int)), Q_Implicit;  (`f), Q_Explicit])) in
    unshelve proof;
    compute ();
    apply_lemma (`tuple2_ind)
  )
