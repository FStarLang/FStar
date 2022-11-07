module CoreCheckMatch
//Thanks to Theophile Wallez for this example
open FStar.Tactics

type simple_record = {
  f1: int;
  f2: int;
}

unfold
let f (x:simple_record): (f1:int & int) =
  let {f1=ff1; f2=ff2} = x in
  (|ff1, ff2|)

unfold
let g (x:(f1:int & int)): simple_record =
  let (|gf1, gf2|) = x in
  {f1=gf1; f2=gf2}

val dtuple2_ind: #a:Type -> #b:(a -> Type) -> p:((x:a & b x) -> Type0) -> squash (forall (x:a) (y:b x). p (|x, y|)) -> Lemma (forall xy. p xy)
let dtuple2_ind #a #b p _ = ()
  
let _: squash (forall (x:(f1:int & int)). f (g x) == x) =
  _ by (
    apply_lemma (`dtuple2_ind);
    let _ = forall_intro () in
    let _ = forall_intro () in
    trefl())

let option_ind (#a:Type) (p:option a -> Type) (_:squash (p None)) (_: squash (forall x. p (Some x))) : Lemma (forall (x:option a). p x) = ()

let _ =
  assert (forall (x:option bool). match x with | None -> True | Some x -> True)
    by (apply_lemma (`option_ind);
        trivial();
        trivial())

assume val nat_dep: nat -> eqtype

type simple_record_nd = {
  f1: nat_dep 1;
  f2: nat_dep 1;
}

unfold
type nested_pair = (f1:nat_dep 1 & nat_dep 1)

unfold
let f_nd (x:simple_record_nd): nested_pair =
  let {f1; f2} = x in
  (|f1, f2|)

unfold
let g_nd (x:nested_pair): simple_record_nd =
  let (|f1, f2|) = x in
  {f1; f2}

let _: squash (forall (x:nested_pair). f_nd (g_nd x) == x) =
  synth_by_tactic(fun () -> (
    apply_lemma (`dtuple2_ind);
    let _ = forall_intro () in
    let _ = forall_intro () in
    trefl()
  ))

//
// This is another example from Theophile Wallez
//
// Here core gets a match term, with a dot pattern,
//   whose typechecking results in a guard
//

type simple_record_dp = {
  f1: nat_dep 1;
  f2: nat_dep 2;
  f3: nat_dep 3;
}

unfold
type nested_pair_dp = (f1:nat_dep 1 & (f2:nat_dep 2 & nat_dep 3))

unfold
let f_dp (x:simple_record_dp): nested_pair_dp =
  let {f1; f2; f3} = x in
  (|f1, (|f2, f3|)|)

unfold
let g_dp (x:nested_pair_dp): simple_record_dp =
  let (|f1, (|f2, f3|)|) = x in
  {f1; f2; f3}

let _: squash (forall (x:nested_pair_dp). f_dp (g_dp x) == x) =
  synth_by_tactic(fun () -> (
    apply_lemma (`dtuple2_ind);
    let _ = forall_intro () in
    apply_lemma (`dtuple2_ind);
    let _ = forall_intro () in
    let _ = forall_intro () in
    trefl()
  ))


//
// Yet another example from Theophile Wallez,
//   illustrating why it is not a good idea to aggressively unrefine the type of
//   scrutinee when typechecking a pattern
//
// The idea is supose there is a constructor C : nat -> t
//   and we write match x with | C n -> ...
//
// Then if we add n:int (i.e. lose the refinement) to the environment for
//   typechecking the branch, we may unnecessarily generate guards
//

let nat_dep_tsc_ref sz = n:nat{n < sz}

type simple_record_tsc_ref = {
  f1: nat_dep_tsc_ref 1;
  f2: nat_dep_tsc_ref 2;
  f3: nat_dep_tsc_ref 3;
  f4: nat_dep_tsc_ref 4;
}

unfold
type nested_pair_tsc_ref = (f1:nat_dep_tsc_ref 1 & (f2:nat_dep_tsc_ref 2 & (f3:nat_dep_tsc_ref 3 & nat_dep_tsc_ref 4)))

unfold
let f_tsc_ref (x:simple_record_tsc_ref): nested_pair_tsc_ref =
  let {f1; f2; f3; f4} = x in
  (|f1, (|f2, (|f3, f4|)|)|)

unfold
let g_tsc_ref (x:nested_pair_tsc_ref): simple_record_tsc_ref =
  let (|f1, (|f2, (|f3, f4|)|)|) = x in
  {f1; f2; f3; f4}

#push-options "--no_smt"
let _: squash (forall (x:nested_pair_tsc_ref). f_tsc_ref (g_tsc_ref x) == x) =
  synth_by_tactic(fun () -> (
    apply_lemma (`dtuple2_ind);
    let _ = forall_intro () in
    apply_lemma (`dtuple2_ind);
    let _ = forall_intro () in
    apply_lemma (`dtuple2_ind);
    let _ = forall_intro () in
    let _ = forall_intro () in
    trefl()
  ))
#pop-options


//
// This example from Theophile Wallez brings out the different between openings and closings in
//   core vs in the tc
//
// In particular, core equality of names does not depend on the string names, whereas
//   syntax substitutions do
//

type refined (a:Type) (pred:a -> bool) = x:a{pred x}

val dtuple2_ind_ss: #a:Type -> #b:(a -> Type) -> p:((x:a & b x) -> Type0) -> squash (forall (x:a) (y:b x). p (|x, y|)) -> Lemma (forall xy. p xy)
let dtuple2_ind_ss #a #b p _ = ()

val refined_ind: a:Type -> pred:(a -> bool) -> p:(refined a pred -> Type0) -> squash (forall (x:a). pred x ==> p x) -> squash (forall (x:refined a pred). p x)
let refined_ind a pred p _ = ()

val eq_to_eq: a:eqtype -> x:a -> y:a -> p:Type0 -> squash (x == y ==> p) -> squash (x = y ==> p)
let eq_to_eq a x y p _ = ()

val add_squash: p:Type0 -> q:Type0 -> squash (squash p ==> q) -> squash (p ==> q)
let add_squash p q _ =
  introduce p ==> q with _. ()

val or_split: b1:bool -> b2:bool -> p:Type0 -> squash (b1 ==> p) -> squash (b2 ==> p) -> squash (b1 || b2 ==> p)
let or_split b1 b2 p _ _ = ()

unfold
type toto = refined nat (fun x0 -> x0 = (1 <: nat) || x0 = (0 <: nat))

unfold
let tata (x1:toto): Type0 =
  match x1 with
  | 0 -> unit
  | 1 -> unit

type test_sum  =
  | Ctor_1: unit -> test_sum
  | Ctor_2: unit -> test_sum

unfold
let f_ss (x:dtuple2 toto tata): test_sum =
  match x with
  | (|0, _0|) -> Ctor_1 _0
  | (|1, _0|) -> Ctor_2 _0

unfold
let g_ss (x:test_sum): dtuple2 toto tata =
  match x with
  | Ctor_1 _0 -> (|0, _0|)
  | Ctor_2 _0 -> (|1, _0|)

val arrow_to_forall: #a:Type -> p:(a -> Type0) -> squash (forall (x:a). p x) -> (x:a -> squash (p x))
let arrow_to_forall #a p _ x =
  ()

val remove_refine: a:Type0 -> p:(a -> Type0) -> q:(a -> Type0) -> squash (forall (x:a). q x) -> squash (forall (x:a{p x}). q x)
let remove_refine a p q _ = ()

//
// The smt query still fail, as they should, but no internal assertion failure
//

#push-options "--admit_smt_queries true"
let _: x:dtuple2 toto tata -> squash (g_ss (f_ss x) == x) =
  synth_by_tactic (fun () ->
    apply (`arrow_to_forall);
    apply_lemma (`dtuple2_ind);
    apply (`refined_ind);
    let _ = forall_intro () in
    norm [primops; iota];
    let solve_one_goal () =
      apply (`eq_to_eq);
      apply (`add_squash);
      let x_eq_term = binder_to_term (implies_intro ()) in
      l_to_r [x_eq_term];
      let _ = forall_intro () in
      trefl()
    in
    apply (`or_split);
    focus solve_one_goal;
    focus solve_one_goal;
    dump "SMT goals"
  )
#pop-options
