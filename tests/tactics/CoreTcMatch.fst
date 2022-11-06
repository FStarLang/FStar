module CoreExhaustivenessCheck
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

//But it works if we trick F* like this??!
//let nat_dep0 sz = n:nat{n < sz}
//let nat_dep sz = x:(nat_dep0 sz){True}

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