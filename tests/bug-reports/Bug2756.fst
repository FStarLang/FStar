module Bug2756

open FStar.Tactics

val arrow_to_forall: #a:Type -> p:(a -> Type0) -> squash (forall (x:a). p x) -> (x:a -> squash (p x))
let arrow_to_forall #a p _ x = ()

val last: #a:Type0 -> list a -> Tac a
let last l =
  guard (Cons? l);
  List.Tot.last l

type refined (a:Type) (pred:a -> bool) = x:a{pred x}
let nat_dep (n:nat) = m:nat{m < pow2 n}

noeq type test_dependent_sum =
  | TestDependentSum1: n1: nat_dep 8 -> n2: nat_dep (n1 + 0) -> tdn1: nat_dep n1 -> test_dependent_sum
  | TestDependentSum2: unit -> test_dependent_sum

unfold
let pre (x:int) = x = 1 || x = 0

unfold
let encoded_snd (x:refined int pre): Type0 =
  match x with
  | 0 -> (n1:nat_dep 8 & (n2:nat_dep (n1 + 0) & nat_dep n1))
  | 1 -> unit

unfold
let encoded_type = dtuple2 (refined (nat_dep 1) pre) encoded_snd

assume val bar:
  f:(encoded_type -> test_dependent_sum) -> g:(test_dependent_sum -> encoded_type) ->
  (x:test_dependent_sum -> squash (f (g x) == x)) ->
  unit

let the_proof (): Tac unit =
  apply (`arrow_to_forall);
  compute();
  let x_term = binder_to_term (forall_intro ()) in
  destruct x_term;
  iterAll (fun () ->
    let destruct_binders = intros() in
    let breq_term = binder_to_term (last destruct_binders) in
    l_to_r [breq_term];
    compute();
    trefl ()
  )

let _: unit =
    (bar
        (id #(encoded_type -> test_dependent_sum)
            (fun x -> match x with
              | (| 0, (| n1, (| n2, tdn1|)|)|) ->
                TestDependentSum1 n1 n2 tdn1
              | (| 1, _0|) -> TestDependentSum2 _0))
        (id #(test_dependent_sum -> encoded_type)
            (fun x -> match x with
              | TestDependentSum1 n1 n2 tdn1 ->
                (| 0, (| n1, (| n2, tdn1 |) |) |)
              | TestDependentSum2 _0 -> (| 1, _0 |)))
        (synth_by_tactic the_proof))

