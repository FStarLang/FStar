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
