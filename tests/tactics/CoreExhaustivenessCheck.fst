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

