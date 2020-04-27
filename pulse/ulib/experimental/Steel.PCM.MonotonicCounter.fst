module Steel.PCM.MonotonicCounter
open Steel.PCM
open Steel.PCM.Preorder
open FStar.Preorder


let pre_pcm : pcm' nat = {
  composable=(fun x y -> True);
  op=(fun (x y:nat) -> Math.Lib.max x y);
  one=0
}
let mctr_pcm : pcm nat = {
  p=pre_pcm;
  comm=(fun _ _ -> ());
  assoc=(fun _ _ _ -> ());
  assoc_r=(fun _ _ _ -> ());
  is_unit=(fun _ -> ())
}


let increasing : preorder nat = fun (x y:nat) -> b2t (x <= y)

let mctr_induces_increases
  : squash (induces_preorder mctr_pcm increasing)
  = ()

let test (x z:nat) (f:(nat -> prop){stable f increasing})
  : Lemma
    (requires (compatible mctr_pcm x z /\ f x))
    (ensures f z)
  = assert (increasing x z)
