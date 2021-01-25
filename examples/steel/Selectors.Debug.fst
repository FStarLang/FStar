module Selectors.Debug

open Steel.SelEffect

open Selectors.LList

val test (#a:Type0) (p:t a)
  : SteelSel (t a * t a) (llist p) (fun res -> llist (snd res))
                (requires fun _ -> True)
                (ensures fun _ _ _ -> True)

let test #a p =
  noop ();
  (p, p)
