module Utils

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference

assume val sladmit (#[@@@framing_implicit] p:slprop)  (#[@@@framing_implicit]q:slprop) (_:unit) : SteelT unit p (fun _ -> q)
assume val sladmitf (#[@@@framing_implicit] p:slprop)  (#[@@@framing_implicit]q:slprop) (_:unit) : SteelF unit p (fun _ -> q) (fun _ -> True) (fun _ _ _ -> True)
assume val sladmit_dep (#a:_)
                       (#[@@@framing_implicit] p:slprop)
                       (#[@@@framing_implicit] q:(a -> slprop))
                       (_:unit)
       : SteelT a p q

assume val sladmit_depF (#a:_)
                       (#[@@@framing_implicit] p:slprop)
                       (#[@@@framing_implicit] q:(a -> slprop))
                       (_:unit)
       : SteelF a p q (fun _ -> True) (fun _ _ _ -> True)

let return (#a:_)
           (#[@@@framing_implicit] p:slprop)
           (#[@@@framing_implicit] q:(a -> slprop))
           (x:a)
    : Steel a p q
         (requires fun _ -> p == q x)
         (ensures fun _ y _ -> y == x)
    = change_slprop p (q x) (fun _ -> ());
      x

let return' (#a:_)
            (#[@@@framing_implicit] q:(a -> slprop))
            (x:a)
            ()
    : SteelT a (q x) q
    = change_slprop (q x) (q x) (fun _ -> ()); x
