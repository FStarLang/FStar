module Utils

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference

assume val sladmit (#p:slprop)  (#q:slprop) (_:unit) : SteelT unit p (fun _ -> q)
assume val sladmitf (#p:slprop)  (#q:slprop) (_:unit) : SteelF unit p (fun _ -> q) (fun _ -> True) (fun _ _ _ -> True)
assume val sladmit_dep (#a:_)
                       (#p:slprop)
                       (#q:(a -> slprop))
                       (_:unit)
       : SteelT a p q

assume val sladmit_depF (#a:_)
                       (#p:slprop)
                       (#q:(a -> slprop))
                       (_:unit)
       : SteelF a p q (fun _ -> True) (fun _ _ _ -> True)

let return (#a:_)
           (#p:slprop)
           (#q:(a -> slprop))
           (x:a)
    : Steel a p q
         (requires fun _ -> p == q x)
         (ensures fun _ y _ -> y == x)
    = change_slprop p (q x) (fun _ -> ());
      noop ();
      x

let return' (#a:_)
            (#q:(a -> slprop))
            (x:a)
            ()
    : SteelT a (q x) q
    = noop (); x
