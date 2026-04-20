module Timeless

assume val slprop : Type u#4
assume val timeless : slprop -> prop

assume val pure : prop -> slprop
assume val timeless_pure p : Lemma (timeless (pure p)) [SMTPat (timeless (pure p))]

assume val ex #a (p: a -> slprop) : slprop
assume val timeless_ex #a p : Lemma
    (requires forall x. timeless (p x))
    (ensures timeless (ex #a p))
    [SMTPat (timeless (ex #a p))]

let foo () : timeless (ex fun x -> pure (x > 10)) = ()

assume val frob (x: nat) : Pure bool (requires x > 5) (ensures fun _ -> True)
let bar () : timeless (ex fun x -> pure (x > 10 /\ frob x)) = ()
let baz () : timeless (ex fun x -> pure (x > 10 ==> frob x)) = ()