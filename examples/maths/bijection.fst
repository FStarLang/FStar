module Bijection

open FStar.Constructive

type injective 'a 'b (f:('a -> Tot 'b)) =
       (forall (x1:'a) (x2:'a). f x1 = f x2 ==> x1 = x2)

type inverse 'a 'b (fab:('a -> Tot 'b)) (fba:('b -> Tot 'a)) =
       (forall (x:'a). fba (fab x) = x) /\ (forall (y:'b). fab (fba y) = y)

type bijective 'a 'b (f:('a -> Tot 'b)) =
       cexists (fun (f':'b -> Tot 'a) ->
         t:ctrue{inverse 'a 'b f f' /\ injective 'a 'b f /\ injective 'b 'a f'})

val even : int -> Tot bool
let even i = (i % 2 = 0)

val foo : nat -> Tot int
let foo n = if even n then n/2 else -((n+1)/2)

val foo_inv : int -> Tot nat
let foo_inv i = if i >= 0 then i*2 else ((-i)*2)-1

val bijective_foo : bijective nat int foo
let bijective_foo = ExIntro foo_inv I
// bijection.fst(25,0-25,37): Unknown assertion failed
// Error: 1 errors were reported (see above)
// CH: I think this used to work 4 months ago!
