module Rel

(* General Definitions *)
type rel (t:Type)  =
| R : l:t -> r:t -> rel t

type eq (t:Type) = v:(rel t){R?.l v == R?.r v}

let same x = R x x

val lift : #t:Type -> #t2:Type
           -> f:(t -> Tot t2) -> rel t
           -> Tot (rel t2)
let lift #t #t2 f (R x y) = R (f x) (f y)

val lift2 : #t:Type -> #t2:Type -> #t3:Type
           -> f:(t -> t2 -> Tot t3) -> rel t -> rel t2
           -> Tot (rel t3)
let lift2 #t #t2 #t3 f (R x y) (R x2 y2) = R (f x x2) (f y y2)

val lift3 : #t:Type -> #t2:Type -> #t3:Type -> #t4:Type
           -> f:(t -> t2 -> t3 -> Tot t4) -> rel t -> rel t2 -> rel t3
           -> Tot (rel t4)
let lift3 #t #t2 #t3 #t4 f (R x y) (R x2 y2) (R x3 y3) = R (f x x2 x3) (f y y2 y3)

val lift4 : #t:Type -> #t2:Type -> #t3:Type -> #t4:Type -> #t5:Type
           -> f:(t -> t2 -> t3 -> t4 -> Tot t5)
           -> rel t -> rel t2 -> rel t3 -> rel t4
           -> Tot (rel t5)
let lift4 #t #t2 #t3 #t4 #t5 f (R x y) (R x2 y2) (R x3 y3) (R x4 y4) =
    R (f x x2 x3 x4) (f y y2 y3 y4)

val lift5 : #t:Type -> #t2:Type -> #t3:Type -> #t4:Type -> #t5:Type -> #t6:Type
           -> f:(t -> t2 -> t3 -> t4 -> t5 -> Tot t6)
           -> rel t -> rel t2 -> rel t3 -> rel t4 -> rel t5
           -> Tot (rel t6)
let lift5 #t #t2 #t3 #t4 #t5 #t6 f (R x y) (R x2 y2) (R x3 y3) (R x4 y4) (R x5 y5) =
    R (f x x2 x3 x4 x5) (f y y2 y3 y4 y5)

val r_eq : #t:Type -> rel t -> Tot Type0
let r_eq #t (R x y) = (x == y)

let diag (#a:Type) (p:a -> Tot Type0) (r:rel a) : Type0 = p (R?.l r) /\ p (R?.r r)
let diagb (#a:Type) (p:a -> Tot bool) (r:rel a) : Type0 = p (R?.l r) /\ p (R?.r r)

let split (#a #b:Type) (r:rel (a*b)) : Tot (rel a * rel b) = (lift fst r, lift snd r)
