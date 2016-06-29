module ST.Def

assume type s : Type //an abstract type of the state

let st (a:Type) = s -> Tot (a * s)
let return  (#a:Type) (x:a) : st a = fun s -> (x, s)
let bind (#a:Type) (#b:Type) (f:st a) (g: a -> Tot (st b)) : st b = 
  fun s0 -> let x, s1 = f s0 in 
         g x s1

open FStar.FunctionalExtensionality

let right_unit (a:Type) (f:st a) : Lemma (bind f return = f)
  = assert (feq (bind f return) f)
  
let left_unit (a:Type) (b:Type) (x:a) (f:a -> Tot (st b)) : Lemma (bind (return x) f = f x)
  = assert (feq (bind (return x) f) (f x))

let assoc (a:Type) (b:Type) (c:Type) (f:st a) (g:(a -> Tot (st b))) (h:(b -> Tot (st c)))
  : Lemma  (bind f (fun x -> bind (g x) h) = bind (bind f g) h) 
  = assert (feq (bind f (fun x -> bind (g x) h)) (bind (bind f g) h))
