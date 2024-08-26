module Part2.ST
// Make st parametric in the state, i.e.,
//   st s a = s -> a & s
// And redefined all the functions below to use it
let st a = int -> a & int

let read
  : st int
  = fun s -> s, s

let write (s1:int)
  : st unit
  = fun _ -> (), s1

let bind #a #b
         (f: st a)
         (g: a -> st b)
  : st b
  = fun s0 ->
      let x, s1 = f s0 in
      g x s1

let return #a (x:a)
  : st a
  = fun s -> x, s


let feq #a #b (f g : a -> b) = forall x. f x == g x
let left_identity #a #b (x:a) (g: a -> st b)
  : Lemma ((v <-- return x; g v) `feq` g x)
  = ()
let right_identity #a (f:st a)
  : Lemma ((x <-- f; return x) `feq` f)
  = ()
let associativity #a #b #c (f1:st a) (f2:a -> st b) (f3:b -> st c)
  : Lemma ((x <-- f1; y <-- f2 x; f3 y) `feq`
           (y <-- (x <-- f1; f2 x); f3 y))
  = ()

let redundant_read_elim ()
  : Lemma ((read;; read) `feq` read)
  = ()

let redundant_write_elim (x y:int)
  : Lemma ((write x ;; write y) `feq` write y)
  = ()

let read_write_noop ()
  : Lemma ((x <-- read;  write x) `feq` return ())
  = ()
