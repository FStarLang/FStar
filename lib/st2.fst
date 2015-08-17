(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst
  --*)

module Relational
open Heap
type rel (a:Type) (b:Type) : Type =
  | R : l:a -> r:b -> rel a b

let twice x = R x  x
type double (t:Type) = rel t  t
type eq (t:Type) = p:(double t){R.l p = R.r p}


val rel_map1 : ('a -> Tot 'b) -> (double 'a) -> Tot (double 'b)
let rel_map1 f (R x1 x2)  = R (f x1) (f x2)

val rel_map2 : ('a -> 'b -> Tot 'c) -> (double 'a) -> (double 'b) -> Tot (double 'c)
let rel_map2 f (R x1 x2) (R y1 y2) = R (f x1 y1) (f x2 y2)

val rel_map3 : ('a -> 'b -> 'c -> Tot 'd) -> (double 'a) -> (double 'b) -> (double 'c) -> Tot (double 'd)
let rel_map3 f (R x1 x2) (R y1 y2) (R z1 z2) = R (f x1 y1 z1) (f x2 y2 z2)

let add_rel (R a b) (R c d) = R (a+c) (b+d)
let mul_rel (R a b) (R c d) = R (a*c) (b*d)
val tl_rel: #a:Type -> l:double (list a){is_Cons (R.l l) /\ is_Cons (R.r l)}-> Tot (double (list a))
let tl_rel (R (_::xs) (_::ys)) = R xs ys
let cons_rel (R x y) (R xs ys) = R (x::xs)  (y::ys)
let pair_rel (R x y) (R x' y') = R (x,x') (y,y')
let fst_rel (R (x, y) (x', y')) = R x x'
let snd_rel (R (x, y) (x', y')) = R y y'
let and_rel (R a b) = a && b
let or_rel (R a b) = a || b
let eq_rel (R a b) = a = b
let sel_rel (R h0 h1) (R r0 r1) = R (sel h0 r0) (sel h1 r1)



module Comp
open Heap
open Relational
type heap2 = double heap

new_effect STATE2 = STATE_h heap2
kind ST2Pre = STPre_h heap2
kind ST2Post (a:Type) = STPost_h heap2 a
effect ST2 (a:Type) (pre:ST2Pre) (post: (heap2 -> ST2Post a)) =
    STATE2 a
      (fun (p:STPost_h heap2 a) (h:heap2) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
      (fun (p:STPost_h heap2 a) (h:heap2) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1))           (* WLP *)
effect St2 (a:Type) = ST2 a (fun h -> True) (fun h0 r h1 -> True)
sub_effect
  PURE   ~> STATE2 = (fun (a:Type) (wp:PureWP a) (p:ST2Post a) -> (fun h2 -> wp (fun a0 -> p a0 h2)))

type comp (a:Type) (b:Type) (wp0:STWP a) (wp1:STWP b) (p:((rel a b) -> heap2 -> Type)) (h2:heap2) =
    wp0 (fun y0 h0 ->
      wp1 (fun y1 h1 -> p (R y0 y1) (R h0 h1))
      (R.r h2))
    (R.l h2)

assume val compose2: #a0:Type -> #b0:Type -> #wp0:(a0 -> STWP b0) -> #wlp0:(a0 -> STWP b0)
                  -> #a1:Type -> #b1:Type -> #wp1:(a1 -> STWP b1) -> #wlp1:(a1 -> STWP b1)
                  -> =c0:(x0:a0 -> STATE b0 (wp0 x0) (wlp0 x0))
                  -> =c1:(x1:a1 -> STATE b1 (wp1 x1) (wlp1 x1))
                  -> x0:a0
                  -> x1:a1
                  -> STATE2 (rel b0 b1)
                             (comp b0 b1 (wp0 x0) (wp1 x1))
                             (comp b0 b1 (wlp0 x0) (wlp1 x1))
