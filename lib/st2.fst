module Comp
open Heap
type heap2 = heap * heap
kind STWP (a:Type) = (a -> heap -> Type) -> heap -> Type
kind PUREWP (a:Type) = (a -> Type) -> Type
kind ALLPost (a:Type) = result a -> heap -> Type

monad_lattice {
  STATE2:: (* STATE a wp wlp *)
          kind Pre     = heap2 -> Type
          kind Post (a:Type) = a -> heap2 -> Type
          kind WP (a:Type) = Post a -> Pre
          type return   (a:Type) (x:a) (p:Post a) = p x
          type bind_wp  (a:Type) (b:Type) (wp1:WP a) (wlp1:WP a) (wp2:(a -> WP b)) (wlp2:(a -> WP b)) (p:Post b) (h0:heap2) =
              wp1 (fun a h1 -> wp2 a p h1) h0
          type bind_wlp (a:Type) (b:Type) (wlp1:WP a) (wlp2:(a -> WP b)) (p:Post b) (h0:heap2) = wlp1 (fun a -> wlp2 a p) h0
          type if_then_else (a:Type) (p:Type) (wp_then:WP a) (wp_else:WP a) (post:Post a) (h0:heap2) =
              (if p
               then wp_then post h0
               else wp_else post h0)
          type ite_wlp  (a:Type) (wlp_cases:WP a) (post:Post a) (h0:heap2) =
              (forall (a:a) (h:heap2). wlp_cases (fun a1 h1 -> a=!=a1 \/ h=!=h1) h0 \/ post a h)
          type ite_wp (a:Type) (wlp_cases:WP a) (wp_cases:WP a) (post:Post a) (h0:heap2) =
              (forall (a:a) (h:heap2). wlp_cases (fun a1 h1 -> a=!=a1 \/ h=!=h1) h0 \/ post a h)
              /\ wp_cases (fun a h_ -> True) h0
          type wp_binop (a:Type) (wp1:WP a) ('op:Type -> Type -> Type) (wp2:WP a) (p:Post a) (h:heap2) =
              'op (wp1 p h) (wp2 p h)
          type wp_as_type (a:Type) (wp:WP a) = (forall (p:Post a) (h:heap2). wp p h)
          type close_wp (a:Type) (b:Type) (wp:(b -> WP a)) (p:Post a) (h:heap2) = (forall (b:b). wp b p h)
          type close_wp_t (a:Type) (wp:(Type -> WP a)) (p:Post a) (h:heap2) = (forall (b:Type). wp b p h)
          type assert_p (a:Type) ('P:Type) (wp:WP a) (p:Post a) (h:heap2) = ('P /\ wp p h)
          type assume_p (a:Type) ('P:Type) (wp:WP a) (p:Post a) (h:heap2) = ('P ==> wp p h)
          type null_wp (a:Type) (p:Post a) (h:heap2) = (forall (x:a) (h':heap2). p x h')
          type trivial (a:Type) (wp:WP a) = (forall h0. wp (fun r h1 -> True) h0)
          with ST2 (a:Type) (pre:Pre) (post: (heap2 -> Post a)) =
              STATE2 a
                (fun (p:Post a) (h:heap2) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
                (fun (p:Post a) (h:heap2) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1))           (* WLP *)
          and St2 (a:Type) = ST2 a (fun h -> True) (fun h0 r h1 -> True)
  with
  PURE   ~> STATE2 = (fun ('a:Type) ('wp:PUREWP 'a) ('p:STATE2.Post 'a) -> (fun h2 -> 'wp (fun a0 -> 'p a0 h2)));
  STATE2 ~> ALL    = (fun ('a:Type) ('wp:STATE2.WP 'a) ('p:ALLPost 'a) -> (fun h -> False))
}

type comp (a:Type) (b:Type) (wp0:STWP a) (wp1:STWP b) (p:((a * b) -> heap2 -> Type)) (h2:heap2) =
    wp0 (fun y0 h0 ->
      wp1 (fun y1 h1 -> p (y0, y1) (h0, h1))
      (snd h2))
    (fst h2)

assume val compose2: a0:Type -> b0:Type -> wp0:(a0 -> STWP b0) -> wlp0:(a0 -> STWP b0)
                  -> a1:Type -> b1:Type -> wp1:(a1 -> STWP b1) -> wlp1:(a1 -> STWP b1)
                  -> =c0:(x0:a0 -> STATE b0 (wp0 x0) (wlp0 x0))
                  -> =c1:(x1:a1 -> STATE b1 (wp1 x1) (wlp1 x1))
                  -> x0:a0
                  -> x1:a1
                  -> STATE2 (b0 * b1)
                             (comp b0 b1 (wp0 x0) (wp1 x1))
                             (comp b0 b1 (wlp0 x0) (wlp1 x1))

let f x = x := !x - !x
let g x = x := 0
val equiv1: x:ref int
         -> y:ref int
         -> STATE2.ST2 (unit * unit)
                (requires (fun _ -> True)) //x, y may be high-references
                (ensures (fun _ _ h2' -> sel (fst h2') x == sel (snd h2') y)) //their contents are equal afterwards
let equiv1 x y = compose2 f g x y


let square x = x := !x * !x
val equiv2: x:ref int
         -> y:ref int
         -> STATE2.ST2 (unit * unit)
                (requires (fun h2 -> sel (fst h2) x = - (sel (snd h2) y)))     //x, y negatives of each other
                (ensures (fun _ _ h2' -> sel (fst h2') x = sel (snd h2') y)) //their contents are equal afterwards
let equiv2 x y = compose2 square square x y
