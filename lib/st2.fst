(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:set.fsi heap.fst st.fst all.fst list.fst
  --*)

module FStar.Relational
open FStar.Heap

(* Relational Type constructor (Equivalent to pairs) *)
type rel (a:Type) (b:Type) : Type =
  | R : l:a -> r:b -> rel a b

(* Some frequently used abbreviations *)
type double (t:Type) = rel t  t
type eq (t:Type) = p:(double t){R.l p = R.r p}

let twice x = R x x
let tu = twice ()

(* functions to lift normal functions to Relational functions *)
val rel_map1T : ('a -> Tot 'b) -> (double 'a) -> Tot (double 'b)
let rel_map1T f (R x1 x2)  = R (f x1) (f x2)

val rel_map2T : ('a -> 'b -> Tot 'c) -> (double 'a) -> (double 'b) -> Tot (double 'c)
let rel_map2T f (R x1 x2) (R y1 y2) = R (f x1 y1) (f x2 y2)

val rel_map3T : ('a -> 'b -> 'c -> Tot 'd) -> (double 'a) -> (double 'b) -> (double 'c) -> Tot (double 'd)
let rel_map3T f (R x1 x2) (R y1 y2) (R z1 z2) = R (f x1 y1 z1) (f x2 y2 z2)

(* Some convenient arithmetic functions *)
let op_Hat_Plus = rel_map2T (fun x y -> x + y)
let op_Hat_Minus = rel_map2T (fun x y -> x - y)
let op_Hat_Star = rel_map2T (fun x y -> x * y)
let op_Hat_Slash = rel_map2T (fun x y -> x / y)

(* Some convenient list functions *)
val tl_rel: #a:Type -> l:double (list a){is_Cons (R.l l) /\ is_Cons (R.r l)}-> Tot (double (list a))
let tl_rel (R (_::xs) (_::ys)) = R xs ys
let cons_rel (R x y) (R xs ys) = R (x::xs) (y::ys)

(* Some convenient tuple functions *)
let pair_rel (R a b) (R c d) = R (a,c) (b,d)
let triple_rel (R a b) (R c d) (R e f) = R (a,c,e) (b,d,f)
let fst_rel = rel_map1T fst
let snd_rel = rel_map1T snd

(* Some convenient boolean functions *)
let and_rel = rel_map2T (fun x y -> x && y)
let or_rel = rel_map2T (fun x y -> x || y)
let eq_rel = rel_map2T (fun x y -> x = y)

(* Some convenient functions combining left and right side (for specification only) *)
let and_irel (R a b) = a && b
let or_irel (R a b) = a || b
let eq_irel (R a b) = a = b

(* Some convenient functions on heap (for specification) *)
let sel_rel1 h r  = rel_map2T sel h (twice r)
let sel_rel2 = rel_map2T sel
let upd_rel = rel_map3T upd

module FStar.Comp

open FStar.Heap
open FStar.Relational

type heap2 = double heap

new_effect STATE2 = STATE_h heap2
kind ST2Pre = STPre_h heap2
kind ST2Post (a:Type) = STPost_h heap2 a
kind ST2WP (a:Type) = STWP_h heap2 a
effect ST2 (a:Type) (pre:ST2Pre) (post: (heap2 -> ST2Post a)) =
    STATE2 a
      (fun (p:ST2Post a) (h:heap2) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
      (fun (p:ST2Post a) (h:heap2) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1))          (* WLP *)
effect St2 (a:Type) = ST2 a (fun h -> True) (fun h0 r h1 -> True)
sub_effect
  PURE   ~> STATE2 = (fun (a:Type) (wp:PureWP a) (p:ST2Post a) -> (fun h2 -> wp (fun a0 -> p a0 h2)))
sub_effect
  DIV    ~> STATE2 = (fun (a:Type) (wp:PureWP a) (p:ST2Post a) -> (fun h2 -> wp (fun a0 -> p a0 h2)))

(* construct a ST2WP from 2 STWPs *)
type comp (a:Type) (b:Type) (wp0:STWP a) (wp1:STWP b) (p:((rel a b) -> heap2 -> Type)) (h2:heap2) =
    wp0 (fun y0 h0 ->
      wp1 (fun y1 h1 -> p (R y0 y1) (R h0 h1))
      (R.r h2))
    (R.l h2)

assume val compose2: #a0:Type -> #b0:Type -> #wp0:(a0 -> STWP b0) -> #wlp0:(a0 -> STWP b0)
                  -> #a1:Type -> #b1:Type -> #wp1:(a1 -> STWP b1) -> #wlp1:(a1 -> STWP b1)
                  -> =c0:(x0:a0 -> STATE b0 (wp0 x0) (wlp0 x0))
                  -> =c1:(x1:a1 -> STATE b1 (wp1 x1) (wlp1 x1))
                  -> x: rel a0 a1
                  -> STATE2 (rel b0 b1)
                            (comp b0 b1 (wp0 (R.l x)) (wp1 (R.r x)))
                            (comp b0 b1 (wlp0 (R.l x)) (wlp1 (R.r x)))

val compose2_self : #a:Type -> #b:Type -> #wp:(a -> STWP b) -> #wlp:(a -> STWP b)
                -> =c:(x:a -> STATE b (wp x) (wlp x))
                -> x: double a
                -> STATE2 (double b)
                          (comp b b (wp (R.l x)) (wp (R.r x)))
                          (comp b b (wlp (R.l x)) (wlp (R.r x)))
let compose2_self f x = compose2 f f x


assume val cross : #a:Type -> #b:Type -> #c:Type -> #d:Type
                -> #p:(heap2 -> Type)
                -> #p':(heap2 -> Type)
                -> #q:(heap2 -> rel a b -> heap2 -> Type)
                -> #q':(heap2 -> rel c d -> heap2 -> Type)
                -> =c1:(double unit -> ST2 (rel a b) (requires (fun h -> p h)) (ensures (fun h1 r h2 -> q h1 r h2)))
                -> =c2:(double unit -> ST2 (rel c d) (requires (fun h -> p' h)) (ensures (fun h1 r h2 -> q' h1 r h2)))
                -> ST2 (rel a d) (requires (fun h -> (exists (hl:heap) (hr:heap).
                                                             p (R (R.l h) hr)
                                                          /\ p' (R hl (R.r h)))))
                                 (ensures (fun h1 r h2 -> (exists (h2l:heap) (h2r:heap) (rl:c) (rr:b).
                                                                  q h1 (R (R.l r) rr) (R (R.l h2) (h2r))
                                                               /\ q' h1 (R rl (R.r r)) (R h2l (R.r h2)))))


(* Some experimental functions *)

type decomp_l (a0:Type) (a1:Type) (b0:Type) (b1:Type) (al:a0)
            (wp:(rel a0 a1 -> ST2WP (rel b0 b1))) (p:b0 -> heap -> Type) (hl:heap) = 
    (exists (ar:a1) (hr:heap).
      wp (R al ar) (fun y2 h2 -> p (R.l y2) (R.l h2))
         (R hl hr))

type decomp_r (a0:Type) (a1:Type) (b0:Type) (b1:Type) (ar:a1)
            (wp:(rel a0 a1 -> ST2WP (rel b0 b1))) (p:b1 -> heap -> Type) (hr:heap) =
    (exists (al:a0) (hl:heap).
      wp (R al ar) (fun y2 h2 -> p (R.r y2) (R.r h2))
         (R hl hr))

assume val project_l : #a0:Type -> #b0:Type -> #a1:Type -> #b1:Type
                    -> #wp:(rel a0 a1 -> ST2WP (rel b0 b1))
                    -> #wlp:(rel a0 a1 -> ST2WP (rel b0 b1))
                    -> =c:(x:rel a0 a1 -> STATE2 (rel b0 b1) (wp x) (wlp x))
                    -> x:a0
                    -> STATE b0 (decomp_l a0 a1 b0 b1 x wp)
                                (decomp_l a0 a1 b0 b1 x wlp)

assume val project_r : #a0:Type -> #b0:Type -> #a1:Type -> #b1:Type
                    -> #wp:(rel a0 a1 -> ST2WP (rel b0 b1))
                    -> #wlp:(rel a0 a1 -> ST2WP (rel b0 b1))
                    -> =c:(x:rel a0 a1 -> STATE2 (rel b0 b1) (wp x) (wlp x))
                    -> x:a1
                    -> STATE b1 (decomp_r a0 a1 b0 b1 x wp)
                                (decomp_r a0 a1 b0 b1 x wlp)


module FStar.RelationalState
open FStar.Comp
open FStar.Relational
open FStar.Heap

(* Some convenient stateful functions *)
let read_rel1 r = compose2_self read (twice r)
let read_rel2 = compose2_self read
let assign_rel1 r v = compose2_self (fun (a,b) -> write a b) (pair_rel (twice r) v)
let assign_rel2 r v = compose2_self (fun (a,b) -> write a b) (pair_rel r v)
