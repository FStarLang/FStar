(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst
  --*)
module Comp
open Heap
type heap2 = heap * heap

(* Working around https://github.com/FStarLang/FStar/issues/164 *)
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


let f3 x = if !x = 0 then x := 0 else x:= 1
let g3 x = if !x <> 0 then x := 1 else x:= 0
val equiv3: x:ref int
         -> y:ref int
         -> STATE2.ST2 (unit * unit)
                (requires (fun h -> sel (fst h) x = sel (snd h) y)) // x, y have same values
                (ensures (fun _ _ h2' -> sel (fst h2') x = sel (snd h2') y)) // their contents are equal afterwards
let equiv3 x y = compose2 f3 g3 x y


let f4 x = if !x = 0 then x := 0 else x:= 1
let g4 x = if !x = 0 then x := 1 else x:= 0
val equiv4: x:ref int
         -> y:ref int
         -> STATE2.ST2 (unit * unit)
                (requires (fun h -> if sel (fst h) x = 0 then sel (snd h) y = 1 else sel (snd h) y = 0)) // making sure !x=0 <==> !y <> 0
                (ensures (fun _ _ h2' -> sel (fst h2') x = sel (snd h2') y)) //their contents are equal afterwards
let equiv4 x y = compose2 f4 g4 x y


let f5 x = x := 0
let g5 x = if !x = 0 then x := !x else x:= !x - !x
val equiv5: x:ref int
         -> y:ref int
         -> STATE2.ST2 (unit * unit)
                (requires (fun _ -> True))  // no requirements
                (ensures (fun _ _ h2' -> sel (fst h2') x = sel (snd h2') y)) //their contents are equal afterwards
let equiv5 x y = compose2 f5 g5 x y


let f6 x = let y = 1 in x := y
let g6 x = if !x = 0 then x := 1 else if !x <> 0 then x := 1 else x:= 0
val equiv6: x:ref int
         -> y:ref int
         -> STATE2.ST2 (unit * unit)
                (requires (fun _ -> True)) // no requirements
                (ensures (fun _ _ h2' -> sel (fst h2') x = sel (snd h2') y)) //their contents are equal afterwards
let equiv6 x y = compose2 f6 g6 x y


let f7 x = x := 2*!x
let g7 x = let y = (fun a -> a + a) !x in x := y
val equiv7: x:ref int
         -> y:ref int
         -> STATE2.ST2 (unit * unit)
                (requires (fun h -> sel (fst h) x - sel (snd h) y = 10)) // values of x, y differ by 10
                (ensures (fun _ _ h2' -> sel (fst h2') x - sel (snd h2') y = 20)) // values of x, y differ by 20
let equiv7 x y = compose2 f7 g7 x y


let f8 (x, y, z) = if !z=0 then (x := 1; y := 1) else (y:=1 ; x := 0)
val equiv8: a:(ref int * ref int * ref int)
         -> b:(ref int * ref int * ref int)
         -> STATE2.ST2 (unit * unit)
                (requires (fun h -> MkTuple3._1 a <> MkTuple3._2 a /\  // x and y are not aliases
                                    MkTuple3._1 b <> MkTuple3._2 b))
                (ensures (fun _ _ h2' -> sel (fst h2') (MkTuple3._2 a) = sel (snd h2') (MkTuple3._2 b))) //value of y is the same
let equiv8 a b = compose2 f8 f8 a b




(* Examples taken from the POPL paper *)

let assign x y = x := y

val monotonic_assign : x:ref int -> y1:int -> y2:int
                       -> STATE2.ST2 (unit * unit)
                                     (requires (fun h -> y1 <= y2))
                                     (ensures (fun h1 r h2 -> sel (fst h2) x <= sel (snd h2) x))
let monotonic_assign x y1 y2 = compose2 (assign x) (assign x) y1 y2


val id : int -> Tot int
let id x = x

val monotonic_id_standard : x:int -> y:int
                            -> Lemma (requires (x <= y))
                                     (ensures (id x <= id y))
let monotonic_id_standard x y = ()


(* This does not work...? *)
(* val monotonic_id : x:int -> y:int -> STATE2.ST2 (int * int) *)
(*                                                 (requires (fun h -> x <= y)) *)
(*                                                 (ensures (fun h1 r h2 -> (fst r) <= (snd r))) *)
(* let monotonic_id x y = compose2 id id x y *)

type twice (a:Type) = a * a

type low 'a = x:(twice 'a){fst x = snd x}
type high 'a = twice 'a

val same : 'a -> Tot (twice 'a)
let same x = (x,x)

val one : twice int
let one = same 1

val pair_map2 : ('a -> 'b -> Tot 'c) -> (twice 'a) -> (twice 'b) -> Tot (twice 'c)
let pair_map2 f (x1,x2) (y1,y2) = (f x1 y1, f x2 y2)

let plus = pair_map2 (fun x y -> x + y)

val test_info : (high int * low int) -> Tot (high int * low int)
(* This one fails as expected *)
(* val test_info : (high int * low int) -> (low int * low int) *)
let test_info (x,y) = ((plus x y), (plus y one))

let minus  = pair_map2 (fun x y -> x - y)

val test_minus : high int -> Tot (low int)
let test_minus z = minus z z

type monotonic = x:twice int -> Tot (y:(twice int){fst x <= snd x ==> fst y <= snd y})

type k_sensitive (d:(int -> int -> Tot int)) (k:int) =
   x:twice int -> Tot (y:(twice int){d (fst x) (snd x) <= d (fst y) (snd y)})

val foo : k:int -> twice int -> Tot (twice int)
let foo k x = pair_map2 (fun k x -> k * x) (same k) x

val foo_monotonic : k:int{k>=0} -> Tot monotonic
let foo_monotonic k = (fun x -> pair_map2 (fun k x -> k * x) (same k) x)

val dist : int -> int -> Tot int
let dist x1 x2 = let m = x1 - x2 in
              if m >= 0 then m else -m

(* This doesn't work for obscure reasons *)
(* val foo_k_sensitive : k:int{k>0} -> Tot (k_sensitive dist k) *)
(* let foo_k_sensitive k = (fun x -> pair_map2 (fun k x -> k * x) (same k) x) *)
(* Unknown assertion failed *)

(* Unfolding k_sensitive makes it work again *)
val foo_k_sensitive : k:int{k>0} -> x:twice int ->
      Tot (y:(twice int){dist (fst x) (snd x) <= k * (dist (fst y) (snd y))})
let foo_k_sensitive k = (fun x -> pair_map2 (fun k x -> k * x) (same k) x)

(* This does not work if I η-expand [noleak] in the body of noleak_ok *)
let noleak (x,b) = if b then x := 1 else x := 1
val noleak_ok: x1:ref int
               -> x2:ref int
               -> b1:bool
               -> b2:bool
               -> STATE2.ST2 (unit * unit)
                             (requires (fun h -> True))
                             (ensures (fun h1 r h2 -> ((x1 = x2) /\ (fst h1 = snd h1)) ==> (fst h2 = snd h2)))
let noleak_ok x1 x2 b1 b2 = compose2 noleak noleak (x1,b1) (x2,b2)


(*  First try to work on Nik's proposal of sequencing... Not working yet *)

(* Duplication... was unable to access types defined in STATE2 monad *)
type bind_wp_s2  (a:Type) (b:Type) (wp1:STATE2.WP a) (wlp1:STATE2.WP a) 
                 (wp2:(a -> STATE2.WP b)) (wlp2:(a -> STATE2.WP b)) 
                 (p:STATE2.Post b) (h0:heap2) =
                     wp1 (fun a h1 -> wp2 a p h1) h0

type bind_wlp_s2 (a:Type) (b:Type) (wlp1:STATE2.WP a) (wlp2:(a -> STATE2.WP b))
                 (p:STATE2.Post b) (h0:heap2) =
                     wlp1 (fun a -> wlp2 a p) h0


assume val sequence: c0r:Type -> c1r:Type 
                     -> wp0:STATE2.WP c0r -> wp1:STATE2.WP c1r
                     -> wlp0:STATE2.WP c0r -> wlp1:STATE2.WP c1r
                     -> =c0:(unit -> STATE2 c0r wp0 wlp0)
                     -> =c1:(unit -> STATE2 c1r wp1 wlp1)
                     -> STATE2 c1r 
                       (bind_wp_s2 c0r c1r wp0 wlp0 (fun a-> wp1) (fun a -> wlp1))
                       (bind_wlp_s2 c0r c1r wlp0 (fun a -> wlp1))

let c0_pfx a = a := 0
let c1_pfx b = b := !b - !b
val equiv_pfx: a:ref int
               -> b:ref int
               -> STATE2.ST2 (unit * unit)
                  (requires (fun _ -> True)) 
                  (ensures (fun _ _ h2 -> sel (fst h2) a = sel (snd h2) b)) 
let equiv_pfx a b = compose2 c0_pfx c1_pfx a b

let c0_sfx c = c := !c - !c
let c1_sfx d = d := 0
val equiv_sfx: c:ref int
                -> d:ref int
                -> STATE2.ST2 (unit * unit)
                  (requires (fun _ -> True)) 
                  (ensures (fun _ _ h2 -> sel (fst h2) c = sel (snd h2) d))
let equiv_sfx c d = compose2 c0_sfx c1_sfx c d

(* This does not work yet: Unknown assertion failed... *)
(*
val equiv_seq: a:ref int
               -> b:ref int
               -> c:ref int
               -> d:ref int
               -> STATE2.ST2 (unit * unit)
                  (requires (fun _ -> True))
                  (ensures (fun _ _ h2 -> sel (fst h2) a = sel (snd h2) b /\
                                          sel (fst h2) c = sel (snd h2) d)) 
let equiv_seq a b c d = sequence (fun () -> equiv_pfx a b) (fun () -> equiv_sfx c d)
*)
