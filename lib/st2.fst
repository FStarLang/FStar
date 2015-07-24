(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst
  --*)
module Comp
open Heap
type heap2 = heap * heap

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

type comp (a:Type) (b:Type) (wp0:STWP a) (wp1:STWP b) (p:((a * b) -> heap2 -> Type)) (h2:heap2) =
    wp0 (fun y0 h0 ->
      wp1 (fun y1 h1 -> p (y0, y1) (h0, h1))
      (snd h2))
    (fst h2)

assume val compose2: #a0:Type -> #b0:Type -> #wp0:(a0 -> STWP b0) -> #wlp0:(a0 -> STWP b0)
                  -> #a1:Type -> #b1:Type -> #wp1:(a1 -> STWP b1) -> #wlp1:(a1 -> STWP b1)
                  -> =c0:(x0:a0 -> STATE b0 (wp0 x0) (wlp0 x0))
                  -> =c1:(x1:a1 -> STATE b1 (wp1 x1) (wlp1 x1))
                  -> x0:a0
                  -> x1:a1
                  -> STATE2 (b0 * b1)
                             (comp b0 b1 (wp0 x0) (wp1 x1))
                             (comp b0 b1 (wlp0 x0) (wlp1 x1))

module Samples
open Comp
open Heap
let f x = x := !x - !x
let g x = x := 0
val equiv1: x:ref int
         -> y:ref int
         -> ST2 (unit * unit)
                (requires (fun _ -> True)) //x, y may be high-references
                (ensures (fun _ _ h2' -> sel (fst h2') x == sel (snd h2') y)) //their contents are equal afterwards
let equiv1 x y = compose2 f g x y


let square x = x := !x * !x
val equiv2: x:ref int
         -> y:ref int
         -> Comp.ST2 (unit * unit)
                (requires (fun h2 -> sel (fst h2) x = - (sel (snd h2) y)))     //x, y negatives of each other
                (ensures (fun _ _ h2' -> sel (fst h2') x = sel (snd h2') y)) //their contents are equal afterwards
let equiv2 x y = compose2 square square x y


let f3 x = if !x = 0 then x := 0 else x:= 1
let g3 x = if !x <> 0 then x := 1 else x:= 0
val equiv3: x:ref int
         -> y:ref int
         -> Comp.ST2 (unit * unit)
                (requires (fun h -> sel (fst h) x = sel (snd h) y)) // x, y have same values
                (ensures (fun _ _ h2' -> sel (fst h2') x = sel (snd h2') y)) // their contents are equal afterwards
let equiv3 x y = compose2 f3 g3 x y


let f4 x = if !x = 0 then x := 0 else x:= 1
let g4 x = if !x = 0 then x := 1 else x:= 0
val equiv4: x:ref int
         -> y:ref int
         -> Comp.ST2 (unit * unit)
                (requires (fun h -> if sel (fst h) x = 0 then sel (snd h) y = 1 else sel (snd h) y = 0)) // making sure !x=0 <==> !y <> 0
                (ensures (fun _ _ h2' -> sel (fst h2') x = sel (snd h2') y)) //their contents are equal afterwards
let equiv4 x y = compose2 f4 g4 x y


let f5 x = x := 0
let g5 x = if !x = 0 then x := !x else x:= !x - !x
val equiv5: x:ref int
         -> y:ref int
         -> Comp.ST2 (unit * unit)
                (requires (fun _ -> True))  // no requirements
                (ensures (fun _ _ h2' -> sel (fst h2') x = sel (snd h2') y)) //their contents are equal afterwards
let equiv5 x y = compose2 f5 g5 x y


let f6 x = let y = 1 in x := y
let g6 x = if !x = 0 then x := 1 else if !x <> 0 then x := 1 else x:= 0
val equiv6: x:ref int
         -> y:ref int
         -> Comp.ST2 (unit * unit)
                (requires (fun _ -> True)) // no requirements
                (ensures (fun _ _ h2' -> sel (fst h2') x = sel (snd h2') y)) //their contents are equal afterwards
let equiv6 x y = compose2 f6 g6 x y


let f7 x = x := 2*!x
let g7 x = let y = (fun a -> a + a) !x in x := y
val equiv7: x:ref int
         -> y:ref int
         -> Comp.ST2 (unit * unit)
                (requires (fun h -> sel (fst h) x - sel (snd h) y = 10)) // values of x, y differ by 10
                (ensures (fun _ _ h2' -> sel (fst h2') x - sel (snd h2') y = 20)) // values of x, y differ by 20
let equiv7 x y = compose2 f7 g7 x y


let f8 (x, y, z) = if !z=0 then (x := 1; y := 1) else (y:=1 ; x := 0)
val equiv8: a:(ref int * ref int * ref int)
         -> b:(ref int * ref int * ref int)
         -> Comp.ST2 (unit * unit)
                (requires (fun h -> MkTuple3._1 a <> MkTuple3._2 a /\  // x and y are not aliases
                                    MkTuple3._1 b <> MkTuple3._2 b))
                (ensures (fun _ _ h2' -> sel (fst h2') (MkTuple3._2 a) = sel (snd h2') (MkTuple3._2 b))) //value of y is the same
let equiv8 a b = compose2 f8 f8 a b




(* Examples taken from the POPL paper *)

let assign x y = x := y

val monotonic_assign : x:ref int -> y1:int -> y2:int
                       -> Comp.ST2 (unit * unit)
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
(* val monotonic_id : x:int -> y:int -> Comp.ST2 (int * int) *)
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
   x:twice int -> Tot (y:(twice int){d (fst y) (snd y) <= k * (d (fst x) (snd x))})

val foo : k:int -> twice int -> Tot (twice int)
let foo k x = pair_map2 (fun k x -> k * x) (same k) x

val foo_monotonic : k:int{k>=0} -> Tot monotonic
let foo_monotonic k = (fun x -> pair_map2 (fun k x -> k * x) (same k) x)

val dist : int -> int -> Tot int
let dist x1 x2 = let m = x1 - x2 in
              if m >= 0 then m else -m

val foo_k_sensitive : k:int{k>0} -> Tot (k_sensitive dist k)
let foo_k_sensitive k = (fun x -> pair_map2 (fun k x -> k * x) (same k) x)


(* This does not work if I η-expand [noleak] in the body of noleak_ok *)
let noleak (x,b) = if b then x := 1 else x := 1
val noleak_ok: x1:ref int
               -> x2:ref int
               -> b1:bool
               -> b2:bool
               -> Comp.ST2 (unit * unit)
                             (requires (fun h -> True))
                             (ensures (fun h1 r h2 -> ((x1 = x2) /\ (fst h1 = snd h1)) ==> (fst h2 = snd h2)))
let noleak_ok x1 x2 b1 b2 = compose2 noleak noleak (x1,b1) (x2,b2)



(* Simple recursive function:
   The proof works by proving a pure specification for the imperative functions
   and by proving the equality of those specifiactions *)

(* Pure specifications *)
val gauss : nat -> Tot nat
let gauss x = (x * x + x) / 2

val gauss_rec : nat -> nat -> Tot nat
let rec gauss_rec x a = if x = 0 then a else gauss_rec (x - 1) (a + x)

(* Proof of the equality for the pure specifiaction *)
val gauss_lemma : x:nat -> a:nat -> Lemma
                        (requires True)
                        (ensures (gauss x + a = gauss_rec x a))
                        [SMTPat (gauss_rec x a)]
let rec gauss_lemma x a = if x = 0 then () else gauss_lemma (x-1) (a+x)

val equiv_gauss: x : nat
                 -> ST2 (nat * nat)
                    (requires (fun _ -> True))
                    (ensures (fun _ p _ -> fst p = snd p))
let equiv_gauss x = compose2 (fun x -> gauss_rec x 0) (fun x -> gauss x) x x

(* We prove, that the imperative functions fulfill the specifiaction *)
val gauss_imp : x:ref nat -> ST nat
                    (requires (fun h -> True))
                    (ensures  (fun h0 r h1 -> r = gauss (sel h0 x)))
let gauss_imp x = (!x*!x + !x)/2

val gauss_imp_rec : p:(ref nat * ref nat) -> ST nat
                    (requires (fun h -> fst p <> snd p))
                    (ensures  (fun h0 r h1 ->
                      r = gauss_rec ((sel h0) (fst p)) ((sel h0) (snd p)) /\
                      sel h1 (snd p) = r ))
let rec gauss_imp_rec (x, a) = if !x = 0 then !a
                           else (a := !a + !x; x := !x-1; gauss_imp_rec (x, a))

(* We can conclude the equality for the imperative functions *)
val equiv_gauss_imp: x:ref nat
                 -> a:ref nat
                 -> ST2 (nat * nat)
                    (requires (fun h2 -> a <> x /\
                                        sel (fst h2) x = sel (snd h2) x /\
                                        sel (fst h2) a = 0 ))
                    (ensures (fun _ p h2 -> fst p = snd p))
let equiv_gauss_imp x a = compose2 gauss_imp_rec gauss_imp (x,a) x

(* Example for Nik's proposal of sequencing (Email from 04/29/2015) *)

let c0_pfx a = a := 0
let c1_pfx b = b := 1
let equiv_pfx a b = compose2 c0_pfx c1_pfx a b


opaque type injection (f:int -> Tot int) = (forall x y. f x = f y ==> x = y)
opaque type surjection (f:int -> Tot int) = (forall y. (exists x. f x = y))
opaque type bijection (f:int -> Tot int) = injection f /\ surjection f
type bij = f:(int -> Tot int){bijection f}
opaque type inverses (f:int -> Tot int) (g:int -> Tot int) =
   (forall y. f (g y) = y) /\
   (forall x. g (f x) = x)
val lemma_inverses_bij:  f:(int -> Tot int) -> g:(int -> Tot int) ->
  Lemma (requires (inverses f g))
        (ensures (bijection f))
let lemma_inverses_bij f g = ()

let dec x = x - 1

let inc x = x + 1


(* sample two random values into c and d such that they are related by a
  bijection f *)
assume val sample : f:(int -> Tot int){bijection f}
                    -> ST2 (int * int)
                       (requires (fun _ -> True))
                       (*(ensures (fun h2' (v1,v2)  h2 -> h2' = h2 /\ v1 = v2))*)
                       (ensures (fun h2' p  h2 -> h2' = h2 /\ fst p = f (snd p)))


let c0_sfx (a, c) = a := !a + c
let c1_sfx (b, d) = b := !b + d
let equiv_sfx a b c d = compose2 c0_sfx c1_sfx (a, c) (b, d)


(* relate the programs
  c0_pfx ; sample ; c0_sfx  and
  c1_pfx ; sample ; c1_sfx  *)
val equiv_seq: a:ref int
               -> b:ref int
               -> ST2 (unit * unit)
                  (requires (fun _ -> True))
                  (ensures (fun _ _ h2 -> sel (fst h2) a = sel (snd h2) b))
let equiv_seq a b = let _ = equiv_pfx a b in
                    cut (inverses inc dec);
                    let c, d = sample inc in
                    equiv_sfx a b c d

