module Part1.Quicksort.Generic

//Some auxiliary definitions to make this a standalone example
let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

let rec append #a (l1 l2:list a)
  : list a
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2

let total_order (#a:Type) (f: (a -> a -> bool)) =
    (forall a. f a a)                                         (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1=!=a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                       (* totality  *)

let total_order_t (a:Type) = f:(a -> a -> bool) { total_order f }

let rec sorted #a  (f:total_order_t a) (l:list a)
  : bool
  = match l with
    | [] -> true
    | [x] -> true
    | x :: y :: xs -> f x y && sorted f (y :: xs)

let rec mem (#a:eqtype) (i:a) (l:list a)
  : bool
  = match l with
    | [] -> false
    | hd :: tl -> hd = i || mem i tl

let rec sort #a (f:total_order_t a) (l:list a)
  : Tot (list a) (decreases (length l))
  = admit()

let rec sort_correct (#a:eqtype) (f:total_order_t a) (l:list a)
  : Lemma (ensures (
           let m = sort f l in
           sorted f m /\
           (forall i. mem i l = mem i m)))
          (decreases (length l))
  = admit()

let rec sort_intrinsic (#a:eqtype) (f:total_order_t a) (l:list a)
  : Tot (m:list a {
                sorted f m /\
                (forall i. mem i l = mem i m)
         })
   (decreases (length l))
  = admit()
