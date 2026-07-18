module Bug2414

let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

let total_order (#a:Type) (f: (a -> a -> bool)) =
    (forall a. f a a)
    /\ (forall a1 a2. (f a1 a2 /\ a1=!=a2)  <==> not (f a2 a1))
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1)

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

val sort_correct (#a:eqtype) (f:total_order_t a) (l:list a)
  : Lemma (ensures (
           let m = sort f l in
           sorted f m /\
           (forall i. mem i l = mem i m)))
          (decreases (length l))
[@@expect_failure [184]]
let rec sort_correct = admit() // Bug: Seems to be OK if I remove 'rec' here

[@@expect_failure [184]]
let rec f =
  let g = f in 4
