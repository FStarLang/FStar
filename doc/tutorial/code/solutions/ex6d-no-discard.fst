module QuicksortNoDiscard

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

val partition: ('a -> Tot bool) -> list 'a -> Tot (list 'a * list 'a)
let rec partition f = function 
  | [] -> [], []
  | hd::tl -> 
    let l1, l2 = partition f tl in
    if f hd 
    then hd::l1, l2
    else l1, hd::l2

(* Specification of sortedness according to some comparison function f *)
val sorted: ('a -> 'a -> Tot bool) -> list 'a -> Tot bool
let rec sorted f = function
  | []
  | [_] -> true
  | x::y::tl -> f x y && sorted f (y::tl)

val count : 'a -> list 'a -> Tot nat
let rec count (x:'a) (l:list 'a) = match l with
  | hd::tl -> if hd=x then 1 + count x tl else count x tl
  | [] -> 0

val count_append: l:list 'a -> m:list 'a -> x:'a 
               -> Lemma (requires True)
                        (ensures (count x (append l m) = (count x l + count x m)))
                        [SMTPat (count x (append l m))]
let rec count_append l m x = match l with 
  | [] -> ()
  | hd::tl -> count_append tl m x

let mem x l = count x l > 0

val append_mem:  l1:list 'a
              -> l2:list 'a
              -> a:'a
              -> Lemma (requires True)
                       (ensures (mem a (append l1 l2) = (mem a l1 || mem a l2)))
                       [SMTPat (mem a (append l1 l2))]
let rec append_mem l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> append_mem tl l2 a

(* A lemma about List.partition ... duh *)
val partition_lemma: f:('a -> Tot bool)
                  -> l:list 'a
                  -> Lemma (requires True)
                           (ensures ((fun l1 l2 -> 
                                     (length l1 + length l2 = length l
                                      /\ (forall x. mem x l1 ==> f x)
                                      /\ (forall x. mem x l2 ==> not (f x))
                                      /\ (forall x. count x l = (count x l1 + count x l2))))
                                        (fst (partition f l))
                                        (snd (partition f l))))
                           (* [SMTPat (partition f l)] (\* injected to the solver *\) *)
let rec partition_lemma f l = match l with 
  | [] -> ()
  | hd::tl -> partition_lemma f tl


opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)

val sorted_concat_lemma:  a:Type
               ->  f:(a -> a -> Tot bool)
               ->  l1:list a{sorted f l1}
               ->  l2:list a{sorted f l2}
               ->  pivot:a
               ->  Lemma (requires (total_order a f
                                    /\ (forall y. mem y l1 ==> not(f pivot y))
                                    /\ (forall y. mem y l2 ==> f pivot y))
)                         (ensures (sorted f (append l1 (pivot::l2))))
                          [SMTPat (sorted f (append l1 (pivot::l2)))]
let rec sorted_concat_lemma f l1 l2 pivot = match l1 with 
  | [] -> ()
  | hd::tl -> sorted_concat_lemma f tl l2 pivot


val sort: f:('a -> 'a -> Tot bool){total_order 'a f}
      ->  l:list 'a
      ->  Tot (m:list 'a{sorted f m /\ (forall x. count x l = count x m)})
              (decreases (length l))
let rec sort f = function
  | [] -> []
  | pivot::tl -> 
    let hi, lo  = partition (f pivot) tl in 
    partition_lemma (f pivot) tl;
    sort f (append lo (Cons pivot (sort f hi)))
