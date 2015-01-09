module QuickSortPoly

val mem: 'a -> list 'a -> Tot bool
let rec mem a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

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

val partition_lemma: f:('a -> Tot bool)
                   -> l:list 'a
                   -> Lemma (requires True)
                            (ensures ((length (fst (partition f l)) + length (snd (partition f l)) = length l
                                 /\ (forall x. mem x (fst (partition f l)) ==> f x)
                                 /\ (forall x. mem x (snd (partition f l)) ==> not (f x))
                                 /\ (forall x. mem x l = (mem x (fst (partition f l)) || mem x (snd (partition f l)))))))
let rec partition_lemma f l = match l with 
  | [] -> ()
  | hd::tl -> partition_lemma f tl

(* Specification of sortedness according to some comparison function f *)
val sorted: ('a -> 'a -> Tot bool) -> list 'a -> Tot bool
let rec sorted f = function
  | []
  | [_] -> true
  | x::y::tl -> f x y && sorted f (y::tl)

val sorted_concat_lemma: l1:list int{sorted l1}
                      -> l2:list int{sorted l2}
                      -> pivot:int
                      -> Lemma (requires ((forall y. mem y l1 ==> not (pivot <= y))
                                       /\ (forall y. mem y l2 ==> pivot <= y)))
                               (ensures (sorted (append l1 (pivot::l2))))
                         [SMTPat (sorted (append l1 (pivot::l2)))]

(* Use the same lemma about List.partition as previously. *)

(* Defining a new predicate symbol *)
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
                                    /\ (forall y. mem y l2 ==> f pivot y)))
                         (ensures (sorted f (append l1 (pivot::l2))))
                         [SMTPat (sorted f (append l1 (pivot::l2)))]
let rec sorted_concat_lemma f l1 l2 pivot = match l1 with 
  | [] -> ()
  | hd::tl -> sorted_concat_lemma f tl l2 pivot

val sort: f:('a -> 'a -> Tot bool){total_order 'a f}
      ->  l:list 'a
      ->  Tot (m:list 'a{sorted f m /\ (forall x. mem x l = mem x m)})
              (decreases (length l))
let rec sort f = function
  | [] -> []
  | pivot::tl -> 
    let hi, lo  = partition (f pivot) tl in 
    partition_lemma (f pivot) tl;
    sort f (append lo (pivot::sort f hi))
