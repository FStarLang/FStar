module Ex06b
//quick-sort-poly

val mem: #t:eqtype -> t -> list t -> Tot bool
let rec mem #t a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl


val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2


val append_mem: #t:eqtype 
	      -> l1:list t
              -> l2:list t
              -> Lemma (requires True)
                       (ensures (forall a. mem a (append l1 l2) = (mem a l1 || mem a l2)))
                       [SMTPat (append l1 l2)]
let rec append_mem #t l1 l2 = match l1 with
  | [] -> ()
  | hd::tl -> append_mem tl l2


val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl


(* Specification of sortedness according to some comparison function f *)
val sorted: ('a -> 'a -> Tot bool) -> list 'a -> Tot bool
let rec sorted f l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> f x y && sorted f (y::xs)


val partition: ('a -> Tot bool) -> list 'a -> Tot (list 'a * list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2


val partition_lemma: #t:eqtype -> f:(t -> Tot bool)
   -> l:list t
   -> Lemma (requires True)
            (ensures ((length (fst (partition f l))
                     + length (snd (partition f l)) = length l
                  /\ (forall x. mem x (fst (partition f l)) ==> f x)
                  /\ (forall x. mem x (snd (partition f l)) ==> not (f x))
                  /\ (forall x. mem x l = (mem x (fst (partition f l))
                                        || mem x (snd (partition f l)))))))
            [SMTPat (partition f l)]
let rec partition_lemma #t f l = match l with
    | [] -> ()
    | hd::tl -> partition_lemma f tl


(* Defining a new predicate symbol *)
type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)


val sorted_concat_lemma: #t:eqtype 
		      -> f:(t -> t -> Tot bool)
                      -> l1:list t{sorted f l1}
                      -> l2:list t{sorted f l2}
                      -> pivot:t
                      -> Lemma (requires (total_order t f
                                       /\ (forall y. mem y l1 ==> not (f pivot y))
                                       /\ (forall y. mem y l2 ==> f pivot y)))
                               (ensures (sorted f (append l1 (pivot::l2))))
                               [SMTPat (sorted f (append l1 (pivot::l2)))]
let rec sorted_concat_lemma #t f l1 l2 pivot = match l1 with
    | [] -> ()
    | hd::tl -> sorted_concat_lemma f tl l2 pivot


val sort: #t:eqtype -> f:(t -> t -> Tot bool){total_order t f}
       -> l:list t
       -> Tot (m:list t{sorted f m /\ (forall i. mem i l = mem i m)})
              (decreases (length l))

let rec sort #t f l = match l with
  | [] -> []
  | pivot::tl ->
    let hi, lo = partition (f pivot) tl in
    let m = append (sort f lo) (pivot::sort f hi) in
    assert (forall i. mem i (pivot :: sort f hi) = mem i (append [pivot] (sort f hi)));
    m
