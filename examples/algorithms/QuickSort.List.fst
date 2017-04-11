module QuickSort.List

#set-options "--initial_ifuel 1 --initial_fuel 1 --max_ifuel 1 --max_fuel 1"

open FStar.List.Tot

(* Specification of sorted according to a comparison function f *)
val sorted: ('a -> 'a -> Tot bool) -> list 'a -> Tot bool
let rec sorted f = function
  | x::y::xs -> f x y && sorted f (y::xs)
  | _ -> true

type total_order (a:eqtype) =
  f:(a -> a -> Tot bool) {
      (forall a. f a a) // reflexive
    /\ (forall a1 a2. f a1 a2 /\ f a2 a1 ==> a1 = a2) // anti-symmetric
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) // transitive
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1) // total
  }

val count: #a:eqtype -> a -> list a -> Tot nat
let rec count #a x = function
  | hd::tl -> (if hd = x then 1 else 0) + count x tl
  | [] -> 0


val mem_count: #a:eqtype -> x:a -> l:list a ->
  Lemma (requires True)
	(ensures (mem x l = (count x l > 0)))
	(decreases l)
  [SMTPat (mem x l)]
let rec mem_count #a x = function
  | [] -> ()
  | _::tl -> mem_count x tl


val append_count: #a:eqtype -> l:list a -> m:list a -> x:a ->
  Lemma (requires True)
        (ensures (count x (l @ m) = (count x l + count x m)))
  [SMTPat (count x (l @ m))]
let rec append_count #a l m x =
  match l with
  | [] -> ()
  | hd::tl -> append_count tl m x


val partition: ('a -> Tot bool) -> list 'a -> Tot (list 'a * list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
    let l1, l2 = partition f tl in
    if f hd then (hd::l1, l2) else (l1, hd::l2)


val partition_lemma: #a:eqtype -> f:(a -> Tot bool) -> l:list a ->
  Lemma (requires True)
        (ensures (let (hi, lo) = partition f l in
                  length l = length hi + length lo
                  /\ (forall x. (mem x hi ==>   f x)
                        /\ (mem x lo ==> ~(f x))
                        /\ (count x l = count x hi + count x lo))))
  [SMTPat (partition f l)]
let rec partition_lemma #a f l = match l with
  | [] -> ()
  | hd::tl ->  partition_lemma f tl


val sorted_app_lemma: #a:eqtype -> f:total_order a
  -> l1:list a{sorted f l1} -> l2:list a{sorted f l2} -> pivot:a
  -> Lemma (requires (forall y. (mem y l1 ==> ~(f pivot y))
		        /\ (mem y l2 ==>   f pivot y)))
          (ensures (sorted f (l1 @ pivot :: l2)))
  [SMTPat (sorted f (l1 @ pivot::l2))]
let rec sorted_app_lemma #a f l1 l2 pivot =
  match l1 with
  | hd::tl -> sorted_app_lemma f tl l2 pivot
  | _ -> ()

type is_permutation (a:eqtype) (l:list a) (m:list a) =
  forall x. count x l = count x m

val quicksort: #a:eqtype -> f:total_order a -> l:list a ->
  Tot (m:list a{sorted f m /\ is_permutation a l m})
  (decreases (length l))
//NS: for CI, replaying this with hints fails; 
//    Then it requires finding a proof in a fresh solver context
//    which now seems to take a lot of time ... without the lemma invocation below
let rec quicksort #a f = function
  | [] -> []
  | pivot::tl ->
    let hi, lo = partition (f pivot) tl in
    partition_lemma (f pivot) tl;  //without this, proof takes a much longer now (e.g., ~20s)
    (quicksort f lo) @ pivot :: quicksort f hi
