module Part1.Quicksort.Permutation
#push-options "--fuel 1 --ifuel 1"

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
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                       (* totality *)
let total_order_t (a:Type) = f:(a -> a -> bool) { total_order f }

let rec sorted #a  (f:total_order_t a) (l:list a)
  : bool
  = match l with
    | [] -> true
    | [x] -> true
    | x :: y :: xs -> f x y && sorted f (y :: xs)

//SNIPPET_START: count permutation
let rec count (#a:eqtype) (x:a) (l:list a)
  : nat
  = match l with
    | hd::tl -> (if hd = x then 1 else 0) + count x tl
    | [] -> 0

let mem (#a:eqtype) (i:a) (l:list a)
  : bool
  = count i l > 0

let is_permutation (#a:eqtype) (l m:list a) =
  forall x. count x l = count x m

let rec append_count (#t:eqtype)
                     (l1 l2:list t)
  : Lemma (ensures (forall a. count a (append l1 l2) = (count a l1 + count a l2)))
  = match l1 with
    | [] -> ()
    | hd::tl -> append_count tl l2
//SNIPPET_END: count permutation

let rec partition (#a:Type) (f:a -> bool) (l:list a)
  : x:(list a & list a) { length (fst x) + length (snd x) = length l }
  = match l with
    | [] -> [], []
    | hd::tl ->
      let l1, l2 = partition f tl in
      if f hd
      then hd::l1, l2
      else l1, hd::l2

let rec sort #a (f:total_order_t a) (l:list a)
  : Tot (list a) (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let hi, lo  = partition (f pivot) tl in
      append (sort f lo) (pivot :: sort f hi)

let rec partition_mem_permutation (#a:eqtype)
                                  (f:(a -> bool))
                                  (l:list a)
  : Lemma (let l1, l2 = partition f l in
           (forall x. mem x l1 ==> f x) /\
           (forall x. mem x l2 ==> not (f x)) /\
           (is_permutation l (append l1 l2)))
  = match l with
    | [] -> ()
    | hd :: tl -> 
      partition_mem_permutation f tl;
      let hi, lo = partition f tl in
      append_count hi lo;
      append_count hi (hd::lo);
      append_count (hd :: hi) lo

let rec sorted_concat (#a:eqtype)
                      (f:total_order_t a)
                      (l1:list a{sorted f l1})
                      (l2:list a{sorted f l2})
                      (pivot:a)
  : Lemma (requires (forall y. mem y l1 ==> not (f pivot y)) /\
                    (forall y. mem y l2 ==> f pivot y))
          (ensures sorted f (append l1 (pivot :: l2)))
  = match l1 with
    | [] -> ()
    | hd :: tl -> sorted_concat f tl l2 pivot

let permutation_app_lemma (#a:eqtype) (hd:a) (tl:list a)
                          (l1:list a) (l2:list a)
   : Lemma (requires (is_permutation tl (append l1 l2)))
           (ensures (is_permutation (hd::tl) (append l1 (hd::l2))))
  = append_count l1 l2;
    append_count l1 (hd :: l2)
  
let rec sort_correct (#a:eqtype) (f:total_order_t a) (l:list a)
  : Lemma (ensures (
           sorted f (sort f l) /\
           is_permutation l (sort f l)))
          (decreases (length l))
  = match l with
    | [] -> ()
    | pivot :: tl ->
      let hi, lo  = partition (f pivot) tl in
      partition_mem_permutation (f pivot) tl;
      append_count lo hi;
      append_count hi lo;
      assert (is_permutation tl (append lo hi));
      sort_correct f hi;
      sort_correct f lo;
      sorted_concat f (sort f lo) (sort f hi) pivot;
      append_count (sort f lo) (sort f hi);
      assert (is_permutation tl (sort f lo `append` sort f hi));
      permutation_app_lemma pivot tl (sort f lo) (sort f hi)
      

let rec sort_intrinsic (#a:eqtype) (f:total_order_t a) (l:list a)
  : Tot (m:list a {
                sorted f m /\
                is_permutation l m
         })
   (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let hi, lo  = partition (f pivot) tl in
      partition_mem_permutation (f pivot) tl;
      append_count lo hi;  append_count hi lo;
      sorted_concat f (sort_intrinsic f lo) (sort_intrinsic f hi) pivot;
      append_count (sort_intrinsic f lo) (sort_intrinsic f hi);
      permutation_app_lemma pivot tl (sort_intrinsic f lo) (sort_intrinsic f hi);
      append (sort_intrinsic f lo) (pivot :: sort_intrinsic f hi)


