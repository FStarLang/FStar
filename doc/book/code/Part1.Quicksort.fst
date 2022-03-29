module Part1.Quicksort

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

//SNIPPET_START: sorted mem
let rec sorted (l:list int)
  : bool
  = match l with
    | [] -> true
    | [x] -> true
    | x :: y :: xs -> x <= y && sorted (y :: xs)

let rec mem (#a:eqtype) (i:a) (l:list a)
  : bool
  = match l with
    | [] -> false
    | hd :: tl -> hd = i || mem i tl
//SNIPPET_END: sorted mem

//SNIPPET_START: partition
let rec partition (#a:Type) (f:a -> bool) (l:list a)
  : x:(list a & list a) { length (fst x) + length (snd x) = length l }
  = match l with
    | [] -> [], []
    | hd::tl ->
      let l1, l2 = partition f tl in
      if f hd
      then hd::l1, l2
      else l1, hd::l2
//SNIPPET_END: partition

//SNIPPET_START: sort-impl
let rec sort (l:list int)
  : Tot (list int) (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let hi, lo  = partition ((<=) pivot) tl in
      append (sort lo) (pivot :: sort hi)
//SNIPPET_END: sort-impl

//SNIPPET_START: partition_mem
let rec partition_mem (#a:eqtype)
                      (f:(a -> bool))
                      (l:list a)
  : Lemma (let l1, l2 = partition f l in
           (forall x. mem x l1 ==> f x) /\
           (forall x. mem x l2 ==> not (f x)) /\
           (forall x. mem x l = (mem x l1 || mem x l2)))
  = match l with
    | [] -> ()
    | hd :: tl -> partition_mem f tl
//SNIPPET_END: partition_mem

//SNIPPET_START: sorted_concat
let rec sorted_concat (l1:list int{sorted l1})
                      (l2:list int{sorted l2})
                      (pivot:int)
  : Lemma (requires (forall y. mem y l1 ==> not (pivot <= y)) /\
                    (forall y. mem y l2 ==> pivot <= y))
          (ensures sorted (append l1 (pivot :: l2)))
  = match l1 with
    | [] -> ()
    | hd :: tl -> sorted_concat tl l2 pivot
//SNIPPET_END: sorted_concat

//SNIPPET_START: append_mem
let rec append_mem (#t:eqtype)
                   (l1 l2:list t)
  : Lemma (ensures (forall a. mem a (append l1 l2) = (mem a l1 || mem a l2)))
  = match l1 with
    | [] -> ()
    | hd::tl -> append_mem tl l2
//SNIPPET_END: append_mem

//SNIPPET_START: sort_correct
let rec sort_correct (l:list int)
  : Lemma (ensures (
           let m = sort l in
           sorted m /\
           (forall i. mem i l = mem i m)))
          (decreases (length l))
  = match l with
    | [] -> ()
    | pivot :: tl ->
      let hi, lo  = partition ((<=) pivot) tl in
      sort_correct hi;
      sort_correct lo;
      partition_mem ((<=) pivot) tl;
      sorted_concat (sort lo) (sort hi) pivot;
      append_mem (sort lo) (pivot :: sort hi)
//SNIPPET_END: sort_correct


//SNIPPET_START: sort_correct_annotated
let sort_ok (l:list int) =
    let m = sort l in
    sorted m /\
    (forall i. mem i l = mem i m)

let rec sort_correct_annotated (l:list int)
  : Lemma (ensures sort_ok l)
          (decreases (length l))
  = match l with
    | [] -> ()
    | pivot :: tl ->
      let hi, lo  = partition ((<=) pivot) tl in
      assert (length hi + length lo == length tl);
      sort_correct_annotated hi;
      assert (sort_ok hi);
      sort_correct_annotated lo;
      assert (sort_ok lo);
      partition_mem ((<=) pivot) tl;
      assert (forall i. mem i tl = mem i hi || mem i lo);
      assert (forall i. mem i hi ==> pivot <= i);
      assert (forall i. mem i lo ==> i < pivot);
      assert (sort l == (append (sort lo) (pivot :: sort hi)));
      sorted_concat (sort lo) (sort hi) pivot;
      assert (sorted (sort l));
      append_mem (sort lo) (pivot :: sort hi);
      assert (forall i. mem i l = mem i (sort l))
//SNIPPET_END: sort_correct_annotated

//SNIPPET_START: sort_alt
let rec sort_alt (l:list int)
  : Tot (list int) (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let hi, lo  = partition (fun x -> pivot <= x) tl in
      append (sort_alt lo) (pivot :: sort_alt hi)
//SNIPPET_END: sort_alt

//SNIPPET_START: sort_alt_correct
let sort_alt_ok (l:list int) =
    let m = sort_alt l in
    sorted m /\
    (forall i. mem i l = mem i m)

let rec sort_alt_correct_annotated (l:list int)
  : Lemma (ensures sort_alt_ok l)
          (decreases (length l))
  = match l with
    | [] -> ()
    | pivot :: tl ->
      let hi, lo  = partition (fun x -> pivot <= x) tl in
      assert (length hi + length lo == length tl);
      sort_alt_correct_annotated hi;
      assert (sort_alt_ok hi);
      sort_alt_correct_annotated lo;
      assert (sort_alt_ok lo);
      partition_mem (fun x -> pivot <= x) tl;
      assert (forall i. mem i tl = mem i hi || mem i lo);
      assert (forall i. mem i hi ==> pivot <= i);
      assert (forall i. mem i lo ==> i < pivot);
      //THIS NEXT LINE IS NOT PROVABLE BY SMT ALONE
      assume (sort_alt l == append (sort_alt lo) (pivot :: sort_alt hi));
      sorted_concat (sort_alt lo) (sort_alt hi) pivot;
      assert (sorted (sort_alt l));
      append_mem (sort_alt lo) (pivot :: sort_alt hi);
      assert (forall i. mem i l = mem i (sort_alt l))
//SNIPPET_END: sort_alt_correct


//SNIPPET_START: sort_intrinsic
let rec sort_intrinsic (l:list int)
  : Tot (m:list int {
                sorted m /\
                (forall i. mem i l = mem i m)
         })
   (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let hi, lo  = partition (fun x -> pivot <= x) tl in
      partition_mem (fun x -> pivot <= x) tl;
      sorted_concat (sort_intrinsic lo) (sort_intrinsic hi) pivot;
      append_mem (sort_intrinsic lo) (pivot :: sort_intrinsic hi);
      append (sort_intrinsic lo) (pivot :: sort_intrinsic hi)
//SNIPPET_END: sort_intrinsic
