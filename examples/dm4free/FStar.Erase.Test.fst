module FStar.Erase.Test

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST
open FStar.Erase.Heap.ST
module L = FStar.List.Tot

(* let h (pre:st_pre) (post:st_post unit) (f: unit -> ST unit pre post) (h:heap) = *)
(*   let g () : Lemma (fst (reify (f ())) h == ()) = () in *)
(*   () *)

let memo_t (a:eqtype) (b:Type) = ref (list (a * b))

(* ******************************************************************************** *)
(*                                  Taken from Memo                                 *)
(* ******************************************************************************** *)

let rec for_all_prop (#a:Type) (p:a -> Type0) (l:list a) : Tot Type0 (decreases l)
= match l with
  | [] -> True
  | x :: xs -> p x /\ for_all_prop p xs

let rec for_all_prop_assoc_lemma (#a:eqtype) (#b:Type) (x:a) (p : (a * b) -> Tot Type0) (l:list (a*b))
  : Lemma (requires (for_all_prop p l))
    (ensures (match L.assoc x l with Some y -> p (x,y) | _ -> True))
= match l with
  | [] -> ()
  | (x0, y0) :: xs -> if x0 = x then () else for_all_prop_assoc_lemma x p xs

let forall_prop_assoc_lemma2 (#a:eqtype) (#b:Type) (x:a) (y:b) (p : (a * b) -> Tot Type0)
  : Lemma (forall h. for_all_prop p h /\ List.assoc x h == Some y ==> p (x,y))
= let aux h : Lemma (requires (for_all_prop p h /\ List.assoc x h == Some y)) (ensures (p (x,y))) =
      for_all_prop_assoc_lemma x p h
  in
  FStar.Classical.(forall_intro (move_requires aux))

let valid_memo (#a:eqtype) (#b:Type) (h:list (a * b)) (f:a -> Tot b) =
  for_all_prop (fun (x,y) -> y == f x) h

let memo_invariant (#a:eqtype) (#b:Type) (f: a -> Tot b) (r:memo_t a b) : inductive_inv =
  fun (h:heap) ->
    h `contains_a_well_typed` r /\
    valid_memo (sel h r) f

let memo_initializer (#a:eqtype) (#b:Type) (f:a -> Tot b)
  : erase_initializer (memo_invariant f)
= fun () -> alloc []

let memo (#a:eqtype) (#b:Type) (f:a -> Tot b) (r:memo_t a b) : Tot (x:a -> ST b (requires (memo_invariant f r)) (ensures (fun _ y h1 -> memo_invariant f r h1 /\ y == f x))) =
  let g (x:a) : ST b (requires (memo_invariant f r)) (ensures (fun _ y h1 -> memo_invariant f r h1 /\ y == f x)) =
    match L.assoc x !r with
    | Some y ->
      forall_prop_assoc_lemma2 x y (fun (x,y) -> y == f x) ;
      y
    | None -> let y = f x in r := (x,y) :: !r ; y
  in g

open FStar.Classical

let impl_intro (#p:Type0) (#q:Type0) ($f: (squash p) -> Lemma q) : Lemma (p ==> q)  =
      give_witness #(p ==> q) (arrow_to_impl (lemma_to_squash_gtot f))

let memo_invariant_valid (#a:eqtype) (#b:Type) (f:a -> Tot b) (r:memo_t a b)
  : Lemma (invariant #a #b (memo_invariant f r) (fun _ -> True) (fun x y -> y == f x) #(fun _ -> memo_invariant f r) #(fun x _ y h1 -> memo_invariant f r h1 /\ y == f x) (memo f r))
= let p = (memo_invariant f r) in
  let pre_pure = (fun _ -> True) in
  let post_pure = (fun x y -> y == f x) in
  let pre = (fun _ -> memo_invariant f r) in
  let post = (fun x _ y h1 -> memo_invariant f r h1 /\ y == f x) in
  let f0 = f in
  let f = (memo f r) in
  let stuff (s1 s2:heap) (_:squash (p s1 /\ p s2)) (x:a) (w:squash (pre_pure x))
    : Lemma (fst (reify (f x) s1) == fst (reify (f x) s2)) =
    let _ = reify (f x) s1 in
    let _  = reify (f x) s2 in
    ()
  in
  (* let h0 s1 s2 h1 : Lemma (forall x. pre_pure x ==> (fst (reify (f x) s1) == fst (reify (f x) s2))) = *)
  (*   forall_intro (fun x -> impl_intro (stuff s1 s2 h1 x)) *)
  (* in *)
  (* let h1 s1 s2 : Lemma (p s1 /\ p s2 ==> (forall x. pre_pure x ==> (fst (reify (f x) s1) == fst (reify (f x) s2)))) = impl_intro (h0 s1 s2) in *)
  (* forall_intro_2 h1 ; *)
  assert (forall x s. (p s /\ pre_pure x) ==> pre x s) ;
  assert (forall x s1 s2 y. (p s1 /\ post x s1 y s2) ==> (p s2 /\ post_pure x y)) ;
  assume (forall s1 s2. p s1 /\ p s2 ==> (forall x. pre_pure x ==> fst (reify (f x) s1) == fst (reify (f x) s2)))

  (* Eat up mre than 6G of ram... *)
  (* assert_by_tactic *)
  (*   (forall s1 s2. p s1 /\ p s2 ==> (forall x. pre_pure x ==> fst (reify (f x) s1) == fst (reify (f x) s2))) *)
  (*   (s1 <-- forall_intro ; *)
  (*    s2 <-- forall_intro ; *)
  (*    h1 <-- implies_intro ; *)
  (*    x <-- forall_intro ; *)
  (*    h2 <-- implies_intro ; *)
  (*    apply_lemma (quote stuff) ; *)
  (*    fail "") ; *)

let memo_invariant_valid' (#a:eqtype) (#b:Type) (f:a -> Tot b)
    : Lemma (forall (r:memo_t a b). invariant #a #b (memo_invariant f r) (fun _ -> True) (fun x y -> y == f x) #(fun _ -> memo_invariant f r) #(fun x _ y h1 -> memo_invariant f r h1 /\ y == f x) (memo f r))
= forall_intro (memo_invariant_valid f)

let pure_memo (#a:eqtype) (#b:Type) (f:a -> Tot b) : Pure (a -> Tot b)(requires True) (ensures (fun g -> forall x. g x == f x))=
  memo_invariant_valid' f ;
  erase_st #a #b (memo_invariant f) (fun _ -> True) (fun x y -> y == f x) #(fun r _ -> memo_invariant f r) #(fun r x _ y h1 -> memo_invariant f r h1 /\ y == f x) (memo f) (memo_initializer f)
