(*
A translation to F* of Lists.v from Software Foundations
Original name: "Lists: Working with Structured Data"
*)

(* Lists of Numbers *)

module SfLists
open Prims.PURE

type ilist =
  | Nil : ilist
  | Cons : int -> ilist -> ilist

val length : ilist -> Tot nat
let rec length l =
  match l with
  | Nil -> 0
  | Cons h t -> length t + 1

val repeat : int -> count:nat -> Tot ilist
let rec repeat n count =
  match count with
  | 0 -> Nil
  | _ -> Cons n (repeat n (count - 1))

val app : ilist -> ilist -> Tot ilist
let rec app l1 l2 = 
  match l1 with
  | Nil    -> l2
  | Cons h t -> Cons h (app t l2)

val test_app1 : unit -> Fact unit
      (ensures (app (Cons 1 (Cons 2 (Cons 3 Nil))) (Cons 4 (Cons 5 Nil))
                = (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil)))))))
let test_app1 () = ()

val test_app2 : unit -> Fact unit
      (ensures (app Nil (Cons 4 (Cons 5 Nil))
                = (Cons 4 (Cons 5 Nil))))
let test_app2 () = ()

val test_app3 : unit -> Fact unit
      (ensures (app (Cons 1 (Cons 2 (Cons 3 Nil))) Nil)
                = (Cons 1 (Cons 2 (Cons 3 Nil))))
let test_app3 () = ()

val nil_app : l:ilist -> Fact unit
                              (ensures (app Nil l = l))
let nil_app l = ()

val app_nil : l:ilist -> Fact unit
                              (ensures (app l Nil = l))
let rec app_nil l =
  match l with
  | Nil -> ()
  | Cons h t -> app_nil t

val hd : l:ilist{l =!= Nil} -> Tot int
let hd l =
  match l with
  | Cons h t -> h

(* In SF they have tl Nil = nil, but we do better below *)

val tl_strange : l:ilist -> Tot ilist
let tl_strange l =
  match l with
  | Nil -> Nil
  | Cons h t -> t

val tl_strange_length_pred : l:ilist{l =!= Nil} -> Fact unit
      (ensures ((length l) - 1 = length (tl_strange l)))
let tl_strange_length_pred l = ()

val tl_strange_length_pred_equiv : l:ilist{is_Cons l} -> Fact unit
      (ensures ((length l) - 1 = length (tl_strange l)))
let tl_strange_length_pred_equiv l = ()

val tl : l:ilist{l =!= Nil} -> Tot ilist
let tl l =
  match l with
  | Cons h t -> t

val tl_length_pred : l:ilist{l =!= Nil} -> Fact unit
      (ensures ((length l) - 1 = length (tl l)))
let tl_length_pred l = ()

val app_assoc : l1 : ilist -> l2 : ilist -> l3 : ilist -> Fact unit
      (ensures (app (app l1 l2) l3) = app l1 (app l2 l3))
let rec app_assoc l1 l2 l3 =
  match l1 with
  | Nil -> ()
  | Cons h t -> app_assoc t l2 l3

val app_length : l1 : ilist -> l2 : ilist -> Fact unit
      (ensures (length (app l1 l2) = (length l1) + (length l2)))
let rec app_length l1 l2 =
  match l1 with
  | Nil -> ()
  | Cons x1 l1' -> app_length l1' l2

val snoc : ilist -> int -> Tot ilist
let rec snoc l v =
  match l with
  | Nil -> Cons v Nil
  | Cons h t -> Cons h (snoc t v)

val rev : ilist -> Tot ilist
let rec rev l =
  match l with
  | Nil -> Nil
  | Cons h t -> snoc (rev t) h

val length_snoc : n : int -> l : ilist -> Fact unit
      (ensures (length (snoc l n) = length l + 1))
let rec length_snoc n l =
  match l with
  | Nil -> ()
  | Cons h t -> length_snoc n t

val rev_length : l : ilist -> Fact unit
      (ensures (length (rev l) = length l))
let rec rev_length l =
  match l with
  | Nil -> ()
  | Cons h t -> length_snoc h (rev t); rev_length t

val foo1 : n:int -> l : ilist -> Pure unit
      (requires (repeat n 0 = l))
      (ensures \r -> length l = 0)
let foo1 n l = ()

val foo2 : n : nat -> m : nat -> l : ilist -> Pure unit
      (requires (repeat n m = l))
      (ensures \r -> length l = m)
let rec foo2 n m l =
  match m with
  | 0 -> () 
  | _ -> foo2 n (m-1) (repeat n (m-1))

val foo3 : l : ilist -> n : int -> m : nat -> Pure unit
      (requires (length l = m))
      (ensures \r -> (length (snoc l n) = m+1))
let rec foo3 l n m =
  match l with
  | Nil -> ()
  | Cons h t -> foo3 t n (length t)

val foo4 : n : int -> l1 : ilist -> l2 : ilist -> Pure unit
      (requires (snoc l1 n = l2))
      (ensures \r -> 0 < length l2)
let foo4 n l1 l2 = ()




val snoc_cons: l:ilist -> h:int -> Lemma True (rev (snoc l h) = Cons h (rev l)) [VPat (ilist -> Tot ilist) rev; VPat (ilist -> int -> Tot ilist) snoc]
let rec snoc_cons l h = match l with
  | Nil -> ()
  | Cons hd tl ->
    let ih = snoc_cons tl h in
    ()

val rev_involutive: l:ilist -> Lemma True (rev (rev l) = l) []
let rec rev_involutive l = match l with
  | Nil -> ()
  | Cons h t ->
    let ih = rev_involutive t in
    let lem = snoc_cons (rev t) h in
    ()

val snoc_injective: l1:ilist -> h1:int -> l2:ilist -> h2:int -> Fact unit (snoc l1 h1 = snoc l2 h2 ==> l1 = l2 /\ h1 = h2)
let rec snoc_injective l1 h1 l2 h2 = match (l1, l2) with
  | Nil, Nil -> ()
  | Cons hd1 tl1, Cons hd2 tl2 ->
    let ih = snoc_injective tl1 h1 tl2 h2 in
    ()
  | _, _ -> ()

val rev_injective: l1:ilist -> l2:ilist -> Fact unit (rev l1 = rev l2 ==> l1 = l2)
let rec rev_injective l1 l2 = match (l1, l2) with
  | Nil, Nil -> ()
  | Cons hd1 tl1, Cons hd2 tl2 ->
    let ih = rev_injective tl1 tl2 in
    let lem = snoc_injective (rev tl1) hd1 (rev tl2) hd2 in
    ()
  | _, _ -> ()

val fold_left: 'a:Type -> f:(int -> 'a -> Tot 'a) -> l:ilist -> 'a -> Tot 'a
let rec fold_left f l a = match l with
  | Nil -> a
  | Cons hd tl -> fold_left f tl (f hd a)

val app_cons: l:ilist -> hd:int -> tl:ilist -> Fact unit (app l (Cons hd tl) = app (app l (Cons hd Nil)) (tl))
let rec app_cons l hd tl = match l with
  | Nil -> ()
  | Cons hd' tl' ->
    let ih = app_cons tl' hd tl in
    ()

val snoc_app: l:ilist -> h:int -> Fact unit (snoc l h = app l (Cons h Nil))
let rec snoc_app l h = match l with
  | Nil -> ()
  | Cons hd tl ->
    let _ = snoc_app tl h in
    ()

val rev_app: tl:ilist -> hd:int -> Fact unit (rev (Cons hd tl) = app (rev tl) (Cons hd Nil))
let rev_app tl hd = snoc_app (rev tl) hd

let g x l = Cons x l

val fold_left_cons_is_rev: l:ilist -> l':ilist -> Fact unit (fold_left g l l' = app (rev l) l')
let rec fold_left_cons_is_rev l l' = match l with
  | Nil -> ()
  | Cons hd tl ->
    let _ = fold_left_cons_is_rev tl (Cons hd l') in
    let _ = app_cons (rev tl) hd l' in
    let _ = rev_app tl hd in
    ()
