(*
A translation to F* of Lists.v from Software Foundations
Original name: "Lists: Working with Structured Data"
*)

(* Lists of Numbers *)

module SfLists
open Prims.PURE

(* NS: You need to write admit P (), for some formula P; admit False (),
       for example.
       Inference does not figure out what that formula should be.
       TODO: need to fix something so that you can just write (admit P),
       instead of the addition () argument. *)
(* CH: This is what I actually need (it matches what Coq does) *)
let admit () = admit False ()

type ilist =
  | Nil : ilist
  | Cons : int -> ilist -> ilist

val repeat : int -> int -> Tot ilist
let rec repeat (n : int) (count : int) : ilist =
  match count with
  | 0 -> Nil
  | _ -> Cons n (repeat n (count-1))

val length : ilist -> Tot int
let rec length l =
  match l with
  | Nil -> 0
  | Cons h t -> length t + 1

val app : ilist -> ilist -> Tot ilist
let rec app l1 l2 = 
  match l1 with
  | Nil    -> l2
  | Cons h t -> Cons h (app t l2)

val hd : l : ilist{l =!= Nil} -> Tot int
let hd l =
  match l with
  | Cons h t -> h

val tl : ilist -> Tot ilist
let tl l =
  match l with
  | Nil -> Nil
  | Cons h t -> t

val test_app1 : unit -> Fact unit
      (ensures (app (Cons 1 (Cons 2 (Cons 3 Nil))) (Cons 4 (Cons 5 Nil))
                == (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil)))))))
let test_app1 () = ()

val test_app2 : unit -> Fact unit
      (ensures (app Nil (Cons 4 (Cons 5 Nil))
                == (Cons 4 (Cons 5 Nil))))
let test_app2 () = ()

val test_app3 : unit -> Fact unit
      (ensures (app (Cons 1 (Cons 2 (Cons 3 Nil))) Nil)
                == (Cons 1 (Cons 2 (Cons 3 Nil))))
let test_app3 () = ()

val nil_app : l:ilist -> Fact unit
      (ensures (app Nil l == l))
let nil_app l = ()

(* This doesn't work *)
(* NS: fails ... need to investigate *)
val tl_length_pred : l:ilist -> Fact unit
      (ensures ((length l) - 1 == length (tl l)))
let tl_length_pred l =
  match l with
  | Nil -> ()
  | Cons h t -> ()

val app_assoc : l1 : ilist -> l2 : ilist -> l3 : ilist -> Fact unit
      (ensures (app (app l1 l2) l3) == app l1 (app l2 l3))
let rec app_assoc l1 l2 l3 =
  match l1 with
  | Nil -> ()
  | Cons h t -> app_assoc t l2 l3

val app_length : l1 : ilist -> l2 : ilist -> Fact unit
      (ensures (length (app l1 l2) == (length l1) + (length l2)))
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
      (ensures (length (snoc l n) == length l + 1))
let rec length_snoc n l =
  match l with
  | Nil -> ()
  | Cons h t -> length_snoc n t

val rev_length : l : ilist -> Fact unit
      (ensures (length (rev l) == length l))
let rec rev_length l =
  match l with
  | Nil -> ()
  | Cons h t -> length_snoc h (rev t); rev_length t

val foo1 : n : int -> l : ilist -> Pure unit
      (requires (repeat n 0 == l))
      (ensures \r => length l == 0) (* NS: fails ... need to investigate *)
let foo1 n l = ()                   (* CH: this should succeed *)

val foo2 : n : int -> m : int -> l : ilist -> Pure unit
      (requires (repeat n m == l))
      (ensures \r => length l == m)
let rec foo2 n m =
  match m with
  | 0 -> (fun l => foo1 n l) (* CH: should actually work without a call to foo1? *)
  | _ -> (fun l => foo2 n (m-1) (repeat n (m-1)))
         (* CH: this should succeed, and clearly not fail pre-type-checking
            it's a frequent pattern for generalizing the induction hypothesis *)
 
(* NS: fails, need to investigate *)
(* CH: after my fixes to it, it should succeed,
   but it fails with same problem as above *)
val foo3 : l : ilist -> n : int -> m : int -> Pure unit
      (requires (length l == m))
      (ensures \r => (length (snoc l n) == m+1))
let rec foo3 l n =
  match l with
  | Nil -> (fun m => ())
  | Cons h t -> (fun m => foo3 t n (length t))

(* CH: this should succeed (at least in Coq it doesn't use induction
   or additional lemmas, just a destruct l1 which I've done below,
   but which Z3 should anyway be able to do automatically) *)
val foo4 : n : int -> l1 : ilist -> l2 : ilist -> Pure unit
      (requires (snoc l1 n == l2))
      (ensures \r => 0 < length l2)
let foo4 n l1 l2 =
  match l1 with
  | Nil -> ()
  | Cons h t -> ()
