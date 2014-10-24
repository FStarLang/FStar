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

type nat = i:int{i >= 0}

val length : ilist -> Tot nat
let rec length l =
  match l with
  | Nil -> 0
  | Cons h t -> length t + 1

val repeat : int -> count:nat -> Tot (i:ilist{length i == count})
let rec repeat n count = 
  if count = 0 
  then Nil
  else if count > 0
  then let tl = repeat n (count - 1) in (* NS: TODO ... seem to need an explicit let here, otherwise the refinement is lost. Fix! *)
       Cons n tl
  else (assert False; Nil)


val app : ilist -> ilist -> Tot ilist
let rec app l1 l2 = 
  match l1 with
  | Nil    -> l2
  | Cons h t -> Cons h (app t l2)

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

val hd : l:ilist{l =!= Nil} -> Tot int
let hd l =
  match l with
  | Cons h t -> h

(* In SF they have tl Nil == nil, but we do better here *)
(* val tl : l:ilist{l =!= Nil} -> Tot ilist *)
(* let tl l = *)
(*   match l with *)
(*   | Cons h t -> t *)

val tl : l:ilist -> Tot ilist
let tl l =
  match l with
  | Nil -> Nil
  | Cons h t -> t


val nil_app : l:ilist -> Fact unit
                              (ensures (app Nil l == l))
let nil_app l = ()

(* (\* CH: I have no clue why this still fails *\) *)
(* val tl_length_pred : l:ilist{l =!= Nil} -> Fact unit *)
(*       (ensures ((length l) - 1 == length (tl l))) *)
(* let tl_length_pred l = () *)

val tl_length_pred_fixed : l:ilist{is_Cons l} -> Fact unit
                                                      (ensures ((length l) - 1 == length (tl l)))
let tl_length_pred_fixed l = ()

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

let z:nat = 0 //TODO: relax restriction on well-formedness of types having trivial refinements

val foo1 : n:int -> l : ilist -> Pure unit
      (requires (repeat n z == l))
      (ensures \r => length l == 0) (* NS: now works. Needed to prove a property about the length of repeat, which I did intrinsically above. *)
let foo1 n l = ()                   (* CH: this should succeed. NS: and it does *)
    (* CH: From an extrinsic proof point of view, this is just cheating.
           Any reason we can't have a purely-extrinsic proof of this? *)

val foo2 : n : nat -> m : nat -> l : ilist -> Pure unit
      (requires (repeat n m == l))
      (ensures \r => length l == m)
let rec foo2 n m l = 
  match m with
  | 0 -> ()  (* CH: should actually work without a call to foo1? NS: And it does with the property about the length of repeat. *)(* CH: ditto, this is no longer an extrinsic proof, basically the refinement you've put on repeat directly implies foo2 *)
  | _ -> foo2 n (m-1) (repeat n (m-1))
         (* CH: this should succeed (NS: and it does), and (NS: the previous version should) clearly not fail pre-type-checking
            it's a frequent pattern for generalizing the induction hypothesis *)
         (* NS: TODO: explicit generalization fails pre-type checking. Fix! 
            But, FYI, all let-rec bound names are implicitly generalized. So, no need for this pattern. *)
         (* CH: This is very cool, a consequence of having n-argument
                fixpoints, while Coq only only has one argument ones *)

val foo3 : l : ilist -> n : int -> m : int -> Pure unit
      (requires (length l == m))
      (ensures \r => (length (snoc l n) == m+1))
let rec foo3 l n m =
  match l with
  | Nil -> ()
  | Cons h t -> foo3 t n (length t)

(* CH: this should succeed (at least in Coq it doesn't use induction
   or additional lemmas, just a destruct l1 which I've done below,
   but which Z3 should anyway be able to do automatically) *)
(* NS: it works now *)
val foo4 : n : int -> l1 : ilist -> l2 : ilist -> Pure unit
      (requires (snoc l1 n == l2))
      (ensures \r => 0 < length l2)
let foo4 n l1 l2 = ()
