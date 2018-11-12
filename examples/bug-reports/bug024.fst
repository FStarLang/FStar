module Bug024

(* Example 1 works now *)

(* Example 2 *)

(* Adding this signature makes it work
val nth : list 'a -> int *)
(* Also removing the rec makes it work *)
let rec nth l = match l with
    | [] -> 0
    | x::xs -> 1

(* Example 3

val length : list 'a -> Tot nat
let rec length l =
  match l with
  | [] -> 0
  | hd::tl -> 1 + length tl

val length_nil : unit -> Lemma
      (ensures (length [] = 0))
let length_nil () = ()

assume val impossible : u : unit { False } -> Tot 'a

(* Getting incomplete patterns here, with or without the [] pattern,
   caused by the same problem as length_nil I think; it should clearly
   be a different error message when the [] pattern is present *)
val index : l : list 'a -> n:int{(0 <= n) /\ (n < length l)} -> Tot 'a
let rec index l n =
  match l with
  | [] -> length_nil(); impossible()
  | h :: t -> if n = 0 then h else index t (n-1)

*)
