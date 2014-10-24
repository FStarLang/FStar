(*
A translation to F* of Poly.v from Software Foundations
Original name: "Polymorphism and Higher-Order Functions"
*)

module SfPoly
open Prims.PURE

(* Lists, pairs, options (using the F* definitions directly) *)

val length : list 'a -> Tot nat
let rec length l =
  match l with
  | [] -> 0
  | hd::tl -> 1 + length tl

val test_length1 : unit -> Fact unit
      (ensures (length [1;2] == 2))
let test_length1 () = ()

val test_length2 : unit -> Fact unit
      (ensures (length [true] == 1))
let test_length2 () = ()

val app : list 'a -> list 'a -> Tot (list 'a)
let rec app l1 l2 =
  match l1 with
  | []   -> l2
  | h::t -> h :: app t l2

val snoc : list 'a -> 'a -> Tot (list 'a)
let rec snoc l x =
  match l with
  | []   -> [x]
  | h::t -> h :: snoc t x

val rev : list 'a -> Tot (list 'a)
let rec rev l =
  match l with
  | []   -> []
  | h::t -> snoc (rev t) h

val combine : list 'a -> list 'b -> list ('a * 'b)
let rec combine la lb =
  match (la,lb) with
  | ([],_) -> []
  | (_,[]) -> []
  | (a::ta, b::tb) -> (a,b) :: (combine ta tb)

(* In SF index returns an option, but we can do much better *)

val index_option : list 'a -> nat -> Tot (option 'a)
let rec index_option l n =
  match l with
  | [] -> None
  | h :: t -> if n = 0 then Some h else index_option t (n-1)

(* All these fail and I think they shouldn't
val test_index_option1 : unit -> Fact unit
      (ensures (index_option [4;5;6;7] 0 == Some 4))
let test_index_option1 () = ()

val test_index_option2 : unit -> Fact unit
      (ensures (index_option [[1];[2]] 1 == Some [2]))
let test_index_option2 () = ()

(* CH: This should succeed *)
val test_index_option3 : unit -> Fact unit
      (ensures (index_option [true] 2 == None))
let test_index_option3 () = ()
*)

(* test_index_option3 fails even if we replace
   the "if" in index_option with a "match" *)
val index_option' : list 'a -> nat -> Tot (option 'a)
let rec index_option' l n =
  match l with
  | [] -> None
  | h :: t -> begin
    match n with
    | 0 -> Some h
    | _ -> index_option' t (n-1)
    end

(* now this fails for other reasons, but it shouldn't
val test_index_option3' : unit -> Fact unit
      (ensures (index_option' [true] 2 == None))
let test_index_option3' () = ()
*)

assume val impossible : u : unit { False } -> Tot 'a
(* let impossible = failwith "this won't happen"  -- this blows up *)

(* CH: This should really work *)
val length_nil : unit -> Fact unit
      (ensures (length [] == 0))
let length_nil () = ()

(* Was getting incomplete patterns here, with or without the [] pattern,
   caused by the same problem with length_nil I think, still it should
   be a different error message when the [] pattern is present *)
val index : l : list 'a -> n:int{(0 <= n) /\ (n < length l)} -> Tot 'a
let rec index l n =
  match l with
  | h :: t -> if n = 0 then h else index t (n-1)

(* Functions as Data *)

(* This is as pure as it gets, still it gets inferred ALL effect 
   NS: Unannotated let recs have the ALL effect. To get the Tot effect, you must request it (enabling the termination checker).
   NS: BTW, the default function type has ML effect, so if not annotated, test will be in ML, and so the whole thing will be ALL. 
   NS: An alternative may be to have some other syntax, like fix instead let rec, to locally change the default function effect to Tot.
*)
val filter : test:('a->Tot bool) -> l:(list 'a) -> Tot (list 'a)
let rec filter test l =
  match l with
  | []     -> []
  | h :: t -> if test h then h :: (filter test t)
                        else       filter test t

(* seems that typing for % is very restrictive
val evenb : int -> Tot bool
let evenb i = i % 2 = 0
I would prefer something like this for %
assume val mod : x : int -> y:int{x =!= 0} -> Tot int
*)

val evenb : int -> Tot bool
let rec evenb i =
  match i with
  | 0 -> true
  | 1 -> false
  | _ -> evenb (i-2)

val test_filter1 : unit -> Fact unit
      (ensures (filter evenb [1;2;3;4] == [2;4]))
let test_filter1 () = ()

(* Map *)








