(*
A translation to F* of Poly.v from Software Foundations
Original name: "Polymorphism and Higher-Order Functions"
*)

(* This chapter is very boring in terms of proofs *)

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

(* Getting incomplete patterns here, with or without the [] pattern,
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

val evenb : nat -> Tot bool
let rec evenb i =
  match i with
  | 0 -> true
  | 1 -> false
  | _ -> evenb (i-2)

val oddb : nat -> Tot bool
let oddb n = not (evenb n)

(* CH: This fails as follows:
Failed because: refinement subtyping is not applicable
Incompatible types (list i:int{i >= 0}) and (list nat)
val test_filter1 : unit -> Fact unit
      (ensures (filter evenb [1;2;3;4] == [2;4]))
let test_filter1 () = ()
*)

(* Map *)

val map : ('a->Tot 'b) -> (list 'a) -> Tot (list 'b)
let rec map f l =
  match l with
  | []     -> []
  | h :: t -> (f h) :: (map f t)

val plus3 : int -> Tot int
let plus3 n = n + 3

val test_map1 : unit -> Fact unit
      (ensures (map plus3 [2;0;2] == [5;3;5]))
(* CH: Replacing plus3 with a lambda (just inlining) fails to parse +, strange *)
let test_map1 () = ()

(* CH: again: Incompatible types (list i:int{i >= 0}) and (list nat)
val test_map2 : unit -> Fact unit
      (ensures (map oddb [2;1;2;5] == [false;true;false;true]))
let test_map2 () = ()
*)

(* This shouldn't blow up:
unknown(0,0-0,0) : Error
Identifier not found: [Prims.Cons] (Possible clash with related name at ../../lib/prims.fst(477,0-481,6))
val test_map3 : unit -> Fact unit
    (ensures (map (fun n => [evenb n;oddb n]) [2;1;2;5]
              == [[true;false];[false;true];[true;false];[false;true]]))
*)

(* Map for options *)

val option_map : ('a -> Tot 'b) -> option 'a -> Tot (option 'b)
let option_map f o =
  match o with
    | None   -> None
    | Some a -> Some (f a)

(* Fold *)

val fold : (f : 'a -> 'b -> Tot 'b) -> list 'a -> 'b -> Tot 'b
let rec fold f l b =
  match l with
  | []   -> b
  | h::t -> f h (fold f t b)

(* CH: This completely blows up because of the lambda
   Bound term variable not found: x
val fold_example1 : unit -> Fact unit 
      (ensures (fold (fun x y -> x * y) [1;2;3;4] 1 == 24))
let fold_example1 () = ()
*)

(* CH: Without the lambda it works fine *)
let mult x y = x * y

val fold_example1 : unit -> Fact unit 
      (ensures (fold mult [1;2;3;4] 1 == 24))
let fold_example1 () = ()

(* CH: This also completely blows up because of the lambda
   Bound term variable not found: x
val fold_example2 : unit -> Fact unit
      (ensures (fold (fun x y -> x && y) [true;true;false;true] true == false))
let fold_example2 () = ()
*)

(* CH: Again without the lambda it works fine *)
let andb x y = x && y

val fold_example2 : unit -> Fact unit
      (ensures (fold andb [true;true;false;true] true == false))
let fold_example2 () = ()

(* CH: This fails, but maybe can't expect so much from Z3? *)
val fold_example3 : unit -> Fact unit
      (ensures (fold app  [[1];[];[2;3];[4]] [] == [1;2;3;4]))
let fold_example3 () = ()

(* Functions For Constructing Functions *)

val constfun : 'a -> 'b -> Tot 'a
let constfun x _ = x

val ftrue : 'b -> Tot bool
(* This should work, but it doesn't: arrow mismatch
let ftrue = constfun true
*)
let ftrue _ = true

(* CH: This causes syntax error at character 12, is override a keyword?
val override : ('a -> Tot 'b) -> 'a -> 'b -> 'a -> Tot 'b
*)

val my_override : ('a -> Tot 'b) -> 'a -> 'b -> 'a -> Tot 'b
let my_override f k x k' = if k = k' then x else f k'

val fmostlytrue : int -> Tot bool
let fmostlytrue = my_override (my_override ftrue 1 false) 3 false

(* CH: these fail, too higher order? *)
val override_example1 : unit -> Fact unit
      (ensures (fmostlytrue 0 == true))
let override_example1 () = ()

val override_example2 : unit -> Fact unit
      (ensures (fmostlytrue 1 == false))
let override_example2 () = ()

val override_example3 : unit -> Fact unit
      (ensures (fmostlytrue 2 == true))
let override_example3 () = ()

val override_example4 : unit -> Fact unit
      (ensures (fmostlytrue 3 == false))
let override_example4 () = ()

(* Surprisingly F* manages to prove this *)
val override_eq : x:'a -> k:'b -> f:('b->Tot 'a) -> Fact unit
      (ensures ((my_override f k x) k == x))
let override_eq x k f = ()

