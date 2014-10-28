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

val nil_app : l : list 'a -> Fact unit
      (ensures (app [] l == l))
let nil_app l = ()

val app_nil : l : list 'a -> Fact unit
      (ensures (app l [] == l))
let rec app_nil l =
  match l with
  | [] -> ()
  | h::t -> app_nil t

val snoc : list 'a -> 'a -> Tot (list 'a)
let rec snoc l x =
  match l with
  | []   -> [x]
  | h::t -> h :: snoc t x

val snoc_with_append : l1:list 'a -> l2:list 'a -> a:'a -> Fact unit
      (ensures (snoc (app l1 l2) a == app l1 (snoc l2 a)))
let rec snoc_with_append l1 l2 a =
  match l1 with
  | [] -> ()
  | a1 :: l1' -> snoc_with_append l1' l2 a

val rev : list 'a -> Tot (list 'a)
let rec rev l =
  match l with
  | []   -> []
  | h::t -> snoc (rev t) h

val rev_snoc : a:'a -> l:list 'a -> Fact unit
      (ensures (rev (snoc l a) == a :: (rev l)))
let rec rev_snoc a l =
  match l with
  | []   -> ()
  | h::t -> rev_snoc a t

val rev_involutive : l:list 'a -> Fact unit
      (ensures (rev (rev l)) == l)
let rec rev_involutive l =
  match l with
  | []   -> ()
  | h::t -> rev_snoc h (rev t); rev_involutive t

val repeat : 'a -> nat -> list 'a
let rec repeat a n =
  match n with
  | 0 -> []
  | _ -> a :: (repeat a (n-1))

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

(* All these fail and I think they shouldn't:
   Type "(unit -> Fact (unit))" has unexpected non-trivial pre-condition
   Filed this as: https://github.com/FStarLang/FStar/issues/18
val test_index_option1 : unit -> Fact unit
      (ensures (index_option [4;5;6;7] 0 == Some 4))
let test_index_option1 () = ()

val test_index_option2 : unit -> Fact unit
      (ensures (index_option [[1];[2]] 1 == Some [2]))
let test_index_option2 () = ()

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

(* still get same error:
   Type "(unit -> Fact (unit))" has unexpected non-trivial pre-condition
val test_index_option3' : unit -> Fact unit
      (ensures (index_option' [true] 2 == None))
let test_index_option3' () = ()
*)

assume val impossible : u : unit { False } -> Tot 'a
(* let impossible = failwith "this won't happen"
This blows up
Name not found: failwith
   at Microsoft.FStar.ToSMT.Encode.lookup_lid(env_t env, LongIdent a) in E:\Proj
   ects\fstar\pub\src\tosmt\encode.fs:line 169
Filed as https://github.com/FStarLang/FStar/issues/16 *)

(* CH: This should really work *)
val length_nil : unit -> Fact unit
      (ensures (length [] == 0))
let length_nil () = ()
(* it seems that Z3 cannot use this pattern:

; <Start encoding LengthProblems.length>
;;;;;;;;;;;;;;;;Equation: LengthProblems.length
(assert (forall ((_a___7853__1009 Type))
 (! (implies true
 (= (LengthProblems.length _a___7853__1009 (Prims.Nil _a___7853__1009))
 (BoxInt 0)))
:pattern ((LengthProblems.length _a___7853__1009 (Prims.Nil _a___7853__1009))))))

to prove the following query

; <Query>
;;;;;;;;;;;;;;;;query
(assert (not (exists ((uvar_1016 Type) (uvar_1015 Type))
 (= (LengthProblems.length uvar_1015 (Prims.Nil uvar_1016))
 (BoxInt 0)))))

removing the pattern makes this provable, but I'm not sure that's the
correct fix, what's with these 2 separate existentials in the query
anyway?  using a single common existential also makes this provable
(with the current pattern for the equation) *)

(* Getting incomplete patterns here, with or without the [] pattern,
   caused by the same problem as length_nil I think; it should clearly
   be a different error message when the [] pattern is present *)
val index : l : list 'a -> n:int{(0 <= n) /\ (n < length l)} -> Tot 'a
let rec index l n =
  match l with
(*  | [] -> length_nil(); impossible() *)
  | h :: t -> if n = 0 then h else index t (n-1)

(* Functions as Data *)

(* NS: Unannotated let recs have the ALL effect. To get the Tot effect, you must request it (enabling the termination checker).
   NS: BTW, the default function type has ML effect, so if not annotated, test will be in ML, and so the whole thing will be ALL. 
   NS: An alternative may be to have some other syntax, like fix instead let rec, to locally change the default function effect to Tot. *)

(* Currying *)

val prod_curry : (('a * 'b) -> Tot 'c) -> 'a -> 'b -> Tot 'c
let prod_curry f x y = f (x,y)

val prod_uncurry : ('a -> 'b -> Tot 'c) -> ('a * 'b) -> Tot 'c
let prod_uncurry f xy = f (fst xy) (snd xy)

(* CH: how can we help the prover prove something like this? *)
val uncurry_curry : f:('a->'b->Tot 'c) -> x:'a -> y:'b -> Fact unit
      (ensures (prod_curry (prod_uncurry f) x y == f x y))
let uncurry_curry f x y = ()

(* CH: how can we help the prover prove something like this? *)
val curry_uncurry : f:(('a*'b)->Tot 'c) -> xy:('a*'b) -> Fact unit
      (ensures (prod_uncurry (prod_curry f) xy == f xy))
let curry_uncurry f xy =
  match xy with
  | (x,y) -> ()

(* Filter *)

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
(* Working around it for now *)
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
   Filed this as: https://github.com/FStarLang/FStar/issues/20
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
(* CH: Replacing plus3 with (fun n -> n + 3) (just inlining) makes F* blow up:
   Bound term variable not found: n
   at Microsoft.FStar.ToSMT.Encode.lookup_term_var[a,b](env_t env, withinfo_t`2
   a) in E:\Projects\fstar\pub\src\tosmt\encode.fs:line 141
   Filed this as: https://github.com/FStarLang/FStar/issues/19
   *)
let test_map1 () = ()

(* CH: again: Incompatible types (list i:int{i >= 0}) and (list nat)
val test_map2 : unit -> Fact unit
      (ensures (map oddb [2;1;2;5] == [false;true;false;true]))
let test_map2 () = ()
*)

(* This shouldn't blow up, although I'm using the wrong kind of arrow for fun:
unknown(0,0-0,0) : Error
Identifier not found: [Prims.Cons] (Possible clash with related name at ../../lib/prims.fst(477,0-481,6))
val test_map3 : unit -> Fact unit
    (ensures (map (fun n => [evenb n;oddb n]) [2;1;2;5]
              == [[true;false];[false;true];[true;false];[false;true]]))
*)

(* CH: again: Incompatible types (list i:int{i >= 0}) and (list nat)
val test_map3 : unit -> Fact unit
    (ensures (map (fun n -> [evenb n;oddb n]) [2;1;2;5]
              == [[true;false];[false;true];[true;false];[false;true]]))
let test_map3 () = ()
*)

val map_snoc : f:('a->Tot 'b) -> x:'a -> l:list 'a -> Fact unit
      (ensures (map f (snoc l x) == snoc (map f l) (f x)))
let rec map_snoc f x l =
  match l with
  | [] -> ()
  | h::t -> map_snoc f x t

val map_rev : f:('a->Tot 'b) -> l:(list 'a) -> Fact unit
      (ensures (map f (rev l) == rev (map f l)))
let rec map_rev f l =
  match l with
  | [] -> ()
  | h::t -> map_snoc f h (rev t); map_rev f t

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
let mult_clos x y = x * y

val fold_example1 : unit -> Fact unit 
      (ensures (fold mult_clos [1;2;3;4] 1 == 24))
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
   Filed this as: https://github.com/FStarLang/FStar/issues/21
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

(* Maybe surprisingly, F* manages to prove these *)
val override_eq : x:'a -> k:'b -> f:('b->Tot 'a) -> Fact unit
      (ensures ((my_override f k x) k == x))
let override_eq x k f = ()

val override_neq : x1:'a -> x2:'a -> k1:'b -> k2:'b -> f:('b->Tot 'a) -> Pure unit
      (requires ((f k1 == x1) /\ (k2 =!= k1)))
      (ensures \r => (my_override f k2 x2) k1 == x1)
let override_neq x1 x2 k1 k2 f = ()

(* CH: can't inline this because support for lambdas sucks *)
val closure42 : 'a -> nat -> Tot nat
let closure42 a n = n + 1

val fold_length : l:list 'a -> Tot nat
let fold_length l = fold closure42 l 0

(* CH: both cases are supposed to be trivial, but none of them works *)
val fold_length_correct : l:list 'a -> Fact unit
      (ensures (fold_length l == length l))
let rec fold_length_correct l =
  match l with
  | [] -> ()
  | h::t -> fold_length_correct t

val closure43 : ('a->Tot 'b) -> 'a -> list 'b -> Tot (list 'b)
let closure43 f x l = f x :: l

val fold_map : ('a->Tot 'b) -> list 'a -> Tot (list 'b)
let fold_map f l= fold (closure43 f) l []

(* CH: again, this should just work *)
val fold_map_correct : f:('a->Tot 'b) -> l:list 'a -> Fact unit
      (ensures (fold_map f l == map f l))
let rec fold_map_correct f l =
  match l with
  | [] -> ()
  | h::t -> fold_map_correct f t

(* Church numerals *)

(* Q: How can I define a type abbreviation? *)

val zero : ('a->'a) -> 'a -> 'a
let zero f x = x

val one : ('a->'a) -> 'a -> 'a
let one f x = f x

val two : ('a->'a) -> 'a -> 'a
let two f x = f (f x)

val succ : (('a->'a) -> 'a -> 'a) -> ('a->'a) -> 'a -> 'a
let succ n f x = f (n f x)

val plus  : (('a->'a) -> 'a -> 'a) -> (('a->'a) -> 'a -> 'a) -> ('a->'a) -> 'a -> 'a
let plus n m f x = n f (m f x)

val mult  : (('a->'a) -> 'a -> 'a) -> (('a->'a) -> 'a -> 'a) -> ('a->'a) -> 'a -> 'a
let mult n m f x = n (m f) x

(* CH: not enough polymorphism to do this in F*?
val exp  : (('a->'a) -> 'a -> 'a) -> (('a->'a) -> 'a -> 'a) -> ('a->'a) -> 'a -> 'a
let exp n m f x = m n f x
*)
