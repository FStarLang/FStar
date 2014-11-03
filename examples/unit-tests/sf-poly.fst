
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
      (ensures (length [1;2] = 2))
let test_length1 () = ()

val test_length2 : unit -> Fact unit
      (ensures (length [true] = 1))
let test_length2 () = ()

val app : list 'a -> list 'a -> Tot (list 'a)
let rec app l1 l2 =
  match l1 with
  | []   -> l2
  | h::t -> h :: app t l2

val nil_app : l : list 'a -> Fact unit
      (ensures (app [] l = l))
let nil_app l = ()

val app_nil : l : list 'a -> Fact unit
      (ensures (app l [] = l))
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
      (ensures (snoc (app l1 l2) a = app l1 (snoc l2 a)))
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
      (ensures (rev (snoc l a) = a :: (rev l)))
let rec rev_snoc a l =
  match l with
  | []   -> ()
  | h::t -> rev_snoc a t

val rev_involutive : l:list 'a -> Fact unit
      (ensures (rev (rev l)) = l)
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

val test_index_option1 : unit -> Fact unit
      (ensures (index_option [4;5;6;7] 0 = Some 4))
let test_index_option1 () = ()

val test_index_option2 : unit -> Fact unit
      (ensures (index_option [[1];[2]] 1 = Some [2]))
let test_index_option2 () = ()

val test_index_option3 : unit -> Fact unit
      (ensures (index_option [true] 2 = None))
let test_index_option3 () = ()

assume val impossible : u : unit { False } -> Tot 'a
(* let impossible = failwith "this won't happen"
This blows up
Name not found: failwith
   at Microsoft.FStar.ToSMT.Encode.lookup_lid(env_t env, LongIdent a) in E:\Proj
   ects\fstar\pub\src\tosmt\encode.fs:line 169
Filed as https://github.com/FStarLang/FStar/issues/16 *)

val length_nil : unit -> Fact unit
      (ensures (length [] = 0))
let length_nil () = ()

val index : l : list 'a -> n:int{(0 <= n) /\ (n < length l)} -> Tot 'a
let rec index l n =
  match l with
  | [] -> length_nil(); impossible()
  | h :: t -> if n = 0 then h else index t (n-1)

(* Functions as Data *)

(* NS: Unannotated let recs have the ALL effect. To get the Tot effect, you must request it (enabling the termination checker).
   NS: BTW, the default function type has ML effect, so if not annotated, test will be in ML, and so the whole thing will be ALL. 
   NS: An alternative may be to have some other syntax, like fix instead let rec, to locally change the default function effect to Tot. *)

(* Currying *)

(* NS: Currying in F* is explicit. 

       If you intend to reason logically about partial applications of
       terms, then you should make currying explicit in types and mark
       each partially applied arrow with an effect (possibly Tot) in
       its co-domain.
       
       However, the notation for function application doesn't 
       distinguish between partial and full applications. 

       OTOH, currently, the notation for introducing functions that
       are explicitly curried is currently horribly explicit.
       Hence the weird definitions for prod_curry/prod_uncurry.
       I will change this shortly (related to the other
       bugs on matching val-declarations with the corresponding
       definitions).
 *)
val prod_curry : (('a * 'b) -> Tot 'c) -> Tot ('a -> 'b -> Tot 'c)
let prod_curry f =
  let z = () in  (* NS TODO: fix ugly syntax *)
  fun x y -> f (x,y) 

val prod_uncurry : ('a -> 'b -> Tot 'c) -> Tot (('a * 'b) -> Tot 'c)
let prod_uncurry f = 
  let z = () in (* NS TODO: fix ugly syntax *)
  fun xy -> f (fst xy) (snd xy)

val test_prod_curry: f:('a->'b->Tot 'c) -> x:'a -> y:'b -> Fact unit
      (ensures ((prod_uncurry f) (x, y) = f x y))
let test_prod_curry f x y = ()

val test_prod_uncurry: f:(('a * 'b)->Tot 'c) -> x:'a -> y:'b -> Fact unit
      (ensures ((prod_curry f) x y = f (x, y)))
let test_prod_uncurry f x y = ()

val uncurry_curry : f:('a->'b->Tot 'c) -> x:'a -> y:'b -> Fact unit
      (ensures (prod_curry (prod_uncurry f) x y = f x y))
let uncurry_curry f x y = ()

val curry_uncurry : f:(('a*'b)->Tot 'c) -> xy:('a*'b) -> Fact unit
      (ensures (prod_uncurry (prod_curry f) xy = f xy))
let curry_uncurry f xy = ()

(* Filter *)

val filter : test:('a->Tot bool) -> l:(list 'a) -> Tot (list 'a)
let rec filter test l =
  match l with
  | []     -> []
  | h :: t -> if test h then h :: (filter test t)
                        else       filter test t

val evenb : nat -> Tot bool
let evenb i = i%2 = 0

(* NS: Note: induction over non-inductive types like int *)
(*     doesn't generate good patterns for the solver *)
(* let rec evenb i = *)
(*   match i with *)
(*   | 0 -> true *)
(*   | 1 -> false *)
(*   | _ -> evenb (i-2) *)

val oddb : nat -> Tot bool
let oddb n = not (evenb n)

val test_filter1 : unit -> Fact unit
      (ensures (filter evenb [1;2;3;4] = [2;4]))
let test_filter1 () = ()

(* Map *)

val map : ('a->Tot 'b) -> (list 'a) -> Tot (list 'b)
let rec map f l =
  match l with
  | []     -> []
  | h :: t -> (f h) :: (map f t)

val test_map1 : unit -> Fact unit
      (ensures (map (fun n -> n + 3) [2;0;2] = [5;3;5]))
let test_map1 () = ()

val test_map2 : unit -> Fact unit
      (ensures (map oddb [2;1;2;5] = [false;true;false;true]))
let test_map2 () = ()

(* This shouldn't blow up, although I'm using the wrong kind of arrow for fun:
unknown(0,0-0,0) : Error
Identifier not found: [Prims.Cons] (Possible clash with related name at ../../lib/prims.fst(477,0-481,6))
val test_map3 : unit -> Fact unit
    (ensures (map (fun n => [evenb n;oddb n]) [2;1;2;5]
              = [[true;false];[false;true];[true;false];[false;true]]))
*)

(* F* can't prove this, but it's indeed a bit complex *)
(* NS: Oh yes, it can! *)
val test_map3 : unit -> Fact unit
    (ensures (map (fun n -> [evenb n;oddb n]) [2;1;2;5]
              = [[true;false];[false;true];[true;false];[false;true]]))
let test_map3 () = ()

val map_snoc : f:('a->Tot 'b) -> x:'a -> l:list 'a -> Fact unit
      (ensures (map f (snoc l x) = snoc (map f l) (f x)))
let rec map_snoc f x l =
  match l with
  | [] -> ()
  | h::t -> map_snoc f x t

val map_rev : f:('a->Tot 'b) -> l:(list 'a) -> Fact unit
      (ensures (map f (rev l) = rev (map f l)))
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

val fold_example1 : unit -> Fact unit 
      (ensures (fold (fun x y -> x * y) [1;2;3;4] 1 = 24))
let fold_example1 () = ()

val fold_example2 : unit -> Fact unit
      (ensures (fold (fun x y -> x && y) [true;true;false;true] true = false))
let fold_example2 () = ()

(* CH: This fails, but maybe can't expect so much from Z3? *)
(* NS: Oh yes, you can! : ) *)
val fold_example3 : unit -> Fact unit
      (ensures (fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4]))
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

(* CH: This causes syntax error at character 12, is override a
   keyword?  

   NS: Yes, override is a keyword. Only because it is a keyword in F#,
   and since we (plan to) codegen to F# and Caml, unless we mangle
   names, we inherit their keywords.

val override : ('a -> Tot 'b) -> 'a -> 'b -> 'a -> Tot 'b
 *)

val my_override : ('a -> Tot 'b) -> 'a -> 'b -> Tot ('a -> Tot 'b)
let my_override f k x = 
  let z = () in  (* NS: TODO, fix ugly syntax *)
  fun k' -> if k = k' then x else f k'

val fmostlytrue : int -> Tot bool
let fmostlytrue x = my_override (my_override ftrue 1 false) 3 false x

(* CH: these fail, too higher order? *)
(* NS: Not any more ... need to make currying explicit *)
val override_example1 : unit -> Fact unit
      (ensures (fmostlytrue 0 = true))
let override_example1 () = ()

val override_example2 : unit -> Fact unit
      (ensures (fmostlytrue 1 = false))
let override_example2 () = ()

val override_example3 : unit -> Fact unit
      (ensures (fmostlytrue 2 = true))
let override_example3 () = ()

val override_example4 : unit -> Fact unit
      (ensures (fmostlytrue 3 = false))
let override_example4 () = ()

(* Maybe surprisingly, F* manages to prove these *)
val override_eq : x:'a -> k:'b -> f:('b->Tot 'a) -> Fact unit
      (ensures ((my_override f k x) k = x))
let override_eq x k f = ()

val override_neq : x1:'a -> x2:'a -> k1:'b -> k2:'b -> f:('b->Tot 'a) -> Pure unit
      (requires (f k1 = x1 /\ k2 <> k1))
      (ensures \r => (my_override f k2 x2) k1 = x1)
let override_neq x1 x2 k1 k2 f = ()

(* This causes subtyping check failure without the annotation on n *)
val fold_length : l:list 'a -> Tot nat
let fold_length l = fold (fun _ (n:nat) -> n + 1) l 0

(* CH: both cases are supposed to be trivial, but none of them works *)
val fold_length_correct : l:list 'a -> Fact unit
      (ensures (fold_length l = length l))
let rec fold_length_correct l =
  match l with
  | [] -> ()
  | h::t -> fold_length_correct t

val fold_map : ('a->Tot 'b) -> list 'a -> Tot (list 'b)
let fold_map f l= fold (fun x l -> f x :: l) l []

(* CH: again, this should just work *)
val fold_map_correct : f:('a->Tot 'b) -> l:list 'a -> Fact unit
      (ensures (fold_map f l = map f l))
let rec fold_map_correct f l =
  match l with
  | [] -> ()
  | h::t -> fold_map_correct f t

(* Church numerals *)

(* Using type abbreviation here does not work, even with full annotations
   Problem seems similar to https://github.com/FStarLang/FStar/issues/15

type church 'a = ('a -> 'a) -> 'a -> 'a

val zero : church 'a
let zero ('a:Type) (f:'a->'a) (x:'a) = x

sf-poly.fst(371,0-373,3) : Error
Expected a term of type "('a:Type -> (church 'a))";
got a function "(fun 'a:Type f:('a -> 'a) x:'a -> x)"
*)

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
   NS: I don't see why this should type-check. In particular, (m n) is ill-typed. 
       Perhaps you really want higher-rank polymorphism? 
       In which case, you can write it as shown below.
   
val exp  : (('a->'a) -> 'a -> 'a) -> (('a->'a) -> 'a -> 'a) -> ('a->'a) -> 'a -> 'a
let exp n m f x = m n f x
*)

val exp : 'a:Type 
     -> n:(('a -> 'a) -> 'a -> 'a) 
     -> m:('b:Type -> 'b -> 'b)
     -> f:('a -> 'a)
     -> 'a 
     -> 'a
let exp n m f x = 
  let n' = m n in (* NS TODO: fix ugly syntax. I should just allow you to write (m n f x) *)
  n' f x


