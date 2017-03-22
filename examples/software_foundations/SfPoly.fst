
(*
A translation to F* of Poly.v from Software Foundations
Original name: "Polymorphism and Higher-Order Functions"
*)

(* This chapter is very boring in terms of proofs *)

module SfPoly

(* Lists, pairs, options (using the F* definitions directly) *)

val length : list 'a -> Tot nat
let rec length l =
  match l with
  | [] -> 0
  | hd::tl -> 1 + length tl

val test_length1 : unit -> Lemma
      (ensures (length [1;2] = 2))
let test_length1 () = ()

val test_length2 : unit -> Lemma
      (ensures (length [true] = 1))
let test_length2 () = ()

val length_nil : #a:Type -> unit -> Lemma
      (ensures (length #a [] = 0))
let length_nil #a () = ()

val length_cons : h:'a -> t:list 'a -> Lemma
      (ensures (length (h::t) = 1 + length t))
let length_cons h t = ()

val app : list 'a -> list 'a -> Tot (list 'a)
let rec app l1 l2 =
  match l1 with
  | []   -> l2
  | h::t -> h :: app t l2

val nil_app : l : list 'a -> Lemma
      (ensures (app [] l == l))
let nil_app l = ()

val app_nil : l : list 'a -> Lemma
      (ensures (app l [] == l))
let rec app_nil l =
  match l with
  | [] -> ()
  | h::t -> app_nil t

val length_app : l1:list 'a -> l2:list 'a -> Lemma
      (ensures (length (app l1 l2) = length l1 + length l2))
let rec length_app l1 l2 =
  match l1 with
  | [] -> ()
  | h::t -> length_app t l2

val snoc : list 'a -> 'a -> Tot (list 'a)
let rec snoc l x =
  match l with
  | []   -> [x]
  | h::t -> h :: snoc t x

val snoc_with_append : l1:list 'a -> l2:list 'a -> a:'a -> Lemma
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

val rev_snoc : a:'a -> l:list 'a -> Lemma
      (ensures (rev (snoc l a) == a :: (rev l)))
let rec rev_snoc a l =
  match l with
  | []   -> ()
  | h::t -> rev_snoc a t

val rev_involutive : l:list 'a -> Lemma
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

val test_index_option1 : unit -> Lemma
      (ensures (index_option [4;5;6;7] 0 = Some 4))
let test_index_option1 () = ()

val test_index_option2 : unit -> Lemma
      (ensures (index_option [[1];[2]] 1 = Some [2]))
let test_index_option2 () = ()

val test_index_option3 : unit -> Lemma
      (ensures (index_option [true] 2 = None))
let test_index_option3 () = ()

val index : l : list 'a -> n:int{(0 <= n) /\ (n < length l)} -> Tot 'a
let rec index l n =
  match l with
  | h :: t -> if n = 0 then h else index t (n-1)

(* Functions as Data *)

(* NS: Unannotated let recs have the ALL effect. To get the Tot effect, you must request it (enabling the termination checker).
   NS: BTW, the default function type has ML effect, so if not annotated, test will be in ML, and so the whole thing will be ALL.
   NS: An alternative may be to have some other syntax, like fix instead let rec, to locally change the default function effect to Tot. *)

(* Currying *)

(* NS: it used to be that if you intended to partially apply
       a function, then you had to indicate it as such in the type.
       Not so any more. *)
val prod_curry : (('a * 'b) -> Tot 'c) -> 'a -> 'b -> Tot 'c
let prod_curry f x y =  f (x,y)

val prod_uncurry : ('a -> 'b -> Tot 'c) -> ('a * 'b) -> Tot 'c
let prod_uncurry f xy = f (fst xy) (snd xy)

val test_prod_uncurry: f:('a->'b->Tot 'c) -> x:'a -> y:'b -> Lemma
      (ensures ((prod_uncurry f) (x, y) == f x y))
let test_prod_uncurry f x y = ()

val test_prod_curry: f:(('a * 'b)->Tot 'c) -> x:'a -> y:'b -> Lemma
      (ensures ((prod_curry f) x y == f (x, y)))
let test_prod_curry f x y = ()

val uncurry_curry : f:('a->'b->Tot 'c) -> x:'a -> y:'b -> Lemma
      (ensures (prod_curry (prod_uncurry f) x y == f x y))
let uncurry_curry f x y = ()

val curry_uncurry : f:(('a*'b)->Tot 'c) -> xy:('a*'b) -> Lemma
      (ensures (prod_uncurry (prod_curry f) xy == f xy))
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

(* NS: Note: induction over non-inductive types like int is also fine *)
val evenb' : nat -> Tot bool
let rec evenb' i =
  match i with
  | 0 -> true
  | 1 -> false
  | _ -> evenb' (i-2)

val oddb : nat -> Tot bool
let oddb n = not (evenb n)

val test_filter1 : unit -> Lemma
      (ensures (filter evenb [1;2;3;4] = [2;4]))
let test_filter1 () = ()

val test_filter2 : unit -> Lemma
      (ensures (filter evenb' [1;2;3;4] = [2;4]))
let test_filter2 () = ()

(* Map *)

val map : ('a->Tot 'b) -> (list 'a) -> Tot (list 'b)
let rec map f l =
  match l with
  | []     -> []
  | h :: t -> (f h) :: (map f t)

val test_map1 : unit -> Lemma
      (ensures (map (fun n -> n + 3) [2;0;2] = [5;3;5]))
let test_map1 () = ()

val test_map2 : unit -> Lemma
      (ensures (map oddb [2;1;2;5] = [false;true;false;true]))
let test_map2 () = ()

val test_map3 : unit -> Lemma
    (ensures (map (fun n -> [evenb n;oddb n]) [2;1;2;5]
              = [[true;false];[false;true];[true;false];[false;true]]))
let test_map3 () = ()

val map_snoc : f:('a->Tot 'b) -> x:'a -> l:list 'a -> Lemma
      (ensures (map f (snoc l x) == snoc (map f l) (f x)))
let rec map_snoc f x l =
  match l with
  | [] -> ()
  | h::t -> map_snoc f x t

val map_rev : f:('a->Tot 'b) -> l:(list 'a) -> Lemma
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

val fold_example1 : unit -> Lemma
      (ensures (let open FStar.Mul in
	        fold (fun x y -> x * y) [1;2;3;4] 1 = 24))
let fold_example1 () = ()

val fold_example2 : unit -> Lemma
      (ensures (fold (fun x y -> x && y) [true;true;false;true] true = false))
let fold_example2 () = ()

val fold_example3 : unit -> Lemma
      (ensures (fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4]))
let fold_example3 () = ()

(* Functions For Constructing Functions *)

val constfun : 'a -> 'b -> Tot 'a
let constfun x _ = x

val ftrue : 'b -> Tot bool
(* This should work, but it doesn't: causes failed postconditions later on
let ftrue = constfun true *)
let ftrue _ = true

(* CH: This causes syntax error at character 12, is override a
   keyword?

   NS: Yes, override is a keyword. Only because it is a keyword in F#,
   and since we (plan to) codegen to F# and Caml, unless we mangle
   names, we inherit their keywords.

val override : ('a -> Tot 'b) -> 'a -> 'b -> 'a -> Tot 'b
 *)

val my_override : #a:eqtype -> #b:Type -> (a -> Tot b) -> a -> b -> a -> Tot b
let my_override #a #b f k x k' = if k = k' then x else f k'

val fmostlytrue : int -> Tot bool
let fmostlytrue x = my_override (my_override ftrue 1 false) 3 false x

(* CH: these fail, too higher order? *)
(* NS: Not any more ... need to make currying explicit *)
(* CH: That's counter intuitive. I fail to see the
   difference between implicit and explicit currying.
   Isn't one just syntax sugar for the other? *)
val override_example1 : unit -> Lemma
      (ensures (fmostlytrue 0 = true))
let override_example1 () = ()

val override_example2 : unit -> Lemma
      (ensures (fmostlytrue 1 = false))
let override_example2 () = ()

val override_example3 : unit -> Lemma
      (ensures (fmostlytrue 2 = true))
let override_example3 () = ()

val override_example4 : unit -> Lemma
      (ensures (fmostlytrue 3 = false))
let override_example4 () = ()

val override_eq : #a:Type -> #b:eqtype -> x:a -> k:b -> f:(b->Tot a) -> Lemma
      (ensures ((my_override f k x) k == x))
let override_eq #a #b x k f = ()

val override_neq : #a:Type -> #b:eqtype
		 -> x1:a -> x2:a -> k1:b -> k2:b -> f:(b->Tot a) -> Pure unit
      (requires (f k1 == x1 /\ ~(k2 == k1)))
      (ensures (fun r -> (my_override f k2 x2) k1 == x1))
let override_neq #a #b x1 x2 k1 k2 f = ()

(* NS: Experimenting first with named functions *)
val plus_one: 'a -> nat -> Tot nat
let plus_one m n = n + 1

val fold_length_named : l:list 'a -> Tot nat
let fold_length_named l = fold plus_one l 0

val fold_length_named_correct : l:list 'a -> Lemma
      (ensures (fold_length_named l = length l))
let rec fold_length_named_correct l =
  match l with
  | [] -> ()
  | h::t -> fold_length_named_correct t

(* NS: But, with named functions, you have to explicitly closure-convert ...
       and the closure arguments have to be explicitly curried ... yuck *)
val fcons : ('a -> Tot 'b) -> 'a -> list 'b -> Tot (list 'b)
let fcons f x l = f x :: l

val fold_map_named : ('a->Tot 'b) -> list 'a -> Tot (list 'b)
let fold_map_named f l= fold (fcons f) l []

(* But it works *)
val fold_map_named_correct : f:('a->Tot 'b) -> l:list 'a -> Lemma
      (ensures (fold_map_named f l == map f l))
let rec fold_map_named_correct f l =
  match l with
  | [] -> ()
  | h::t -> fold_map_named_correct f t

(* NS: So, let's do better with closures this time *)
(* NS: The lambda here is relatively easy, since it has no free variables *)
val fold_length : l:list 'a -> Tot nat
let fold_length l = fold (fun _ (n:nat) -> n + 1) l 0

val fold_length_correct : l:list 'a -> Lemma
      (ensures (fold_length l = length l))
let rec fold_length_correct l =
  match l with
  | [] -> ()
  | h::t -> fold_length_correct t

(* NS: This lambda is fancier, since it captures 'f' in its environment *)
val fold_map : ('a->Tot 'b) -> list 'a -> Tot (list 'b)
let fold_map f l= fold (fun x l -> f x :: l) l []

val fold_map_correct : f:('a->Tot 'b) -> l:list 'a -> Lemma
      (ensures (fold_map f l == map f l))
let rec fold_map_correct f l =
  match l with
  | [] -> ()
  | h::t -> fold_map_correct f t

open FStar.List.Tot
val fold_right_cons_is_id: l:list 'a -> l':list 'a ->
                           Lemma (fold_right Cons l l' == (l @ l'))
let rec fold_right_cons_is_id l l' = match l with
  | []   -> ()
  | _::t -> fold_right_cons_is_id t l'

(* Church numerals *)

(* Using type abbreviation here does not work, even with full annotations
   Problem seems similar to https://github.com/FStarLang/FStar/issues/15
   and https://github.com/FStarLang/FStar/issues/23

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

let exp (#a:Type) (n:((a -> Tot a) -> Tot (a -> Tot a)))
        (m:(#b:Type -> b -> Tot b))
	(f:(a -> Tot a))
	(x:a) : Tot a =
  let n' : (a -> Tot a) -> Tot (a -> Tot a) = m n in (* NS TODO: fix ugly syntax. I should just allow you to write (m n f x) *)
  n' f x
