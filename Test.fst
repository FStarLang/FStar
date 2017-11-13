module Test

val g : x:'a -> Tot unit
let g x = ()

let rec xxx (x:int) (y:int) :unit = g (xxx y)


//let rec foo :int -> int -> int = fun x -> let z = 3 in fun y -> x + y + z

// let rec false_elim (#a:Type) (u:unit{false}) : Tot a = false_elim ()

// let a n :nat = 1
// let f (ls:list nat) :nat =
//   let rec aux (xs:list nat) :nat = a 0
//   in
//   0

// assume type t (n:nat) :Type0
// assume val foo: #n:nat{n > 0} -> t n -> Tot unit

// let bar (k:nat) (x:t k) = if k > 0 then foo x else ()


// let rec fact (a:Type u#a) (x:nat) :nat = if x = 0 then 0 else x + fact a (x - 1)

// let foo (a:Type u#a) = assert_norm (fact a 2 = 3)

//let rec sum (a:Type) (x:nat) :Tot nat = if x = 0 then 1 else sum a (x - 1)



// assume type predicate: Type0

// assume val bar (x:int{predicate}) :Tot unit

// let foo (x:int) :Lemma (requires True) (ensures predicate) [SMTPat (bar x)] = admit ()

// let baz () :Lemma (requires True) (ensures (predicate)) = foo 0

// #set-options "--max_fuel 0 --max_ifuel 0 --initial_fuel 0 --initial_ifuel 0 --use_two_phase_tc"
// let fa_intro_lem (p:int -> Type0) (f:(x:int -> squash (p x))) :Lemma (forall (x:int). p x)
//   = FStar.Classical.forall_intro #int #p (fun x -> (f x <: Lemma (p x)))

(* This gives error in reguaring ... try with printing phase 1 message, and with --ugly
open FStar.All

let rec map (f:'a -> ML 'b) (x:list 'a) :ML (list 'b) = match x with
  | [] -> []
  | a::tl -> f a::map f tl
*)

// #set-options "--use_two_phase_tc"

// assume val req (r1:int) (r2:int) :Type0
// assume val ens (r1:int) (r2:int{req r1 r2}) :Type0

// assume val foo (r1:int) (r2:int) :Lemma (requires (req r1 r2)) (ensures (req r1 r2 /\ ens r1 r2))

// let baz () :Lemma (forall r1 r2. req r1 r2 ==> ens r1 r2) =
//   let foo' (r1:int) (r2:int) :Lemma (requires (req r1 r2)) (ensures (req r1 r2 /\ ens r1 r2)) = foo r1 r2 in
//   FStar.Classical.forall_intro_2 (fun r1 -> Classical.move_requires (foo' r1))
  
//   // let bar (r1:int) (r2:int) :Lemma (req r1 r2 ==> ens r1 r2)
//   //   = FStar.Classical.move_requires (foo' r1) r2
//   // in
//   // ()
