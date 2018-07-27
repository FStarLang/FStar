module TwoPhaseTC

#set-options "--ugly"

open FStar.Classical
module PropExt = FStar.PropositionalExtensionality

#set-options "--max_fuel 0 --max_ifuel 0 --initial_fuel 0 --initial_ifuel 0"

(** Definition of a monoid *)

let right_unitality_lemma (m:Type) (u:m) (mult:m -> m -> m) =
  forall (x:m). x `mult` u == x

let conjunction_monoid :unit =
  let u : prop = singleton True in
  let mult (p q : prop) : prop = p /\ q in
  assume (forall (p:prop). p `mult` u == p);
  assert (right_unitality_lemma prop u mult) ;
  ()

(*
 * Uvar solutions are not always closed, they can have free universe names.
 * The substitution code relies on this assumption and does not substitute inside uvars.
 * This caused a breakage in the second phase (free universe names).
 * This breakage is currently masked by a normalization/compression pass between the two phases.
 * But we need a better solution.
 *)
let rec f1: a:Type u#x -> l:list u#x a -> list u#x a = fun a l -> []

(*
 * If the recursive let binding (xxx below) is added at different types to Gamma in the two phases,
 * the code below fails to typecheck. It infers the implicit in the call to g as int -> int -> Tot unit (phase 1),
 * whereas in the second phase, xxx has a type guarded by the precedes check.
 * We now add the let rec binding with precedes irrespective of lax mode
 *)
val f2 : x:'a -> Tot unit
let f2 x = ()

let rec xxx (x:int) (y:int) :unit = f2 (xxx y)

(*
 * Following are test cases for universe instantiations of let recs.
 * We now add recursive binding with universe instantiations to Gamma.
 *)
let rec false_elim (#a:Type) (u:unit{false}) : Tot a = false_elim ()

let f4 n :nat = 1
let f5 (ls:list nat) :nat =
  let rec aux (xs:list nat) :nat = f4 0
  in
  0

(* Classic dynamic context dependent implicit example *)
assume type f6 (n:nat) :Type0
assume val f7: #n:nat{n > 0} -> f6 n -> Tot unit

let f8 (k:nat) (x:f6 k) = if k > 0 then f7 x else ()

assume val f9 : int -> Type0
let f10 = x:int{f9 x}

assume val f11 : x:f10 -> squash (f9 x)

let f12 () : squash (f9 5) =
    assume (f9 5);
    f11 _

(* An assert_norm example that brought about universe issues on the recursive occurrence in the normalizer *)
let rec f13 (a:Type u#a) (x:nat) :nat = if x = 0 then 0 else x + f13 a (x - 1)

let f14 (a:Type u#a) = assert_norm (f13 a 2 = 3)

(* SMTPats are still lax checked *)
assume type f15: Type0

assume val f16 (x:int{f15}) :Tot unit

let f17 (x:int) :Lemma (requires True) (ensures f15) [SMTPat (f16 x)] = admit ()

(* We were dropping the comp from the ascription in the second phase, this testcase tests the fix *)
let f18 (p:int -> Type0) (f:(x:int -> squash (p x))) :Lemma (forall (x:int). p x)
  = FStar.Classical.forall_intro #int #p (fun (x:int) -> (FStar.Classical.give_witness_from_squash (f x) <: Lemma (p x)))

(*
 * This tests the type annotations on the dependent patterns.
 * Consider ExIntro IP hp in the function f21.
 * In the first phase, it is elaborated to: ExIntro (#uu1:Type0) (#uu2:@0 -> Type0) IP (hp:@0 IP)
 * Where @0, @1 etc. are de-bruijn variables.
 * When it is typechecked in the second phase, the annotation @0 IP for hp is typechecked
 * and the typechecker tries to prove that IP has type #uu1, which it fails to prove without any contextual information.
 * To prove it, we need the information that the scrutinee h is equal to the pattern ExIntro ... and then
 * type equalities kick in, I think.
 *)
type f19 =
  | IP : f19

noeq type f20 : a:Type0 -> (a -> Type0) -> Type u#1 =
  | ExIntro : #a:Type0 -> #p:(a -> Type0) -> x:a -> p x -> f20 a p

val f21 : f20 f19 (fun (p:f19) -> unit) -> Tot unit
  let f21 h =
  let ExIntro IP hp = h in
  ()

(*
 * #1451
 *)
let bar_1451 (#a:Type) (l1:option _) (l2:option a) = ~ (l1 === l2)

let foo_1451 () = assert (bar_1451 (Some 0) (Some true))


(* This gives error in reguaring ... try with printing phase 1 message, and with --ugly
open FStar.All

let rec map (f:'a -> ML 'b) (x:list 'a) :ML (list 'b) = match x with
  | [] -> []
  | a::tl -> f a::map f tl
*)
