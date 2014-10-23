(*
A translation to F* of Basics.v from Software Foundations
Original name: "Basics: Functional Programming in Coq"
*)

module Basic
open Prims.PURE

(* An effect abbreviation for a lemma *)
(*ghost*) effect Fact ('res:Type) ('p:Type) = Pure 'res True (fun r => 'p)

type day =
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday

(* test_next_weekday currently fails, and the error is more
   confusing without the val annotation *)
val next_weekday : day -> Tot day
let next_weekday d =
  match d with
  | Monday    -> Tuesday
  | Tuesday   -> Wednesday
  | Wednesday -> Thursday
  | Thursday  -> Friday
  | Friday    -> Monday
  | Saturday  -> Monday
  | Sunday    -> Monday

val test_next_weekday : unit -> Fact unit
      (ensures ((next_weekday (next_weekday Saturday)) == Tuesday))
let test_next_weekday () = ()

(* Booleans *)

type bool =
  | True
  | False

let negb (b:bool) : bool =
  match b with
  | True -> False
  | False -> True

let andb (b1:bool) (b2:bool) : bool =
  match b1 with
  | True -> b2
  | False -> False

let orb (b1:bool) (b2:bool) : bool =
  match b1 with
  | True -> True
  | False -> b2

(* Numbers *)

type nat =
  | O : nat
  | S : nat -> nat

let pred (n : nat) : nat =
  match n with
    | O -> O
    | S n' -> n'

let minustwo (n : nat) : nat =
  match n with
    | O -> O
    | S O -> O
    | S (S n') -> n'

val evenb : nat -> Tot bool
let rec evenb n =
  match n with
  | O        -> True
  | S O      -> False
  | S (S n') -> evenb n'

let oddb (n:nat) : bool = negb (evenb n)

val plus : nat -> nat -> Tot nat
let rec plus n m =
  match n with
    | O -> m
    | S n' -> S (plus n' m)

val mult : nat -> nat -> Tot nat
let rec mult n m =
  match n with
    | O -> O
    | S n' -> plus m (mult n' m)

val minus : nat -> nat -> Tot nat
let rec minus (n : nat) (m : nat) : nat =
  match n, m with
  | O   , _    -> O
  | S _ , O    -> n
  | S n', S m' -> minus n' m'

(* Without the parens around the inner matches this parses wrongly *)
val beq_nat : nat -> nat -> Tot bool
let rec beq_nat n m =
  match n with
  | O -> (match m with
         | O -> True
         | S m' -> False)
  | S n' -> (match m with
            | O -> False
            | S m' -> beq_nat n' m')

val ble_nat : nat -> nat -> Tot bool
let rec ble_nat n m =
  match n with
  | O -> True
  | S n' ->
      match m with
      | O -> False
      | S m' -> ble_nat n' m'

(* Proof by Simplification *)

val plus_O_n : n : nat -> Fact unit
      (ensures (plus O n == n))
let plus_O_n n = ()

(* Proof by Rewriting *)

val plus_id_example : n : nat -> m : nat -> Pure unit
      (requires (n == m))
      (ensures \r => (plus n n == plus m m))
let plus_id_example n m = ()

val mult_0_plus : n : nat -> m : nat -> Fact unit
      (ensures ((mult (plus O n) m) == mult n m))
let mult_0_plus n m = ()
