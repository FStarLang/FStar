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

(* This doesn't work *)
val test_next_weekday : unit -> Fact unit
      (ensures ((next_weekday (next_weekday Saturday)) == Tuesday))
let test_next_weekday () = ()

(* Booleans *)

type bool =
  | True
  | False

val negb : bool -> Tot bool
let negb b =
  match b with
  | True -> False
  | False -> True

val andb : bool -> bool -> Tot bool
let andb b1 b2 =
  match b1 with
  | True -> b2
  | False -> False

val orb : bool -> bool -> Tot bool
let orb b1 b2 =
  match b1 with
  | True -> True
  | False -> b2

(* This doesn't work *)
val test_orb1 : unit -> Fact unit
      (ensures ((orb True False) == True))
let test_orb1 () = ()

(* This doesn't work *)
val test_orb2 : unit -> Fact unit
      (ensures ((orb False False) == False))
let test_orb2 () = ()

(* This doesn't work *)
val test_orb3 : unit -> Fact unit
      (ensures ((orb False True) == True))
let test_orb3 () = ()

(* This doesn't work *)
val test_orb4 : unit -> Fact unit
      (ensures ((orb True True) == True))
let test_orb4 () = ()

(* Numbers *)

type nat =
  | O : nat
  | S : nat -> nat

val pred : nat -> Tot nat
let pred n =
  match n with
    | O -> O
    | S n' -> n'

val minustwo : nat -> Tot nat
let minustwo n =
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

val oddb : nat -> Tot bool
let oddb n = negb (evenb n)

(* This doesn't work *)
val test_oddb1 : unit -> Fact unit
      (ensures ((oddb (S O)) == True))
let test_oddb1 () = ()

(* This doesn't work *)
val test_oddb2 : unit -> Fact unit
      (ensures ((oddb (S (S (S (S O))))) == True))
let test_oddb2 () = ()

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

(* This does work, WTF? *)
val test_mult1 : unit -> Fact unit
      (ensures (mult (S (S (S O))) (S (S (S O))))
                == (S (S (S (S (S (S (S (S (S O))))))))))
let test_mult1 () = ()

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

(* Proof by Case Analysis *)

(* This doesn't work *)
val plus_1_neq_0 : n : nat -> Fact unit
      (ensures (beq_nat (plus n (S O)) O == False))
let plus_1_neq_0 n =
  match n with
  | O -> ()
  | S n' -> ()

(* This doesn't work *)
val negb_involutive : b : bool -> Fact unit
    (ensures (negb (negb b) == b))
let negb_involutive b =
  match b with
  | True -> ()
  | False -> ()
