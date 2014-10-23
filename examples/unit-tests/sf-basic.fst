(*
A translation to F* of Basics.v from Software Foundations
Original name: "Basics: Functional Programming in Coq"
*)

module Basic
open Prims.PURE

(* An effect abbreviation for a lemma *)
(*ghost*) effect Fact ('res:Type) ('p:Type) = Pure 'res True (fun r => 'p)

assume val ignore: unit -> Fact unit False

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

(* The original example calls these bool, True, and False,
   and that doesn't seem to cause problems;
   I've just renamed them to be 100% sure that's not the cause
   of the troubles in this file *)
type mbool =
  | MTrue
  | MFalse

val negb : mbool -> Tot mbool
let negb b =
  match b with
  | MTrue -> MFalse
  | MFalse -> MTrue

val andb : mbool -> mbool -> Tot mbool
let andb b1 b2 =
  match b1 with
  | MTrue -> b2
  | MFalse -> MFalse

val orb : mbool -> mbool -> Tot mbool
let orb b1 b2 =
  match b1 with
  | MTrue -> MTrue
  | MFalse -> b2

(* This doesn't work *)
val test_orb1 : unit -> Fact unit
      (ensures ((orb MTrue MFalse) == MTrue))
let test_orb1 () = ()

(* This doesn't work *)
val test_orb2 : unit -> Fact unit
      (ensures ((orb MFalse MFalse) == MFalse))
let test_orb2 () = ()

(* This doesn't work *)
val test_orb3 : unit -> Fact unit
      (ensures ((orb MFalse MTrue) == MTrue))
let test_orb3 () = ()

(* This doesn't work *)
val test_orb4 : unit -> Fact unit
      (ensures ((orb MTrue MTrue) == MTrue))
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

val evenb : nat -> Tot mbool
let rec evenb n =
  match n with
  | O        -> MTrue
  | S O      -> MFalse
  | S (S n') -> evenb n'

val oddb : nat -> Tot mbool
let oddb n = negb (evenb n)

(* This doesn't work *)
val test_oddb1 : unit -> Fact unit
      (ensures ((oddb (S O)) == MTrue))
let test_oddb1 () = ()

(* This doesn't work *)
val test_oddb2 : unit -> Fact unit
      (ensures ((oddb (S (S (S (S O))))) == MTrue))
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

(* This does work, although it's much more complicated! *)
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
val beq_nat : nat -> nat -> Tot mbool
let rec beq_nat n m =
  match n with
  | O -> (match m with
         | O -> MTrue
         | S m' -> MFalse)
  | S n' -> (match m with
            | O -> MFalse
            | S m' -> beq_nat n' m')

val ble_nat : nat -> nat -> Tot mbool
let rec ble_nat n m =
  match n with
  | O -> MTrue
  | S n' ->
      match m with
      | O -> MFalse
      | S m' -> ble_nat n' m'

(* This doesn't work *)
val test_ble_nat1 : unit -> Fact unit
      (ensures (ble_nat (S (S O)) (S (S O)) == MTrue))
let test_ble_nat1 () = ()

(* This doesn't work *)
val test_ble_nat2 : unit -> Fact unit
      (ensures (ble_nat (S (S O)) (S (S (S (S O)))) == MTrue))
let test_ble_nat2 () = ()

(* This doesn't work *)
val test_ble_nat3 : unit -> Fact unit
      (ensures (ble_nat (S (S (S (S O)))) (S (S O)) == MFalse))
let test_ble_nat3 () = ()

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
      (ensures (beq_nat (plus n (S O)) O == MFalse))
let plus_1_neq_0 n =
  match n with
  | O -> ()
  | S n' -> ()

(* This doesn't work *)
val negb_involutive : b : mbool -> Fact unit
      (ensures (negb (negb b) == b))
let negb_involutive b =
  match b with
  | MTrue -> ()
  | MFalse -> ()

(* Proof by Induction (Induction.v) *)

val plus_0_r : n : nat -> Fact unit
      (ensures (plus n O == n))
let rec plus_0_r n =
  match n with
  | O -> ()
  | S n' -> plus_0_r n'

val plus_n_Sm : n : nat -> m : nat -> Fact unit
    (ensures (S (plus n m) == plus n (S m)))
let rec plus_n_Sm n m =
  match n with
  | O -> ()
  | S n' -> plus_n_Sm n' m

(* this one uses previous lemma -- needs to be explicit it seems *)
val plus_comm : n : nat -> m : nat -> Fact unit
      (ensures (plus n m == plus m n))
let rec plus_comm n m =
  match n with
  | O -> plus_0_r m
  | S n' -> plus_comm n' m; plus_n_Sm m n'

(* this one uses previous lemma -- needs to be explicit it seems *)
val plus_rearrange : n : nat -> m : nat -> p : nat -> q : nat -> Fact unit
      (ensures (plus (plus n m) (plus p q) == plus (plus m n) (plus p q)))
let rec plus_rearrange n m p q =
  plus_comm n m
