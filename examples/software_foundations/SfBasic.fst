(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
(*
A translation to F* of Basics.v from Software Foundations
Original name: "Basics: Functional Programming in Coq"
*)

module SfBasic

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

val test_next_weekday : unit -> Lemma
      (ensures ((next_weekday (next_weekday Saturday)) = Tuesday))
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

val test_orb1 : unit -> Lemma
      (ensures ((orb MTrue MFalse) = MTrue))
let test_orb1 () = ()

val test_orb2 : unit -> Lemma
      (ensures ((orb MFalse MFalse) = MFalse))
let test_orb2 () = ()

val test_orb3 : unit -> Lemma
      (ensures ((orb MFalse MTrue) = MTrue))
let test_orb3 () = ()

val test_orb4 : unit -> Lemma
      (ensures ((orb MTrue MTrue) = MTrue))
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

val test_oddb1 : unit -> Lemma
      (ensures ((oddb (S O)) = MTrue))
let test_oddb1 () = ()

val test_oddb2 : unit -> Lemma
      (ensures (oddb (S (S (S (S O)))) = MFalse))
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

val test_mult1 : unit -> Lemma
      (ensures (mult (S (S (S O))) (S (S (S O))))
                = (S (S (S (S (S (S (S (S (S O))))))))))
let test_mult1 () = ()

val minus : nat -> nat -> Tot nat
let rec minus (n : nat) (m : nat) : nat =
  match n, m with
  | O   , _    -> O
  | S _ , O    -> n
  | S n', S m' -> minus n' m'

val beq_nat : nat -> nat -> Tot mbool
let rec beq_nat n m =
  match n, m with
  | O   , O    -> MTrue
  | S n', S m' -> beq_nat n' m'
  | _   , _    -> MFalse

val ble_nat : nat -> nat -> Tot mbool
let rec ble_nat n m =
  match n, m with
  | O   , _    -> MTrue
  | S n', O    -> MFalse
  | S n', S m' -> ble_nat n' m'

val test_ble_nat1 : unit -> Lemma
      (ensures (ble_nat (S (S O)) (S (S O)) = MTrue))
let test_ble_nat1 () = ()

val test_ble_nat2 : unit -> Lemma
      (ensures (ble_nat (S (S O)) (S (S (S (S O)))) = MTrue))
let test_ble_nat2 () = ()

val test_ble_nat3 : unit -> Lemma
      (ensures (ble_nat (S (S (S (S O)))) (S (S O)) = MFalse))
let test_ble_nat3 () = ()

(* Proof by Simplification *)

val plus_O_n : n : nat -> Lemma
      (ensures (plus O n = n))
let plus_O_n n = ()

(* Proof by Rewriting *)

val plus_id_example : n : nat -> m : nat -> Pure unit
      (requires (n == m))
      (ensures (fun r -> (plus n n = plus m m)))
let plus_id_example n m = ()

val mult_0_plus : n : nat -> m : nat -> Lemma
      (ensures ((mult (plus O n) m) = mult n m))
let mult_0_plus n m = ()

(* Proof by Case Analysis *)
val plus_1_neq_0 : n : nat -> Lemma
      (ensures (beq_nat (plus n (S O)) O = MFalse))
let plus_1_neq_0 n = ()

val negb_involutive : b : mbool -> Lemma
      (ensures (negb (negb b) = b))
let negb_involutive b = ()

(* Proof by Induction (Induction.v) *)
val plus_0_r : n : nat -> Lemma
      (ensures (plus n O = n))
let rec plus_0_r n =
  match n with
  | O -> ()
  | S n' -> plus_0_r n'

val plus_n_Sm : n : nat -> m : nat -> Lemma
    (ensures (S (plus n m) = plus n (S m)))
let rec plus_n_Sm n m =
  match n with
  | O -> ()
  | S n' -> plus_n_Sm n' m

(* this one uses previous lemma -- needs to be explicit it seems *)
val plus_comm : n : nat -> m : nat -> Lemma
      (ensures (plus n m = plus m n))
let rec plus_comm n m =
  match n with
  | O -> plus_0_r m
  | S n' -> plus_comm n' m; plus_n_Sm m n'

(* this one uses previous lemma -- needs to be explicit it seems *)
val plus_rearrange : n : nat -> m : nat -> p : nat -> q : nat -> Lemma
      (ensures (plus (plus n m) (plus p q) = plus (plus m n) (plus p q)))
let plus_rearrange n m p q = plus_comm n m
