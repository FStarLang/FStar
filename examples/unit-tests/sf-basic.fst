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

let next_weekday (d:day) : day =
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
