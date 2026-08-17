module StrictDuplicate
#set-options "--warn_error +362"
open StrictInt
open StrictBool

(* One occurrence in the source should produce one report, however many
   times the elaborator happens to visit it.

   Elaboration duplicates terms for several unrelated reasons, and each
   copy carries the range of the single occurrence it came from. Each
   definition below exercises one such reason; if reporting were driven by
   visits rather than by occurrences, each would report between two and
   five times.

   362 is demoted to a warning here so that the run continues and prints
   every report it is going to print. *)

(* The computation type of a `let rec` is lifted into the type of the
   binding and also checked with the body. *)
let rec by_let_rec_comp (n:int) : Pure int (requires (same >= 0)) (ensures (fun _ -> True)) =
  if n <= 0 then 0 else by_let_rec_comp (n - 1)

(* The body of a branch is elaborated once per or-pattern disjunct. *)
let by_or_pattern (x:option int) : int =
  match x with
  | None
  | Some 0 -> same
  | Some n -> n

type r = { fld : int }

(* The head of a record update is visited more than once while the fields
   are being resolved. *)
let by_record_update (x:r) : r = { x with fld = same }
