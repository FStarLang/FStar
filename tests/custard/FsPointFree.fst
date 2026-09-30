(* FStarLang/FStar#4623, section 122.11.1.  A top-level definition with no
   value parameters, still polymorphic, whose type is a function type: F#
   generalizes it once it has a parameter, so it is eta-expanded rather than
   refused -- whether a use applies it or passes it. *)
module FsPointFree

open FStar.All

type dec (raw : Type0) (a : Type0) = raw -> option a

let bounded (#raw : Type0) (lo hi : int) (n : int) : dec raw int =
  fun _ -> if lo <= n && n <= hi then Some n else None

(* No value parameter, polymorphic in [raw], of function type. *)
let small (#raw : Type0) : dec raw int = bounded 0 10 5

let twice (#raw #a : Type0) (d : dec raw a) : dec raw a =
  fun v -> match d v with
           | Some _ -> d v
           | None -> None

let applied (#raw : Type0) (v : raw) : option int = small v
let passed (#raw : Type0) (v : raw) : option int = twice small v

let main () : ML Int32.t =
  let r1 : option int = applied "raw" in
  let r2 : option int = passed true in
  if r1 = Some 5 && r2 = Some 5 then 0l else 1l
