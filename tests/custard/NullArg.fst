(* Section 82.  [nil] has one nullary constructor, so Custard erases it to
   [unit] (section 5.5).  A value of it that the source let-bound therefore
   reaches a call as a unit-typed *variable*:

     let res1: unit = NullArg.parse_nil c in NullArg.nil_right res1

   karamel's Rust backend reads a call whose entire argument list is one
   [TUnit] as a call to a nullary function, drops the argument, and asserts it
   was the literal [()] -- which holds for F*'s own extraction, because that
   keeps [nil] as a one-variant enum.  Custard now passes [()].

   The bodies are written so that neither definition is inlined away: the
   point is a call that survives to the backend. *)
module NullArg
module U = FStar.UInt32

type nil = | Mknil0

let nil_right (x1: nil) : nil = match x1 with | Mknil0 -> Mknil0

let parse_nil (c: U.t) : nil = if U.gt c 3ul then Mknil0 else Mknil0

let parse_null (c: U.t) : nil =
  let res1 = parse_nil c in
  nil_right res1

let main () : FStar.All.ML FStar.Int32.t =
  let _ = parse_null 3ul in 0l
