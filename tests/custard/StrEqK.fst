module StrEqK
module U32 = FStar.UInt32

/// Section 50.2.  The older half of the same hole, and the worse one.
///
/// A plain [s = t] on strings has been producing a karamel crash on the Rust
/// path for as long as Custard has had strings -- not a refusal, a crash,
/// with no diagnostic of our own.  Section 48.3's desugaring did not create
/// that; it widened its reach from [=] to [match].  Refused here at the
/// operator, which is where both halves meet.

let same (a : string) (b : string) : U32.t =
  if a = b then 1ul else 0ul

let main () : FStar.Int32.t =
  if U32.eq (same "a" "a") 1ul then 0l else 1l
