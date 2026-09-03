module ChrLit

/// Section 46.1.  A character constant, in expression position and in pattern
/// position.
///
/// The krml backend translated the expression to an [EAbortS] naming "the C
/// backend", which is wrong twice: the program compiled, so the message
/// arrived at *run* time (in Rust, as a panic), and the direct C backend it
/// names is the one that has always handled this.  The pattern was refused.
///
/// [FStar.Char.char] is [uint32_t] on both, which krmllib has said all along.
/// The match is deliberately not in source order: if a character pattern were
/// to fall back to a variable pattern -- the section 44.1 failure -- the first
/// branch would swallow the scrutinee and the answer would be 1, not 0.

let letter () : FStar.Char.char = 'a'

let main () : FStar.Int32.t =
  match letter () with
  | 'b' -> 1l
  | 'a' -> 0l
  | _ -> 2l
