module LitF32

module F32 = FStar.Float32
module I32 = FStar.Int32

/// Section 43.3.  A binary32 literal must reach the target as a binary32
/// literal, not as a binary64 one with a cast in front of it.
///
/// [tricky] is the correctly-rounded binary32 nearest to 7.038531e-26, which
/// is 0x15ae43fd.  Round that decimal to binary64 first and then to binary32
/// and you land on 0x15ae43fe instead -- one ulp away, silently.  [exact] is
/// the full decimal expansion of 0x15ae43fd, which binary64 holds exactly, so
/// it survives either route and can say which one [tricky] took.

let tricky : F32.t = F32.of_literal "7.038531e-26"

let exact : F32.t =
  F32.of_literal
    "7.038530691851209120859188017140306974105991300039164570989669300615787506103515625e-26"

let main () : I32.t = if F32.ieee_eq tricky exact then 0l else 1l
