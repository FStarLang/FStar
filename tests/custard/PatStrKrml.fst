module PatStrKrml

module U32 = FStar.UInt32

/// Section 44.1.  The same match as [PatStr.classify], pointed at the karamel
/// backend, which has no pattern node that can hold a string constant.
///
/// It used to translate the two constant patterns into fresh *variable*
/// patterns.  A variable pattern matches everything, so the first branch
/// swallowed the scrutinee, the other two were dead, and [classify] became the
/// constant 1 with no diagnostic at all.  A construct the backend cannot hold
/// has to stop the extraction; the alternative is not a worse translation, it
/// is a different program.

let classify (s : string) : U32.t =
  match s with
  | "a" -> 1ul
  | "b" -> 2ul
  | _ -> 3ul

let main () : U32.t = classify "a"
