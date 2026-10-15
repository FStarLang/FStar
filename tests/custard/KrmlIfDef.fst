module KrmlIfDef

module I32 = FStar.Int32

/// A [@@CIfDef] flag through the karamel backend.
///
/// Custard had no such flag at all, so the attribute was dropped and the
/// constant survived into C as a variable: karamel declared it [extern] and
/// read it, and the link failed, because a compile-time flag is a macro the
/// target defines or does not define and never an object with an address.
///
/// The flag is deliberately left undefined here, so that the [#else] branch
/// is the one that runs and the test needs nothing on the compiler's command
/// line.  Linking and running is the assertion: without the flag karamel
/// emits a read of an undeclared symbol instead of a [#if].

[@@CIfDef]
assume val krml_ifdef_flag : bool

let main () : I32.t = if krml_ifdef_flag then 1l else 0l
