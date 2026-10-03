module RustSplit
module U32 = FStar.UInt32
module I32 = FStar.Int32
module L = RustSplitLib
module I = RustSplitIface
open FStar.All

/// Section 65.  [--custard_split] on the karamel backends.
///
/// EverParse's shipped crate layout is *specified*, in karamel [-bundle
/// ...[rename=]] clauses over F* module names, and it could not be expressed
/// at all: Custard's [.krml] held one module called [Custard], so every one of
/// those clauses failed with "one of these modules doesn't exist".  The
/// program here is small, but it is the shape that was impossible -- two
/// modules, each bundled and renamed separately, with a reference across the
/// boundary.
///
/// The cross-module call is what the leg is really about.  A single flattened
/// module would still compile and still run; what it would not do is produce a
/// [crate::] path, which is how the generated code in [src/cose/rust/src]
/// reaches both its own other modules and the hand-written [mod ed25519]
/// beside them.  So the grep is for the qualified reference and not for the
/// answer.
///
/// Run with [-fkeep-tuples], because that is what the EverParse Rust build
/// requires, and because without it karamel monomorphizes [dtuple2] away
/// before the collision of section 65.1 can happen.

let main () : ML I32.t =
  let p = L.pair 3ul in
  let s = L.second p in
  (* Section 75.4: an interface-only module, inlined away, still has to
     survive as an empty karamel module for the bundle clause below. *)
  let s = I.bump (I.bump s) in
  if U32.eq s 6ul then 0l else 1l
