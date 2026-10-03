module RustSplitLib
module U32 = FStar.UInt32

/// Section 65.  The lower half of the split test: a module that has to end up
/// as its own karamel file, so that the upper half's reference to it comes
/// out as a cross-crate [crate::...] path rather than as a call within one
/// flattened module.
///
/// It also holds [dtuple2], which collides with karamel's own [Prims]
/// (section 65.1): karamel's builtin spells its fields [fst] and [snd] where
/// F* spells them [_1] and [_2], and this is the declaration EverParse saw
/// karamel's checker reject.
///
/// No [list] here, though it collides the same way.  A recursive datatype
/// does not survive karamel's Rust backend at all -- the stock
/// [--codegen krml] pipeline dies on one with [Fatal error: exception
/// Not_found] -- so a test using one would be pinning that and not this.  It
/// is covered on the [KrmlC] leg by [KrmlPrims] instead; see section 65.2.

let pair (x:U32.t) : (y:U32.t & U32.t) = (| x, U32.add_mod x x |)

let second (p : (y:U32.t & U32.t)) : U32.t = dsnd p
