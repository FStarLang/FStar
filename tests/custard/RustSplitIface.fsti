module RustSplitIface
module U32 = FStar.UInt32

/// Section 75.4.  An interface-only module that contributes no declaration.
///
/// EverParse's Rust crate layout names [CBOR.Pulse.Raw.Slice] in a karamel
/// [-bundle] clause.  That module has a [.fsti] and no [.fst], so nothing in
/// it is compiled; karamel's own input still holds an empty module of that
/// name, because F*'s ML extraction writes one file per module it extracted,
/// and the bundle clause was written against that.  Custard used to drop the
/// module, and karamel then rejected the *whole* bundle -- "one of these
/// modules doesn't exist" is fatal, not an empty selection.
///
/// [inline_for_extraction] is what makes it contribute nothing: the body is
/// substituted at the use site, so no declaration carries this module's name.

inline_for_extraction
let bump (x:U32.t) : U32.t = U32.logxor x 5ul
