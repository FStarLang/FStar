module KrmlExt

module I32 = FStar.Int32
module U32 = FStar.UInt32

/// Section 45.3.  An external through the karamel backend.
///
/// The [DExternal] was emitted under the [@@custard_extern] target and every
/// call site under the F* name, so the translation unit declared one symbol
/// and called another -- and neither karamel nor the C compiler had reason to
/// object, because each half was well formed on its own.  The include the
/// header attribute asks for was missing too, so even the right name would
/// not have been declared.
///
/// The test is that the result links and runs, which is the only assertion
/// that sees any of this.

[@@custard_extern "krmlext_triple"; custard_c_header "KrmlExt_stubs.h"]
assume val triple (x : U32.t) : U32.t

let main () : I32.t = if U32.eq (triple 5ul) 15ul then 0l else 1l
