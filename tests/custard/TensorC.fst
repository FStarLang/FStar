module TensorC

open FStar.Attributes
module U32 = FStar.UInt32

/// Section 45.  A TensorCore-shaped program: nothing but [@@custard_extern],
/// naming C symbols whose spellings are not F* identifiers.
///
/// The value targets below go through a macro so that a plain C compiler can
/// host them, but the shape is the one that matters: [TC_NS(mk_a)] is not an
/// identifier, and neither is Kuiper's [wmma::mma_sync].  Custard used to
/// [sanitize] a value target, which turned [wmma::mma_sync] into
/// [wmma__mma_sync] -- a name that does not exist.  The *type* path had always
/// printed its target verbatim, which is why [auto&] worked and the call
/// beside it did not.

[@@custard_extern "tc_auto_ref"; custard_c_header "TensorC_stubs.h"]
assume val frag : Type0

[@@custard_extern "TC_NS(mk_a)"; custard_c_header "TensorC_stubs.h"]
assume val mk_a (_ : unit) : frag

[@@custard_extern "TC_NS(mk_acc)"; custard_c_header "TensorC_stubs.h"]
assume val mk_acc (_ : unit) : frag

[@@custard_extern "TC_NS(fill)"; custard_c_header "TensorC_stubs.h"]
assume val fill (d : frag) (v : U32.t) : unit

[@@custard_extern "TC_NS(sum)"; custard_c_header "TensorC_stubs.h"]
assume val sum (a b : frag) : U32.t

/// Section 45.2.  The decoration a CUDA kernel *is*.  Custard does not read
/// the string; it goes on the definition and on its prototype, because a
/// qualifier on one and not the other is a redeclaration error rather than a
/// missing qualifier.
[@@ CPrologue "/* __global__ */"; CEpilogue "/* end kernel */";
    Comment "A kernel, decorated from source."]
let kern (_ : unit) : U32.t =
  let a = mk_a () in
  let c = mk_acc () in
  sum a c

let main () : U32.t =
  let a = mk_a () in
  let b = mk_a () in
  if not (U32.eq (sum a b) 32ul) then 1ul
  else if not (U32.eq (kern ()) 0ul) then 2ul
  else 0ul
