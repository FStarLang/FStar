(* Section 85.  [frag]'s target spelling is a template, so its argument is
   written into a template-id and has to be a constant.  Nothing was making
   [g_gemm]'s [tm] one: rule 4b covers a type-carrying binder and rule 4c a
   [@@custard_compile_time] application, and a size index consumed by a
   template was neither.  So [tm] classified [Poly], stayed a runtime
   parameter, and error 390 fired on a definition every call site of which
   passes a literal.

   Two of the three places rule 4d has to look are here.  [tm] occurs in
   [g_gemm]'s own binder sorts, and [fill]'s [#tm] occurs in *its* binder
   sorts -- and [fill] is an [assume val], which has no body for rule 4c to
   read and used to be classified without any demand at all.

   [fill]'s [#tm] being [Mono] is also what section 85.3 is about: an
   external may not have a monomorphized value binder, because the argument
   would be substituted into a body that does not exist.  A template index is
   the exception, for the reason that rule already grants a type argument --
   it goes into the signature, and [wm::frag<16>] does say 16. *)
module TmplMono
module SZ = FStar.SizeT

[@@custard_extern "wm::frag<{0}>"; custard_c_header "TmplMono_stubs.h"]
assume val frag (tm: SZ.t) : Type0

(* Deduced from its argument on the target side, so it needs no template-id
   of its own. *)
[@@custard_extern "wm::fill"; custard_c_header "TmplMono_stubs.h"]
assume val fill (#tm: SZ.t) (f: frag tm) (v: SZ.t) : FStar.All.ML unit

(* Not indexed: C++ cannot deduce a template argument from a return type, so
   a factory is written per size.  Nothing here is under test. *)
[@@custard_extern "wm::mk16"; custard_c_header "TmplMono_stubs.h"]
assume val mk16 (seed: SZ.t) : FStar.All.ML (frag 16sz)

let g_gemm (tm: SZ.t) (f: frag tm) (rows: SZ.t) : FStar.All.ML unit =
  fill f rows

let dispatch (rows: SZ.t) : FStar.All.ML unit =
  let f = mk16 rows in
  g_gemm 16sz f rows

let main () : FStar.All.ML FStar.Int32.t = dispatch 8sz; 0l
