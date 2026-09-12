(* Section 86.  §85's [frag] is indexed by the binder itself, so the argument
   [ty_of_typ] meets after specialization is the substituted term
   [uint_to_t 16], which [const_of_arg] peels to a literal.  Here the index is
   an *application over* the binder -- [frag (SZ.v tm)] -- which is what a
   [nat]-indexed template gets when the caller's parameter is a machine
   integer, and which is how Kuiper's [wmma_fragment] is written.

   Then the argument is [SZ.v (uint_to_t 16)], the compile-time reduction
   evaluates it, and what comes back is an embedding rather than a constant.
   [show] forces the thunk and prints [16]; the constant recogniser saw a
   [Tm_lazy] and said there was no constant.  So error 390 fired on a fully
   determined index, and printed the constant it said it did not have. *)
module TmplMonoV
module SZ = FStar.SizeT

[@@custard_extern "wm::frag<{0}>"; custard_c_header "TmplMono_stubs.h"]
assume val frag (tm: nat) : Type0

[@@custard_extern "wm::fill"; custard_c_header "TmplMono_stubs.h"]
assume val fill (#tm: nat) (f: frag tm) (v: SZ.t) : FStar.All.ML unit

[@@custard_extern "wm::mk16"; custard_c_header "TmplMono_stubs.h"]
assume val mk16 (seed: SZ.t) : FStar.All.ML (frag 16)

let g_gemm (tm: SZ.t) (f: frag (SZ.v tm)) (rows: SZ.t) : FStar.All.ML unit =
  fill f rows

let dispatch (rows: SZ.t) : FStar.All.ML unit =
  let f = mk16 rows in
  g_gemm 16sz f rows

let main () : FStar.All.ML FStar.Int32.t = dispatch 8sz; 0l
