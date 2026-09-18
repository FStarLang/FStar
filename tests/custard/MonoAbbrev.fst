module MonoAbbrev

(* Section 74.  A [Mono] binder behind a codomain abbreviation.

   [Mono.classify_def] measures the arrow spine with [arrow_formals_unfold],
   so [tile] is classified and a call site removes its argument.
   [Extract.specialize] measured it with [U.arrow_formals_comp], which stops
   at [kern_t] -- so it never reached [tile] to substitute the key into the
   body, and the binder survived into the emitted signature.  The definition
   then took one parameter more than every call supplied.

   Kuiper hit both halves of this.  [Klas.SPMM] hit the arity, as error 368
   "applied to 6 of its 7 arguments" against a signature that matched
   karamel's exactly; [Klas.GEMM.TensorCore2D.To] hit the other half, as
   error 390 over a template argument that had reduced only to
   [FStar.SizeT.v tm] because [tm] was still a variable. *)

module U32 = FStar.UInt32

inline_for_extraction noextract
let kern_t = ([@@@monomorphize] tile: U32.t) -> (x: U32.t) -> U32.t

let mk (base: U32.t) : kern_t =
  fun tile x -> U32.logxor (U32.logxor tile base) x

let go (x: U32.t) : U32.t = mk 3ul 4ul x

let main () : FStar.All.ML FStar.Int32.t =
  if go 5ul = U32.logxor (U32.logxor 4ul 3ul) 5ul then 0l else 1l
