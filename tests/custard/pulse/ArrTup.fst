(* Section 93.  A Pulse array in binder position is a pointer, because the
   built-in rule fires on the name [Pulse.Lib.Array.Core.array].  As a
   monomorphization argument the name was gone before anything asked: both
   reductions unfold delta-constants, [array] unfolds to the record [array'],
   and [array']'s [core_pcm_ref] has no C representation -- so the same array
   that compiles as a parameter was rejected by error 368 as a tuple
   component.

   Kuiper's shared-memory descriptors are a type-level fold that builds a
   nested tuple of arrays by construction, so this is not a shape that can be
   written around; [three] is that shape at the depth their epilogue reads.
   [id_arr] is the control that passed throughout; it is an identity and is
   inlined away, so what pins the binder position is [get_arr]'s *result*
   type, which is the same array reaching the same emitter as a pointer. *)
module ArrTup
module A = Pulse.Lib.Array
module U32 = FStar.UInt32

let id_arr (a : A.array U32.t) : A.array U32.t = a

let get_arr (p : A.array U32.t & unit) : A.array U32.t = fst p

let get_snd (p : unit & A.array U32.t) : A.array U32.t = snd p

(* The depth Kuiper reaches: an array projected out of the tail of a nested
   tuple, which is what a fold over a three-element descriptor list builds. *)
let three (p : A.array U32.t & (A.array U32.t & A.array U32.t))
  : A.array U32.t = snd (snd p)

let main () : FStar.All.ML FStar.Int32.t =
  let a = id_arr (A.null #U32.t) in
  let b = get_arr (a, ()) in
  let c = get_snd ((), b) in
  let d = three (c, (c, c)) in
  if A.is_null d then 0l else 1l
