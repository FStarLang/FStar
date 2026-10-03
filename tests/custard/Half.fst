module Half

open FStar.All
open FStar.Attributes

module U32 = FStar.UInt32
module F32 = FStar.Float32

(* Section 40.  Custard has [Float32] and [Float64] and no [Float16], and
   the reason is that the missing half is not the IR: it is a ulib module to
   extract from and a C spelling to extract to, and both of those are facts
   about a target rather than about F*.

   Which means a program that has a target can supply both itself, today,
   with no compiler change.  This is that program written against the shape
   of nvcc's <cuda_fp16.h> and <cuda_bf16.h>: an opaque type, arithmetic that
   is functions rather than operators (which is what CUDA C offers -- the
   operator overloads are C++), and conversions to and from [float].
   Half_stubs.h stands in for the CUDA headers so that the test compiles with
   a plain C compiler; nothing on the F* side would differ. *)

[@@custard_extern "__half"; custard_c_header "Half_stubs.h"]
assume val half : Type0

[@@custard_extern "__nv_bfloat16"; custard_c_header "Half_stubs.h"]
assume val bfloat16 : Type0

[@@custard_extern "__float2half"; custard_c_header "Half_stubs.h"]
assume val of_f32 (x:F32.t) : half

[@@custard_extern "__half2float"; custard_c_header "Half_stubs.h"]
assume val to_f32 (x:half) : F32.t

[@@custard_extern "__hadd"; custard_c_header "Half_stubs.h"]
assume val hadd (x y : half) : half

[@@custard_extern "__hmul"; custard_c_header "Half_stubs.h"]
assume val hmul (x y : half) : half

[@@custard_extern "__hlt"; custard_c_header "Half_stubs.h"]
assume val hlt (x y : half) : bool

[@@custard_extern "__float2bfloat16"; custard_c_header "Half_stubs.h"]
assume val of_f32_bf (x:F32.t) : bfloat16

[@@custard_extern "__bfloat162float"; custard_c_header "Half_stubs.h"]
assume val to_f32_bf (x:bfloat16) : F32.t

[@@custard_extern "__hadd_bf"; custard_c_header "Half_stubs.h"]
assume val hadd_bf (x y : bfloat16) : bfloat16

(* The half types are ordinary F* types here, so everything the pipeline does
   to a type it does to these: they go through a polymorphic function, which
   monomorphization specializes, and they sit in a record, which the layout
   analysis lays out. *)
let twice (#a:Type) (add : a -> a -> a) (x : a) : a = add x x

noeq type pair = { p_h : half; p_b : bfloat16 }

let step (p : pair) : pair =
  { p_h = twice hadd p.p_h; p_b = twice hadd_bf p.p_b }

let main () : ML U32.t =
  let h = of_f32 (F32.of_literal "1.5") in
  let b = of_f32_bf (F32.of_literal "0.5") in
  let p = step { p_h = h; p_b = b } in
  (* 1.5 + 1.5 = 3.0 and 0.5 + 0.5 = 1.0, both exact at either precision. *)
  let ok1 = F32.ieee_eq (to_f32 p.p_h) (F32.of_literal "3.0") in
  let ok2 = F32.ieee_eq (to_f32_bf p.p_b) (F32.of_literal "1.0") in
  let ok3 = hlt h (hmul h (of_f32 (F32.of_literal "2.0"))) in
  if ok1 && ok2 && ok3 then 0ul else 1ul
