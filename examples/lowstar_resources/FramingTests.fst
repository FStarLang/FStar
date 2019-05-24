module FramingTests

open LowStar.Resource
open LowStar.RST

let frame_resolve_test1 (r1 r2:resource)
        (f:unit -> RST unit r2 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True))
      : RST unit (r2 <*> r1) (fun _ -> r1 <*> r2) (fun _ -> True) (fun _ _ _ -> True) =
  rst_frame (r2 <*> r1) (fun _ -> r1 <*> r2) f

let frame_resolve_test2 (r1 r2:resource)
        (f:unit -> RST unit r1 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True))
      : RST unit r1 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True) =
  rst_frame r1 (fun _ -> r2) f

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -LowStar.Monotonic -FStar.Monotonic.HyperHeap -FStar.Monotonic.HyperStack -FStar.Reflection -FStar.Tactics -FStar.ModifiesGen -FStar.HyperStack -FStar.Monotonic.Heap -LowStar.Buffer -FStar.Calc -LowStar.RST.reveal_star_inv' --z3cliopt smt.qi.eager_threshold=100"
let frame_resolve_test3 (r1 r2 r3 r4:resource)
        (f:unit -> RST unit (r1 <*> r2) (fun _ -> r1 <*> r2) (fun _ -> True) (fun _ _ _ -> True))
      : RST unit (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> True) (fun _ _ _ -> True) =
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f; // 5
  
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f; // 10

  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f; // 15

  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f; // 20

  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f; // 25

  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f; // 30

  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f; // 35

  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f; // 40

  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f; // 45

  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f;
  rst_frame (r1 <*> r2 <*> (r3 <*> r4)) (fun _ -> r1 <*> r2 <*> (r3 <*> r4)) f  // 50
#reset-options



(*
// next test currently fails, likely due to two-phase typechecking trying to  
// retypecheck the frame r3 <*> r4; turning two-phase off crashes F* with 
//   (Error) ASSERTION FAILURE: Bound term variable not found  r1#214553 in 
//   environment: ...,CM, x#215035, r4#215006, r3#215005, r2#215004, r1#215003, 
//   p#215015, h1#215036, h#215016, f#215007

let frame_resolve_test4 (r1 r2 r3 r4:resource)
        (f:unit -> RST unit (r1 <*> r2) (fun _ -> r1 <*> r2) (fun _ -> True) (fun _ _ _ -> True))
      : RST unit (r1 <*> r2 <*> r3 <*> r4) (fun _ -> r1 <*> r2 <*> r3 <*> r4) (fun _ -> True) (fun _ _ _ -> True) =
  rst_frame (r1 <*> r2 <*> r3 <*> r4) (fun _ -> r1 <*> r2 <*> r3 <*> r4) f
*)
