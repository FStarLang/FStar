module Test.Pointer

module Ptr =  Steel.Pointer
module P = LowStar.Permissions
module U32 = FStar.UInt32

open Steel.RST

[@expect_failure]
let basic_test_increment (p: Ptr.pointer U32.t) : RST unit
  (Ptr.ptr_resource p)
  (fun _ -> Ptr.ptr_resource p)
  (fun _ -> True)
  (fun h0 _ h1 -> Ptr.get_val p h1 == U32.add_mod (Ptr.get_val p h0) 1ul)
  =
  let x = rst_frame
    (Ptr.ptr_resource p)
    (fun _ -> Ptr.ptr_resource p)
    (fun _ -> Ptr.ptr_read p)
  in
  rst_frame
    (Ptr.ptr_resource p)
    (fun _ -> Ptr.ptr_resource p)
    (fun _ -> Ptr.ptr_write p (U32.add_mod x 1ul))
