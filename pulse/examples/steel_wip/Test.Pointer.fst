module Test.Pointer

open Steel.RST
open Steel.Pointer
module P = LowStar.Permissions
module U32 = FStar.UInt32

[@expect_failure]
let basic_test_increment (p: pointer U32.t) : RST unit
  (ptr_resource p)
  (fun _ -> ptr_resource p)
  (fun _ -> True)
  (fun h0 _ h1 -> get p h1 == U32.add_mod (get p h0) 1ul)
  =
  let x = rst_frame
    (ptr_resource p)
    (fun _ -> ptr_resource p)
    (fun _ -> ptr_read p)
  in
  rst_frame
    (ptr_resource p)
    (fun _ -> ptr_resource p)
    (fun _ -> ptr_write p (U32.add_mod x 1ul))
