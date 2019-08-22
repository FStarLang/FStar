module Test.Pointer

module Ptr =  Steel.Pointer
module P = LowStar.Permissions
module U32 = FStar.UInt32

open Steel.RST
open Steel.Pointer


let basic_test_increment (p: pointer U32.t) : RST unit
  (ptr_resource p)
  (fun _ -> ptr_resource p)
  (fun h0 -> P.allows_write (get_perm p h0))
  (fun h0 _ h1 -> get_val p h1 == U32.add_mod (get_val p h0) 1ul)
  =
  let x = rst_frame
    (ptr_resource p)
    (fun _ -> ptr_resource p)
    (fun _ -> ptr_read p)
  in
  let new_x = U32.add_mod x 1ul in
  rst_frame
    (ptr_resource p)
    (fun _ -> ptr_resource p)
    ( fun _ -> ptr_write p new_x)
