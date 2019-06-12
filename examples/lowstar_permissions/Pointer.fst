module Pointer


open LowStar.Resource
open LowStar.RST
open LowStar.Permissions.Pointer

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0 --z3cliopt smt.qi.eager_threshold=100"

let read_write_without_sharing () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let ptr = ptr_alloc 42ul in
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  ptr_free ptr;
  ()

let read_write_with_sharing () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let ptr = ptr_alloc 42ul in
  let x1 = ptr_read ptr in
  ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  //admit();
  let ptr1 = rst_frame
    (ptr_resource ptr)
    (fun ptr1 -> ptr_resource ptr <*> ptr_resource ptr1)
    (fun _ -> ptr_share ptr)
  in
  admit();
  let x1 =
    rst_frame
      (ptr_resource  ptr <*> ptr_resource ptr1)
      (fun _ -> ptr_resource ptr <*> ptr_resource ptr1)
      (fun _ -> ptr_read  ptr1)
  in
  //ptr_write ptr1 FStar.UInt32.(x1 +%^ 1ul);
  admit();
  ptr_merge ptr ptr1;
  ptr_free ptr;
  ()
