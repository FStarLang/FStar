module Pointer


open LowStar.Resource
open LowStar.RST
open LowStar.Permissions.Pointer

module P = LowStar.Permissions
module PR =  LowStar.Permissions.References
module RST = LowStar.RST
module R = LowStar.Resource

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
  let ptr1 = ptr_share ptr in
  let x1 =
    rst_frame
      (ptr_resource ptr1 <*> ptr_resource ptr)
      (fun _ -> ptr_resource ptr1 <*> ptr_resource ptr)
      (fun _ -> ptr_read ptr1)
  in
  let x1 =
    rst_frame
      (ptr_resource ptr <*> ptr_resource ptr1)
      #(ptr_resource ptr)
      (fun _ -> ptr_resource ptr <*> ptr_resource ptr1)
      #(fun _ -> ptr_resource ptr)
      #(ptr_resource ptr1)
      #(fun h0 -> P.allows_write (R.sel (ptr_view ptr) h0).PR.wp_perm)
      #(fun h0 _ h1 ->
         (R.sel (ptr_view ptr) h1).PR.wp_v ==  FStar.UInt32.(x1 +%^ 1ul) /\
         (R.sel (ptr_view ptr) h1).PR.wp_perm == (R.sel (ptr_view ptr) h0).PR.wp_perm
      )
      (fun _ -> ptr_write ptr FStar.UInt32.(x1 +%^ 1ul))
  in
  admit();
  rst_frame
    (ptr_resource ptr <*> ptr_resource ptr1)
    (fun _ -> ptr_resource ptr)
    (fun _ -> ptr_merge ptr ptr1);
  ptr_free ptr;
  ()
