module Pointer

module P = LowStar.Permissions
module PR =  LowStar.Permissions.References
module PT = LowStar.Permissions.Pointer
module RST = LowStar.RST
module R = LowStar.Resource
module HST = FStar.HyperStack.ST
module MG = FStar.ModifiesGen


#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0 --z3cliopt smt.qi.eager_threshold=100"

let read_write_without_sharing () : RST.RST unit
  (R.empty_resource)
  (fun _ -> R.empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let ptr = PT.ptr_alloc 42ul in
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  PT.ptr_free ptr;
  ()

let read_write_with_sharing () : RST.RST unit
  (R.empty_resource)
  (fun _ -> R.empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let ptr = PT.ptr_alloc 42ul in
  let x1 = PT.ptr_read ptr in
  PT.ptr_write ptr FStar.UInt32.(x1 +%^ 1ul);
  let ptr1 = PT.ptr_share ptr in
  (**) let h0 = HST.get () in
  let x1 =
    RST.rst_frame
      (R.(PT.ptr_resource ptr1 <*> PT.ptr_resource ptr))
      (fun _ -> R.(PT.ptr_resource ptr <*> PT.ptr_resource ptr1))
      (fun _ ->
        PT.ptr_read ptr1
      )
  in
  let new_x1 = FStar.UInt32.(x1 +%^ 1ul) in
  (*RST.rst_frame
   (R.(PT.ptr_resource ptr1 <*> PT.ptr_resource ptr))
   (fun _ -> R.(PT.ptr_resource ptr <*> PT.ptr_resource ptr1))
   (fun _ -> PT.ptr_write ptr new_x1);*)
  RST.rst_frame
    (R.(PT.ptr_resource ptr <*> PT.ptr_resource ptr1))
    (fun _ -> PT.ptr_resource ptr)
    (fun _ -> PT.ptr_merge ptr ptr1);
  RST.rst_frame
    (PT.ptr_resource ptr)
    (fun _ -> R.empty_resource)
    (fun _ -> PT.ptr_free ptr);
  R.reveal_empty_resource ();
  RST.reveal_modifies ()
