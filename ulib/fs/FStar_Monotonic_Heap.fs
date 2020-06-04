module FStar_Monotonic_Heap
module Obj = FSharp.Compatibility.OCaml.Obj

type heap = unit

(* Following OCaml implementation we want reference (physical) equality for ref.  
   https://www.lexifi.com/blog/references-physical-equality *)
[<ReferenceEquality>]
type 'a ref = {
  mutable contents: 'a;
  id: int
}

type 'a mref = 'a ref
            
let emp =
  ()

(* Logical functions on heap *)
(* TODO : complete the functions to have the same interface as in FStar.Heap.fsti *)

let addr_of _ = Obj.magic ()
let is_mm _ = Obj.magic ()

(* let compare_addrs *)

// HACK: We need to somehow make the implementation agree with the interface. Those types seem to be used only 
//       in lemmas, so they shouldn't matter.
type ('a, 'b, 'c, 'd) contains = 'a * 'b * 'c * 'd
type ('a, 'b) addr_unused_in = 'a * 'b
type ('a, 'b, 'c, 'd) unused_in = 'a * 'b * 'c * 'd
let fresh _ _ _ = Obj.magic ()

let sel _ _ = Obj.magic ()
let upd _ _ _ = Obj.magic ()
let alloc _ _ _ = Obj.magic ()

let free_mm _ _ = Obj.magic ()
let sel_tot = sel
let upd_tot = upd
                
(* Untyped view of references *)
type aref =
   | Ref of (unit * unit)
let dummy_aref = Ref ((), ())
let aref_of _ = dummy_aref
let ref_of _ _ = Obj.magic ()
