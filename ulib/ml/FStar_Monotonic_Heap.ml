type heap = unit

(* https://www.lexifi.com/blog/references-physical-equality *)
type 'a ref = {
  mutable contents: 'a;
  id: int
}

type ('a, 'b) mref = 'a ref
            
let emp =
  ()

(* Logical functions on heap *)
(* TODO : complete the functions to have the same interface as in FStar.Heap.fsti *)

let addr_of _ = Obj.magic ()
let is_mm _ = Obj.magic ()

(* let compare_addrs *)

type ('a, 'b, 'c, 'd) contains
type ('a, 'b) addr_unused_in
type ('a, 'b, 'c, 'd) unused_in
let fresh _ _ _ = Obj.magic ()

let sel _ _ = Obj.magic ()
let upd _ _ _ = Obj.magic ()
let alloc _ _ _ = Obj.magic ()

(* Untyped view of references *)
type aref =
   | Ref of (unit * unit)
let dummy_aref = Ref ((), ())
let aref_of _ = dummy_aref
let ref_of _ _ = Obj.magic ()
