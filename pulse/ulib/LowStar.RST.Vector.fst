module LowStar.RST.Vector


open LowStar.RST
module HS = FStar.HyperStack
module A = LowStar.RST.Array
module Arr = LowStar.Array
module P = LowStar.RST.Pointer
module U32 = FStar.UInt32

module S = FStar.Seq
#set-options "--max_fuel 0 --max_ifuel 0"

noeq
type vector_s (a: Type0) =
| Vector:
    len:U32.t -> // number of elements in the vector
    max:U32.t -> // capacity r
    arr:A.array a ->
    vector_s a

let vector (a: Type0) = P.pointer (vector_s a)

let vector_view (#a : Type0) (v : vector a) : Tot (view (vector_view_t a)) =
  let v_ptr_r : resource = P.ptr_resource v in
  reveal_view ();
  P.reveal_ptr ();
  A.reveal_array ();
  let get_arr (h: HS.mem) : GTot (A.array a) = (Seq.index (A.as_seq h v) 0).arr in
  let get_len (h: HS.mem) : GTot U32.t = (Seq.index (A.as_seq h v) 0).len in
  let get_max (h: HS.mem) : GTot U32.t = (Seq.index (A.as_seq h v) 0).max in
  let get_perm (h : HS.mem) : GTot (Ghost.erased LowStar.Permissions.permission) =
    Ghost.hide (A.get_perm h (get_arr h) 0)
  in
  let get_seq (h: HS.mem) : GTot (Seq.seq a) =
    A.as_seq h (get_arr h)
  in
  let v_arr_r (h: HS.mem) : GTot resource = A.array_resource (get_arr h) in
  let fp (h: HS.mem) =
     (A.loc_array v)
    `A.loc_union`
    (A.loc_array (Seq.index (A.as_seq h v) 0).arr)
  in
  let inv (h: HS.mem) : prop =
    inv v_ptr_r h /\ inv (v_arr_r h) h /\
    U32.v (get_len h) <= U32.v (get_max h) /\
    U32.v (get_len h) >= 0
  in
  let sel (h: HS.mem) : GTot (vector_view_t a) =
    {
      v_capacity = get_max h;
      v_arr = get_seq h;
      v_perm = get_perm h;
    }
  in
  { fp; inv; sel }


let create #a init max =
  admit()

let push #a v x =
  admit()
