module LowStar.RST.Vector


open LowStar.RST
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module A = LowStar.RST.Array
module Arr = LowStar.Array
module P = LowStar.RST.Pointer
module U32 = FStar.UInt32
module L = LowStar.RST.Loops
module S = FStar.Seq
module Perm = LowStar.Permissions
#set-options "--max_fuel 0 --max_ifuel 0"

noeq
type vector_s (a: Type0) =
| Vector:
    len:U32.t -> // number of elements in the vector
    max:U32.t -> // capacity
    arr:A.array a ->
    vector_s a

let vector (a: Type0) = P.pointer (vector_s a)

let hget_arr (h: HS.mem) (#a: Type0) (v:vector a) : GTot (A.array a) =
  (Seq.index (A.as_seq h v) 0).arr
let hget_len (h: HS.mem) (#a: Type0) (v:vector a) : GTot U32.t = (Seq.index (A.as_seq h v) 0).len
let hget_max (h: HS.mem) (#a: Type0) (v:vector a) : GTot U32.t = (Seq.index (A.as_seq h v) 0).max
let hget_perm (h : HS.mem) (#a: Type0) (v:vector a)
  : GTot (Ghost.erased LowStar.Permissions.permission) =
  Ghost.hide (A.get_perm h (hget_arr h v) 0)
let hget_seq (h: HS.mem) (#a: Type0) (v:vector a) : GTot (Seq.seq a) =
  A.as_seq h (hget_arr h v)
let hget_arr_r (h: HS.mem) (#a: Type0) (v:vector a) : GTot resource =
  A.array_resource (hget_arr h v)

let vector_view (#a : Type0) (v : vector a) : Tot (view (vector_view_t a)) =
  let v_ptr_r : resource = P.ptr_resource v in
  reveal_view ();
  P.reveal_ptr ();
  A.reveal_array ();

  let fp_r (h: HS.mem) =
    (as_loc (fp (P.ptr_resource v)) h)
    `A.loc_union`
    (as_loc (fp (A.array_resource (hget_arr h v))) h)
  in
  let inv_r (h: HS.mem) : prop =
    inv v_ptr_r h /\ inv (hget_arr_r h v) h /\
    (as_loc (fp (P.ptr_resource v)) h) `A.loc_disjoint`
      (as_loc (fp (A.array_resource (hget_arr h v))) h) /\
    A.length (hget_arr h v) = hget_max h v /\
    U32.v (hget_len h v) <= U32.v (hget_max h v) /\
    U32.v (hget_len h v) >= 0 /\
    Ghost.reveal (hget_perm h v) = A.get_perm h v 0 /\
    A.freeable (hget_arr h v)
  in
  let sel_r (h: HS.mem) : GTot (vector_view_t a) =
    let len = U32.v  (hget_len h v) in
    let correct_len = if len >= 0 && len <= S.length (hget_seq h v) then len else 0 in
    {
      v_capacity = hget_max h v;
      v_arr = S.slice (hget_seq h v) 0 correct_len;
      v_perm = hget_perm h v;
    }
  in
  { fp = fp_r ; inv = inv_r; sel = sel_r }


let create #a init max =
  (**) reveal_empty_resource ();
  (**) reveal_rst_inv ();
  (**) reveal_view ();
  (**) P.reveal_ptr ();
  (**) A.reveal_array ();
  (**) reveal_modifies ();
  let contents = A.alloc init max in
  let v = Vector 0ul max contents in
  let ptr = P.ptr_alloc v in
  ptr

#set-options "--z3rlimit 20"

let push #a v x =
  (**) reveal_empty_resource ();
  (**) reveal_rst_inv ();
  (**) reveal_view ();
  (**) reveal_star ();
  (**) P.reveal_ptr ();
  (**) A.reveal_array ();
  (**) reveal_modifies ();
  let v_record = P.ptr_read v in
  let max = v_record.max in
  let len = v_record.len in
  (**) let h0 = HST.get () in
  if U32.(len <^ max) then begin
    A.upd v_record.arr len x;
    P.ptr_write v (Vector U32.(v_record.len +^ 1ul) v_record.max v_record.arr);
    (**) let h1 = HST.get () in
    (**) assert(
    (**)   S.slice (hget_seq h1 v) 0 (U32.v len + 1) `S.equal`
    (**)     S.snoc (S.slice (hget_seq h0 v) 0 (U32.v len)) x
    (**) )
  end else begin
    let max_uint32 = UInt32.uint_to_t (UInt.max_int 32) in
    let new_contents_lenght =
      if U32.(max >^ max_uint32 /^ 2ul) then
        max_uint32
      else
        U32.(2ul *^ max)
    in
    let new_contents = A.alloc x new_contents_lenght in
    (**) let h1 = HST.get () in
    (**) let sub_new = LowStar.Array.sub new_contents 0ul len in
    (**) reveal_star_inv (A.array_resource sub_new) (A.array_resource v_record.arr) h1;
    (**) assert(inv (A.array_resource v_record.arr) h1);
    (**) assume(inv (A.array_resource sub_new) h1);
    (**) assume(A.fresh_loc (A.loc_array new_contents) h0 h1);
    (**) assume(A.loc_disjoint (A.loc_array sub_new) (A.loc_array v_record.arr));
    (**) assume(rst_inv (A.array_resource sub_new <*> A.array_resource v_record.arr) h1);
    A.copy sub_new v_record.arr;
    (**) let h2 = HST.get () in
    A.free v_record.arr;
    (**) let h3 = HST.get () in
    let new_v_record = Vector len max new_contents in
    (**) assume(inv (P.ptr_resource v) h3);
    (**) assume(rst_inv (P.ptr_resource v) h3);
    (**) assume(Perm.allows_write (A.get_perm h3 v 0));
    P.ptr_write v new_v_record;
    (**) let h4 = HST.get () in
    (**) assume(inv (vector_resource v) h4);
    (**) assume(rst_inv (vector_resource v) h4);
    (**) assume(A.modifies (as_loc (fp (vector_resource v)) h0) h0 h4);
    (**) assume(frame_usedness_preservation (as_loc (fp ((vector_resource v))) h0) (as_loc (fp ((vector_resource v))) h4) h0 h4)
  end
