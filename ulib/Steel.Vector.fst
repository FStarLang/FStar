module Steel.Vector


open Steel.RST
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module A = Steel.Array
module Arr = LowStar.Array
module M = LowStar.Array.Modifies
module P = Steel.Pointer
module U32 = FStar.UInt32
module L = Steel.Loops
module S = FStar.Seq
module Perm = LowStar.Permissions
#set-options "--max_fuel 0 --max_ifuel 0"

noeq
type contents_t (a: Type0) =
| Vector:
    len:U32.t -> // number of elements in the vector
    max:U32.t -> // capacity
    arr:A.array a ->
    contents_t a

let vector (a: Type0) = P.pointer (contents_t a)

let as_contents (h: HS.mem) (#a: Type0) (v:vector a) : GTot (contents_t a) =
  (Seq.index (A.as_seq h v) 0)

let vector_view (#a : Type0) (v : vector a) : Tot (view (vector_view_t a)) =
  let v_ptr_r : resource = P.ptr_resource v in
  reveal_view ();
  P.reveal_ptr ();
  A.reveal_array ();
  reveal_star ();
  let fp_r (h: HS.mem) =
    as_loc (fp (P.ptr_resource v <*> A.array_resource (as_contents h v).arr)) h
  in
  let inv_r (h: HS.mem) : prop =
    inv (P.ptr_resource v <*> A.array_resource (as_contents h v).arr) h /\
    A.length (as_contents h v).arr = (as_contents h v).max /\
    U32.v (as_contents h v).len <= U32.v (as_contents h v).max /\
    U32.v (as_contents h v).len >= 0 /\
    A.get_rperm
      (as_contents h v).arr
      #(A.array_resource (as_contents h v).arr)
      (mk_rmem (A.array_resource (as_contents h v).arr) h) ==
      P.get_perm v #(P.ptr_resource v) (mk_rmem (P.ptr_resource v) h) /\
    A.freeable (as_contents h v).arr
  in
  let sel_r (h: HS.mem) : GTot (vector_view_t a) =
    let len = U32.v (as_contents h v).len in
    let correct_len = if len >= 0 && len <= A.vlength (as_contents h v).arr then len else 0 in
    {
      v_capacity = (as_contents h v).max;
      v_arr = S.slice (A.as_seq h (as_contents h v).arr) 0 correct_len;
      v_perm = Ghost.hide (A.get_perm h v 0);
    }
  in
  { fp = fp_r ; inv = inv_r; sel = sel_r }


val unpack_vector (#a: Type) (v: vector a) : RST (contents_t a)
  (vector_resource v)
  (fun contents -> A.array_resource contents.arr <*> P.ptr_resource v)
  (fun _ -> True)
  (fun h0 contents h1 ->
    A.length contents.arr = contents.max /\
    U32.v contents.len <= U32.v contents.max /\
    U32.v contents.len >= 0 /\
    A.get_rperm
      contents.arr
      (focus_rmem h1 (A.array_resource contents.arr)) == get_perm v h0 /\
    P.get_perm v (focus_rmem h1 (P.ptr_resource v)) == get_perm v h0  /\
    A.freeable contents.arr /\
    (h0 (vector_resource v)).v_capacity == contents.max /\
    as_rseq v h0 == S.slice (A.as_rseq contents.arr h1) 0 (U32.v contents.len)
  )
let unpack_vector #a v =
  P.reveal_ptr ();
  A.reveal_array ();
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_star ();
  P.ptr_read v

val pack_vector
  (#a: Type)
  (len: U32.t)
  (max: U32.t)
  (arr: A.array a)
  (v:P.pointer (contents_t a))
  : RST unit
    (P.ptr_resource v <*> A.array_resource arr)
    (fun _ -> vector_resource v)
    (fun h0 ->
      let contents = Vector len max arr in
      P.get_val v h0 == contents /\
      A.length arr = max /\
      U32.v len <= U32.v max /\
      U32.v len >= 0 /\
      A.freeable arr  /\
      A.get_rperm arr (focus_rmem h0 (A.array_resource arr)) ==
        P.get_perm v (focus_rmem h0 (P.ptr_resource v))
    )
    (fun h0 _ h1 ->
      let contents = Vector len max arr in
      P.get_val v h0 == contents /\
      U32.v len <= U32.v max /\
      U32.v len >= 0 /\
      A.length arr = max /\
     (h1 (vector_resource v)).v_capacity == max /\
       as_rseq v h1 == S.slice (A.as_rseq arr h0) 0 (U32.v len) /\
      get_perm v h1 == P.get_perm v (focus_rmem h0 (P.ptr_resource v)) /\
      get_perm v h1 ==  A.get_rperm arr (focus_rmem h0 (A.array_resource arr))
    )
let pack_vector #a len max arr  v =
  P.reveal_ptr ();
  A.reveal_array ();
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_star ()

#set-options "--z3rlimit 50"

let create #a init max =
  let arr = rst_frame
    empty_resource
    (fun arr -> A.array_resource arr)
    (fun _ -> A.alloc init max)
  in
  let v = rst_frame
    (A.array_resource arr)
    (fun v -> P.ptr_resource v <*> A.array_resource arr)
    ( fun _ -> P.ptr_alloc (Vector 0ul max arr))
  in
  let v_view : view (vector_view_t a) = vector_view v in
  assert(fp_reads_fp v_view.fp v_view.inv); (* TODO: figure out why this ? *)
  rst_frame
    (P.ptr_resource v <*> A.array_resource arr)
    (fun _ -> vector_resource v)
    (fun _ -> pack_vector 0ul max arr v);
  v


#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 100"

let push #a v x =
  (**) let h0 = HST.get () in
  (**) let h0_r = get (vector_resource v) in
  let contents = rst_frame
    (vector_resource v)
    (fun contents -> A.array_resource contents.arr <*> P.ptr_resource v)
    (* TODO: solve this unification problem *)
    #(fun contents -> A.array_resource contents.arr <*> P.ptr_resource v)
    (fun _ -> unpack_vector v)
  in
  let max = contents.max in
  let len = contents.len in
  let arr = contents.arr in
  if U32.(len <^ max) then begin
    rst_frame
      (A.array_resource arr <*> P.ptr_resource v)
      (fun _ ->  A.array_resource arr <*> P.ptr_resource v)
      (fun _ -> A.upd arr len x);
    let new_len =  U32.(len +^ 1ul) in
    let new_v_record = Vector new_len max arr in
    rst_frame
      (A.array_resource arr <*> P.ptr_resource v)
      (fun _ -> A.array_resource arr <*> P.ptr_resource v)
      (fun _ -> P.ptr_write v new_v_record);
    let h = get (P.ptr_resource v <*> A.array_resource arr) in
    rst_frame
      (A.array_resource arr <*> P.ptr_resource v)
      (fun _ -> vector_resource v)
      (fun _ -> pack_vector new_len max arr v);
    (**) let h1 = HST.get () in
    (**) (* Should go away with effect layering *)
    (**) assume(modifies (vector_resource v) (vector_resource v) h0 h1);
    (**) let h1_r = get (vector_resource v) in
    (**) let v0 = h0_r (vector_resource v)  in
    (**) let v1 = h1_r (vector_resource v) in
    (**) assert(S.slice v1.v_arr 0 (U32.v len) == v0.v_arr);
    (**) assert(S.index v1.v_arr (U32.v len) == x);
    (**) assert(v1.v_arr == S.snoc v0.v_arr x)
  end else begin
    let max_uint32 = UInt32.uint_to_t (UInt.max_int 32) in
    let new_contents_length =
      if U32.(max >^ max_uint32 /^ 2ul) then
        max_uint32
      else
        U32.(2ul *^ max)
    in
    assume(UInt32.v new_contents_length > UInt32.v len);
    let new_contents = rst_frame
      (A.array_resource arr <*> P.ptr_resource v)
      (fun b -> A.array_resource b <*> A.array_resource arr <*> P.ptr_resource v)
      (fun _ -> A.alloc x new_contents_length)
    in
    let new_contents_parts1, new_contents_parts2 = rst_frame
      (A.array_resource new_contents <*> A.array_resource arr <*> P.ptr_resource v)
      (fun new_contents_parts ->
        A.array_resource (fst new_contents_parts) <*> A.array_resource (snd new_contents_parts) <*>
        A.array_resource arr <*> P.ptr_resource v
      )
      (fun _ -> A.split new_contents len)
    in
    let current_res =
      A.array_resource new_contents_parts1 <*> A.array_resource new_contents_parts2 <*>
      A.array_resource arr <*> P.ptr_resource v
    in
    let h = get current_res in
    assume(A.array_resource new_contents_parts2 `is_subresource_of` current_res);
    assume(A.get_rperm new_contents_parts2 h == Perm.full_permission);
    rst_frame
      (
        A.array_resource new_contents_parts1 <*> A.array_resource new_contents_parts2 <*>
        A.array_resource arr <*> P.ptr_resource v
      )
      #(A.array_resource new_contents_parts2)
      (fun _ ->
        A.array_resource new_contents_parts1 <*> A.array_resource new_contents_parts2 <*>
        A.array_resource arr <*> P.ptr_resource v
      )
      #(fun _ -> A.array_resource new_contents_parts2)
      (fun _ -> A.upd new_contents_parts2 0ul x);
    let h = get current_res in
    assume(A.array_resource new_contents_parts1 `is_subresource_of` current_res);
    assume(Perm.allows_write (A.get_rperm new_contents_parts1 h));
    (*rst_frame
      (
        A.array_resource new_contents_parts1 <*> A.array_resource new_contents_parts2 <*>
        A.array_resource arr <*> P.ptr_resource v
      )
      #(A.array_resource new_contents_parts1 <*> A.array_resource arr)
      (fun _ ->
        A.array_resource new_contents_parts1 <*> A.array_resource new_contents_parts2 <*>
        A.array_resource arr <*> P.ptr_resource v
      )
      #(fun _ -> A.array_resource new_contents_parts1 <*> A.array_resource arr)
      (fun _ -> A.copy new_contents_parts1 arr);*)
    (**) admit()
  end


(*
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
    let new_contents_length =
      if U32.(max >^ max_uint32 /^ 2ul) then
        max_uint32
      else
        U32.(2ul *^ max)
    in
    let new_contents = rst_frame
      (A.array_resource v_record.arr)
      (fun b -> A.array_resource b <*> A.array_resource v_record.arr)
      (fun _ -> A.alloc x new_contents_length)
    in
    (**) let h1 = HST.get () in
    (**) let sub_new = LowStar.Array.sub new_contents 0ul len in
    (**) M.loc_union_gsub #a new_contents 0ul len U32.(new_contents_length -^ len);
    (**) A.gsub_zero_length new_contents;
    A.copy sub_new v_record.arr;
    (**) let h2 = HST.get () in
    admit();
    A.free v_record.arr;
    (**) let h3 = HST.get () in
    let new_v_record = Vector U32.(len +^ 1ul) new_contents_length new_contents in
    P.ptr_write v new_v_record;
    (**) let h4 = HST.get () in
    (**) assume(rst_inv (vector_resource v) h4);
    (**) assume(modifies (vector_resource v) (vector_resource v) h0 h4);
    (**) assert(inv (P.ptr_resource v) h4);
    (**) assume(inv (hget_arr_r h4 v) h4);
    (**) assert((as_loc (fp (P.ptr_resource v)) h4) `A.loc_disjoint`
    (**)  (as_loc (fp (A.array_resource (hget_arr h4 v))) h4));
    (**) assume(A.length (hget_arr h4 v) = hget_max h4 v);
    (**) assert(U32.v (hget_len h4 v) <= U32.v (hget_max h4 v));
    (**) assert(U32.v (hget_len h4 v) >= 0);
    (**) assert(Ghost.reveal (hget_perm h4 v) = A.get_perm h4 v 0);
    (**) assert(A.freeable (hget_arr h4 v));
    (**) assume(S.slice (hget_seq h4 v) 0 (U32.v new_contents_length) ==
    (**)   S.slice (hget_seq h0 v) 0 (U32.v len)
    (**) )
  end
*)
