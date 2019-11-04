module AllHands

open Steel.RST

module A = Steel.Array
module P = LowStar.Permissions
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

#set-options "--max_fuel 0 --max_ifuel 0"

(**** Resources *)

let res0 : resource = empty_resource

let res1 (a: A.array U32.t) : resource = A.array_resource a

[@expect_failure]
let res1_fp (a: A.array U32.t) : GTot (fp:fp_t{forall (h: HS.mem). as_loc fp h == A.loc_array a}) =
  //A.reveal_array ();
  fp (res1 a)

let res1_inv (a: A.array U32.t) : GTot (inv:inv_t{
  forall (h: HS.mem). inv h <==> A.live h a /\ A.constant_perm_seq h a
}) =
  A.reveal_array ();
  inv (res1 a)

let res1_view (a: A.array U32.t) : GTot (sel:(sel_t (A.varray a)){
  forall (h: HS.mem). sel h == {
    A.s = A.as_seq h a;
    A.p = A.get_perm h a 0
  }
}) =
  A.reveal_array ();
  sel (res1 a).view

let res2 (a b: A.array U32.t) : resource =
  A.array_resource a <*> A.array_resource b

#push-options "--max_fuel 1 --max_ifuel 1"

let rec list_res (l: list (A.array U32.t)) : resource =
  match l with
  | [] -> empty_resource
  | hd::tl -> A.array_resource hd <*> list_res tl

#pop-options

let res3 (a b: A.array U32.t) : resource =
  hsrefine (res2 a b) (fun h -> A.vlength a == A.vlength b /\ A.as_rseq a h == A.as_rseq b h)

(**** The RST effect *)

let foo1 (a: A.array U32.t) : RST unit
  (A.array_resource a)
  (fun _ -> A.array_resource a)
  (fun h0 -> P.allows_write (A.get_rperm a h0))
  (fun h0 _ h1 ->
    Seq.index (A.as_rseq a h1) 0 == U32.add_mod (Seq.index (A.as_rseq a h0) 0) 1ul /\
    (forall (j:nat{j > 0 /\ j < A.vlength a}).
       Seq.index (A.as_rseq a h1) j ==  Seq.index (A.as_rseq a h0) j)
  )
  =
  let x = A.index a 0ul in
  let new_x = (U32.add_mod x 1ul) in
  A.upd a 0ul new_x

let points_to (a: A.array U32.t) (x: U32.t) : resource =
  hsrefine (A.array_resource a) (fun h ->
    Seq.index (A.as_rseq a h) 0 == x /\ P.allows_write (A.get_rperm a h)
  )

let foo2 (a b: A.array U32.t) : RST unit
  (A.array_resource a <*> A.array_resource b)
  (fun _ -> A.array_resource a <*> A.array_resource b)
  (fun h0 -> P.allows_write (A.get_rperm a h0))
  (fun h0 _ h1 ->
    Seq.index (A.as_rseq a h1) 0 == U32.add_mod (Seq.index (A.as_rseq a h0) 0) 1ul /\
    (forall (j:nat{j > 0 /\ j < A.vlength a}).
       Seq.index (A.as_rseq a h1) j ==  Seq.index (A.as_rseq a h0) j) /\
    A.as_rseq b h1 == A.as_rseq b h0
  )
  =
  let x = rst_frame
    (A.array_resource a <*> A.array_resource b)
    (fun _ -> A.array_resource a <*> A.array_resource b)
    (fun _ -> A.index a 0ul)
  in
  let new_x = (U32.add_mod x 1ul) in
  rst_frame
    (A.array_resource a <*> A.array_resource b)
    (fun _ -> A.array_resource a <*> A.array_resource b)
    (fun _ -> A.upd a 0ul new_x)
