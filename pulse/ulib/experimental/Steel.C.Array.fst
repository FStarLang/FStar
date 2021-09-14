module Steel.C.Array

module S = Steel.C.Struct

let array_domain
  (t: Type u#0)
  (n: Ghost.erased size_t)
: Tot Type0
= (x: size_t { size_v x < size_v n })

let array_range
  (t: Type u#0)
  (n: Ghost.erased size_t)
  (x: array_domain t n)
: Tot Type0
= option t

open FStar.FunctionalExtensionality

let array_pcm_carrier t n = restricted_t (array_domain t n) (array_range t n)

let array_elements_pcm
  (t: Type u#0)
  (n: Ghost.erased size_t)
  (x: array_domain t n)
: Tot (Steel.C.PCM.pcm (array_range t n x))
= Steel.C.Opt.opt_pcm #t

let array_pcm t n = S.prod_pcm (array_elements_pcm t n)

[@"opaque_to_smt"]
let rec raise_list_array_domain
  (t: Type u#0)
  (n n': size_t)
  (l: list (array_domain t n))
: Pure (list (array_domain t n'))
  (requires (size_v n' >= size_v n))
  (ensures (fun l' ->
    (forall (x': array_domain t n') . List.Tot.mem x' l' <==> (size_v x' < size_v n /\ List.Tot.mem x' l)) /\
    List.Tot.length l' == List.Tot.length l
  ))
= match l with
  | [] -> []
  | x :: l_ -> x :: raise_list_array_domain t n n' l_

[@"opaque_to_smt"]
let rec included_indices
  (t: Type u#0)
  (n: size_t)
: Pure (list (array_domain t n))
  (requires True)
  (ensures (fun l ->
    (forall (x: array_domain t n) . List.Tot.mem x l) /\
    List.Tot.length l == size_v n
  ))
  (decreases (size_v n))
= if n = mk_size_t (FStar.UInt32.uint_to_t 0)
  then []
  else
    let n' = size_sub n (mk_size_t (FStar.UInt32.uint_to_t 1)) in
    n' :: raise_list_array_domain t n' n (included_indices t n')

let array_elements_view_type
  (t: Type u#0)
  (n: size_t)
  (k: array_domain t n)
: Tot Type0
= t

let array_elements_view
  (t: Type u#0)
  (n: size_t)
  (k: array_domain t n)
: Tot (Steel.C.Ref.sel_view (array_elements_pcm t n k) (array_elements_view_type t n k) false)
= Steel.C.Opt.opt_view _

let intro_array_view_init
  (t: Type u#0)
  (n: size_t)
  (x: restricted_t (Steel.C.Ref.refine (array_domain t n) (S.mem (included_indices t n))) (array_elements_view_type t n))
  (k: nat { k < size_v n })
: Tot t
= x (int_to_size_t k)

let intro_array_view
  (t: Type u#0)
  (n: size_t)
  (x: restricted_t (Steel.C.Ref.refine (array_domain t n) (S.mem (included_indices t n))) (array_elements_view_type t n))
: Tot (array_view_type t n)
= Seq.init (size_v n) (intro_array_view_init t n x)

let array_to_view
  (t: Type u#0)
  (n: size_t)
  (x: Steel.C.Ref.refine (array_pcm_carrier t n) (S.struct_view_to_view_prop (array_elements_view t n) (included_indices t n)))
: Tot (array_view_type t n)
= intro_array_view t n (S.struct_view_to_view (array_elements_view t n) (included_indices t n) x)

let elim_array_view_f
  (t: Type u#0)
  (n: size_t)
  (x: array_view_type t n)
  (k: Steel.C.Ref.refine (array_domain t n) (S.mem (included_indices t n)))
: Tot (array_elements_view_type t n k)
= Seq.index x (size_v k)

let elim_array_view
  (t: Type u#0)
  (n: size_t)
  (x: array_view_type t n)
: Tot (restricted_t (Steel.C.Ref.refine (array_domain t n) (S.mem (included_indices t n))) (array_elements_view_type t n))
= on_dom (Steel.C.Ref.refine (array_domain t n) (S.mem (included_indices t n))) (elim_array_view_f t n x)

let array_to_carrier
  (t: Type u#0)
  (n: size_t)
  (x: array_view_type t n)
: Tot (Steel.C.Ref.refine (array_pcm_carrier t n) (S.struct_view_to_view_prop (array_elements_view t n) (included_indices t n)))
= S.struct_view_to_carrier (array_elements_view t n) (included_indices t n) (elim_array_view t n x)

open Steel.C.PCM

let array_view_to_view_frame
  (t: Type u#0)
  (n: size_t)
  (x: array_view_type t n)
  (frame: array_pcm_carrier t n)
: Lemma
    (requires (composable (array_pcm t n) (array_to_carrier t n x) frame))
    (ensures
      S.struct_view_to_view_prop (array_elements_view t n) (included_indices t n)
        (op (array_pcm t n) (array_to_carrier t n x) frame) /\ 
      array_to_view t n
        (op (array_pcm t n) (array_to_carrier t n x) frame) `Seq.equal` x)
= S.struct_view_to_view_frame (array_elements_view t n) (included_indices t n)
    (elim_array_view t n x) frame

let array_view' (t: Type u#0) (n: size_t)
  : Tot (Steel.C.Ref.sel_view (array_pcm t n) (array_view_type t n) (size_v n = 0))
=
  let open Steel.C.Ref in
  {
    to_view_prop = S.struct_view_to_view_prop (array_elements_view t n) (included_indices t n);
    to_view = array_to_view t n;
    to_carrier = array_to_carrier t n;
    to_carrier_not_one = (S.struct_view (array_elements_view t n) (included_indices t n)).to_carrier_not_one;
    to_view_frame = array_view_to_view_frame t n;
  }

let array_view t n =
  assert (size_v n > 0);
  array_view' t n

noeq
type array base t = {
  base_len: Ghost.erased size_t;
  base_ref: Steel.C.Reference.ref base (array_view_type t base_len) (array_pcm t base_len);
  from: size_t;
  to: size_t; // must be Tot because of array_small_to_large below
  prf: squash (
    size_v base_len >= 0 /\
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  );
}

let len a = a.to `size_sub` a.from

let rec array_is_unit_aux
  (t: Type0) (n: size_t) (a: array_pcm_carrier t n)
  (i: size_t)
  (f:
    (j: size_t) ->
    Lemma
    (requires (size_v j < size_v n - size_v i))
    (ensures (size_v j < size_v n - size_v i /\ a j == one (array_elements_pcm t n j)))
  )
: Pure bool
  (requires True)
  (ensures (fun y -> y == true <==> (forall j . size_v j < size_v n ==> a j == one (array_elements_pcm t n j))))
  (decreases (size_v i))
= Classical.forall_intro (Classical.move_requires f);
  if size_le i zero_size
  then true
  else
    let i' = size_sub i one_size in
    if not (size_le i n)
    then array_is_unit_aux t n a i' (fun _ -> ())
    else if None? (a (size_sub n i))
    then array_is_unit_aux t n a i' (fun j -> if j = size_sub n i then () else f j)
    else false

let array_is_unit_lemma
  (t: Type0) (n: size_t) (a: array_pcm_carrier t n)
: Lemma
  (requires (forall (j: array_domain  t n) . a j == one (array_elements_pcm t n j)))
  (ensures (a == one (array_pcm t n)))
= S.ext a (one (array_pcm t n)) (fun _ -> ())

let array_is_unit t n a =
  Classical.move_requires (array_is_unit_lemma t n) a;
  array_is_unit_aux t n a n (fun _ -> ())

let array_large_to_small_f
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: Ghost.erased size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (x: array_pcm_carrier t base_len)
: Tot (array_pcm_carrier t (to `size_sub` from))
= on_dom (array_domain t (to `size_sub` from)) (fun k -> x (from `size_add` k))

let array_large_to_small
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: Ghost.erased size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
: Tot (Steel.C.Connection.morphism #(array_pcm_carrier t base_len) #(array_pcm_carrier t (to `size_sub` from))  (array_pcm t base_len) (array_pcm t (to `size_sub` from)))
= Steel.C.Connection.mkmorphism
    (array_large_to_small_f t base_len from to sq)
    (assert (array_large_to_small_f t base_len from to sq (one (array_pcm t base_len)) `feq` one (array_pcm t (to `size_sub` from))))
    (fun x1 x2 ->
      assert (array_large_to_small_f t base_len from to sq (op (array_pcm t base_len) x1 x2) `feq` op (array_pcm t (to `size_sub` from)) (array_large_to_small_f t base_len from to sq x1)  (array_large_to_small_f t base_len from to sq x2))
    )

let array_small_to_large_f
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t) // Tot, argh
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (x: array_pcm_carrier t (to `size_sub` from))
: Tot (array_pcm_carrier t base_len)
= on_dom (array_domain t base_len) (fun k -> if size_le from k && not (size_le to k) then x (k `size_sub` from)
  else one (Steel.C.Opt.opt_pcm #t))

let array_small_to_large
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
: Tot (Steel.C.Connection.morphism (array_pcm t (to `size_sub` from))  (array_pcm t base_len))
= Steel.C.Connection.mkmorphism
    (array_small_to_large_f t base_len from to sq)
    (assert (array_small_to_large_f t base_len from to sq (one (array_pcm t (to `size_sub` from))) `feq` one (array_pcm t (base_len))))
    (fun x1 x2 ->
      assert (array_small_to_large_f t base_len from to sq (op (array_pcm t (to `size_sub` from)) x1 x2) `feq` op (array_pcm t (base_len)) (array_small_to_large_f t base_len from to sq x1)  (array_small_to_large_f t base_len from to sq x2))
    )

let array_small_to_large_to_small
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
: Lemma
  (array_large_to_small_f t base_len from to sq `Steel.C.Connection.is_inverse_of` array_small_to_large_f t base_len from to sq)
= assert (forall x . array_large_to_small_f t base_len from to sq (array_small_to_large_f t base_len from to sq x) `feq` x)

#push-options "--z3rlimit 32 --fuel 1 --ifuel 2 --query_stats --z3cliopt smt.arith.nl=false"
#restart-solver

assume
val size_sub' (x y: size_t) (sq: squash (size_v x >= size_v y)) : Pure size_t
  (requires True)
  (ensures (fun z -> size_v z == size_v x - size_v y))

#restart-solver

let array_conn_fpu_f
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (x: Ghost.erased (array_pcm_carrier t (to `size_sub` from)) { ~ (Ghost.reveal x == one (array_pcm t (to `size_sub` from))) })
  (y: Ghost.erased (array_pcm_carrier t (to `size_sub` from)))
  (f: frame_preserving_upd (array_pcm t (to `size_sub` from)) x y)
  (v: frame_preserving_upd_dom (array_pcm t base_len) (array_small_to_large_f t base_len from to sq x))
: Tot (array_pcm_carrier t base_len)
= let sq0 : squash (size_v to >= size_v from) = () in
  let z : size_t = size_sub' to from sq0 in
  let v_small : array_pcm_carrier t z = array_large_to_small_f t base_len from to sq v in
  // let frame : Ghost.erased (array_pcm_carrier t base_len) = Ghost.hide (compatible_elim (array_pcm t base_len) (array_small_to_large_f t base_len from to sq x) v) in
  // let frame_small : Ghost.erased (array_pcm_carrier t (z)) = Ghost.hide (array_large_to_small_f t base_len from to sq (Ghost.reveal frame)) in
  // S.prod_pcm_composable_intro
  //   (array_elements_pcm t z)
  //   x
  //   frame_small
  //   (fun h -> assume False);
  // assert (composable (array_pcm t (z)) x frame_small);
  // op_comm (array_pcm t (z)) x frame_small;
  // assert (op (array_pcm t (z)) frame_small x `feq` v_small);
  // compatible_intro (array_pcm t (z)) x v_small frame_small;
  assume (compatible (array_pcm t (z)) x v_small);
  assume (p_refine (array_pcm t (z)) v_small); // TODO: remove p_refine from Steel.C.PCM
  let v_small' : array_pcm_carrier t z = f v_small in
  let v' : array_pcm_carrier t base_len =
    on_dom (array_domain t base_len) (fun (k: array_domain t base_len) ->
      if from `size_le` k && not (to `size_le` k)
      then begin
        let sq2 : squash (size_v k >= size_v from) = assert (size_v k >= size_v from) in
        v_small' (size_sub' k from sq2) <: option t
      end
      else v k
    )
  in
  v'

let array_conn_fpu
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (x: Ghost.erased (array_pcm_carrier t (to `size_sub` from)) { ~ (Ghost.reveal x == one (array_pcm t (to `size_sub` from))) })
  (y: Ghost.erased (array_pcm_carrier t (to `size_sub` from)))
  (f: frame_preserving_upd (array_pcm t (to `size_sub` from)) x y)
: Tot (frame_preserving_upd (array_pcm t base_len) (array_small_to_large_f t base_len from to sq x) (array_small_to_large_f t base_len from to sq y))
= frame_preserving_upd_intro
    (array_pcm t base_len) (array_small_to_large_f t base_len from to sq x) (array_small_to_large_f t base_len from to sq y)
    (array_conn_fpu_f t base_len from to sq x y f)
    (fun _ -> assume False)
    (fun _ _ -> assume False)
    (fun _ _ -> assume False)

#pop-options

let array_conn
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
: Steel.C.Connection.connection
    (array_pcm t base_len)
    (array_pcm t (to `size_sub` from))
=
  Steel.C.Connection.mkconnection
    (array_small_to_large t base_len from to sq)
    (array_large_to_small t base_len from to sq)
    (array_small_to_large_to_small t base_len from to sq)
    (array_conn_fpu t base_len from to sq)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2 --query_stats --z3cliopt smt.arith.nl=false"
#restart-solver

let array_conn_id
  (t: Type0)
  (base_len: Ghost.erased size_t)
: Lemma
  (array_conn t base_len (mk_size_t (FStar.UInt32.uint_to_t 0)) base_len () == Steel.C.Connection.connection_id _)
=
  let z = mk_size_t (FStar.UInt32.uint_to_t 0) in
  assert (forall x . array_small_to_large_f t base_len z base_len () x `feq` x);
  assume (forall (x: Ghost.erased (array_pcm_carrier t (base_len `size_sub` z)) { ~ (Ghost.reveal x == one (array_pcm t (base_len `size_sub` z))) }) y (f: frame_preserving_upd (array_pcm t (base_len `size_sub` z)) x y) v . array_conn_fpu_f t base_len z base_len () x y f v `feq` f v);
  assert (forall x y f . array_conn_fpu_f t base_len z base_len () x y f `feq` f);
  assume ((array_conn t base_len (mk_size_t (FStar.UInt32.uint_to_t 0)) base_len ()).Steel.C.Connection.conn_lift_frame_preserving_upd === (Steel.C.Connection.connection_id (array_pcm t base_len)).Steel.C.Connection.conn_lift_frame_preserving_upd);
  array_conn t base_len (mk_size_t (FStar.UInt32.uint_to_t 0)) base_len () `Steel.C.Connection.connection_eq` Steel.C.Connection.connection_id _

#restart-solver

let array_conn_compose
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from1: size_t)
  (to1: size_t)
  (from2: size_t)
  (to2: size_t)
: Lemma
  (requires (
    size_v from1 <= size_v to1 /\
    size_v to1 <= size_v base_len /\
    size_v from2 <= size_v to2 /\
    size_v from1 + size_v to2 <= size_v to1
  ))
  (ensures (
    array_conn t base_len from1 to1 () `Steel.C.Connection.connection_compose` array_conn t (to1 `size_sub` from1) from2 to2 () ==
    array_conn t base_len (from1 `size_add` from2) (from1 `size_add` to2) ()
  ))
=
  let z = to1 `size_sub` from1 in
  assert (forall x . array_small_to_large_f t base_len from1 to1 () (array_small_to_large_f t z from2 to2 ()  x) `feq` array_small_to_large_f t base_len (from1 `size_add` from2) (from1 `size_add` to2) () x);
  assert (forall x . array_large_to_small_f t z from2 to2 () (array_large_to_small_f t base_len from1 to1 () x) `feq` array_large_to_small_f t base_len (from1 `size_add` from2) (from1 `size_add` to2) () x);
  let cc = array_conn t base_len from1 to1 () `Steel.C.Connection.connection_compose` array_conn t z from2 to2 () in
  let c = array_conn t base_len (from1 `size_add` from2) (from1 `size_add` to2) () in
  assume (
    cc.Steel.C.Connection.conn_lift_frame_preserving_upd ===
    c.Steel.C.Connection.conn_lift_frame_preserving_upd
  );
  cc `Steel.C.Connection.connection_eq` c

let to_view_array_conn
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (x: array_pcm_carrier t base_len)
: Lemma
  (requires (
    S.struct_view_to_view_prop (array_elements_view t base_len) (included_indices t base_len) x 
  ))
  (ensures (
    let x' = array_large_to_small_f t base_len from to sq x in
    S.struct_view_to_view_prop (array_elements_view t (to `size_sub` from)) (included_indices t (to `size_sub` from)) x' /\
    array_to_view t (to `size_sub` from) x' `Seq.equal` Seq.slice (array_to_view t base_len x) (size_v from) (size_v to)
  ))
= ()

#pop-options

let array_as_ref
  (#base: Type)
  (#t: Type)
  (a: array base t)
: GTot (Steel.C.Reference.ref base (array_view_type t (len a)) (array_pcm t (len a)))
= Steel.C.Ref.ref_focus a.base_ref (array_conn t a.base_len a.from a.to a.prf)

[@@__steel_reduce__]
let varray0
  (#base: Type)
  (#t: Type)
  (x: array base t)
: Tot vprop
= Steel.C.Ref.pts_to_view
    #base
    #(array_pcm_carrier t (len x))
    #(array_pcm t (len x))
    (array_as_ref #base #t x)
    #(array_view_type t (len x))
    #(size_v (len x) = 0)
    (array_view' t (len x))

let varray_hp #base #t x = hp_of (varray0 #base #t x)

#push-options "--debug Steel.C.Array --debug_level Extreme"

let varray_sel #base #t x = sel_of (varray0 #base #t x)

#pop-options

let intro_varray1
  (#inames: _)
  (#base: Type)
  (#t: Type)
  (x: array base t)
: SteelGhost unit inames
    (varray0 x)
    (fun _ -> varray x)
    (fun _ -> True)
    (fun h _ h' -> h' (varray x) == h (varray0 x))
= change_slprop_rel
    (varray0 x)
    (varray x)
    (fun u v -> u == v)
    (fun m -> ())

let elim_varray1
  (#inames: _)
  (#base: Type)
  (#t: Type)
  (x: array base t)
: SteelGhost unit inames
    (varray x)
    (fun _ -> varray0 x)
    (fun _ -> True)
    (fun h _ h' -> h' (varray0 x) == h (varray x))
= change_slprop_rel
    (varray x)
    (varray0 x)
    (fun u v -> u == v)
    (fun m -> ())

val mk_array (#base: Type u#0) (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref base (array_view_type t n) (array_pcm t n))
: Pure (array base t)
  (requires (size_v n > 0))
  (ensures (fun a -> len a == Ghost.reveal n))

let mk_array #base #t #n r =
  {
    base_len = n;
    base_ref = r;
    from = mk_size_t 0ul;
    to = n;
    prf = ();
  }

let g_mk_array r = mk_array r

#push-options "--z3rlimit 32"

let intro_varray
  #base #t #n r sq
=
  let res = mk_array r in
  assert (array_as_ref res == Steel.C.Ref.ref_focus r (array_conn t n (mk_size_t 0ul) n ()));
  array_conn_id t n;
  assert (array_conn t n (mk_size_t 0ul) n () == Steel.C.Connection.connection_id (array_pcm t n));
  assert (array_as_ref res == Steel.C.Ref.ref_focus r (Steel.C.Connection.connection_id (array_pcm t n)));
  Steel.C.Ref.ref_focus_id r;
  assert (Steel.C.Ref.ref_focus r (Steel.C.Connection.connection_id (array_pcm t n)) == r);
  assert (array_as_ref res == r);
  change_equal_slprop
    (r `Steel.C.Ref.pts_to_view` _)
    (varray0 res);
  intro_varray1 res;
  return res

let elim_varray
  #_ #base #t #n r res sq
=
  assert (res == g_mk_array r);
  assert (array_as_ref res == Steel.C.Ref.ref_focus r (array_conn t n (mk_size_t 0ul) n ()));
  array_conn_id t n;
  assert (array_conn t n (mk_size_t 0ul) n () == Steel.C.Connection.connection_id (array_pcm t n));
  assert (array_as_ref res == Steel.C.Ref.ref_focus r (Steel.C.Connection.connection_id (array_pcm t n)));
  Steel.C.Ref.ref_focus_id r;
  assert (Steel.C.Ref.ref_focus r (Steel.C.Connection.connection_id (array_pcm t n)) == r);
  assert (array_as_ref res == r);
  elim_varray1 res;
  change_equal_slprop
    (varray0 res)
    (r `Steel.C.Ref.pts_to_view` _)

#pop-options

let adjacent r1 r2 =
  r1.base_len == r2.base_len /\
  r1.base_ref == r2.base_ref /\
  r1.to == r2.from

val t_merge
  (#base: Type)
  (#t: Type)
  (r1 r2: array base t)
: Pure (array base t)
  (requires (adjacent r1 r2))
  (ensures (fun r -> length r == length r1 + length r2))

let t_merge r1 r2 =
  {
    base_len = r1.base_len;
    base_ref = r1.base_ref;
    from = r1.from;
    to = r2.to;
    prf = ();
  }

let merge r1 r2 = t_merge r1 r2

let merge_assoc r1 r2 r3 = ()

val tsplit
  (#base: Type)
  (#t: Type)
  (r: array base t)
  (i: size_t)
: Pure (array base t & array base t)
  (requires (size_v i <= length r))
  (ensures (fun (rl, rr) ->
    merge_into rl rr r /\
    length rl == size_v i
  ))

let tsplit r i =
  ({
    base_len = r.base_len;
    base_ref = r.base_ref;
    from = r.from;
    to = r.from `size_add` i;
    prf = ()
  }, {
    base_len = r.base_len;
    base_ref = r.base_ref;
    from = r.from `size_add` i;
    to = r.to;
    prf = ()
  })

let gsplit r i = tsplit r i

assume
val pts_to_split
  (t: Type)
  (n: size_t)
  (x: array_pcm_carrier t n)
  (i: size_t)
: Lemma
  (requires (size_v i <= size_v n))
  (ensures (
    let z = mk_size_t 0ul in
    let xl = array_small_to_large_f t n z i () (array_large_to_small_f t n z i () x) in
    let xr = array_small_to_large_f t n i n () (array_large_to_small_f t n i n () x) in
    composable (array_pcm t n) xl xr /\
    op (array_pcm t n) xl xr == x
  ))

(*TODO: split focus into gfocus + tfocus *)

let split
  #j #base #t x i
=
  elim_varray1 x;
  let v = Steel.C.Ref.pts_to_view_elim
    #j
    #base
    #(array_pcm_carrier t (len x))
    #(array_pcm t (len x))
    (array_as_ref #base #t x)
    #(array_view_type t (len x))
    #(size_v (len x) = 0)
    (array_view' t (len x))
  in
  let n = len x in
  pts_to_split t n v i;
  let z = mk_size_t 0ul in
  let vl = array_small_to_large_f t n z i () (array_large_to_small_f t n z i () v) in
  let vr = array_small_to_large_f t n i n () (array_large_to_small_f t n i n () v) in
  
  sladmit ();
  magic ()
  
  

(*

noeq
type array base t = {
  base_len: Ghost.erased size_t;
  base_ref: Steel.C.Reference.ref base (array_view_type t base_len) (array_pcm t base_len);
  from: size_t;
  to: size_t; // must be Tot because of array_small_to_large below
  prf: squash (
    size_v base_len >= 0 /\
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  );
}
