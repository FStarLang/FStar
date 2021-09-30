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

let array_pcm_carrier_ext
  (t: Type)
  (n: size_t)
  (x1 x2: array_pcm_carrier t n)
  (f: (
    (i: array_domain t n) ->
    Lemma
    (x1 i == x2 i)
  ))
: Lemma
  (ensures (x1 == x2))
= Classical.forall_intro f;
  assert (x1 `feq` x2)

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

let array_large_to_small_f_eq
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: Ghost.erased size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (x: array_pcm_carrier t base_len)
  (k: array_domain t (to `size_sub` from))
: Lemma
  (array_large_to_small_f t base_len from to sq x k == x (from `size_add` k))
= ()

let array_large_to_small_f_eq'
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: Ghost.erased size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (x: array_pcm_carrier t base_len)
  (k' : array_domain t base_len)
: Lemma
  (requires (
    size_v from <= size_v k' /\
    size_v k' < size_v to
  ))
  (ensures (
    array_large_to_small_f t base_len from to sq x (k' `size_sub` from) == x k'
  ))
= ()

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

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2 --query_stats --z3cliopt smt.arith.nl=false"
#restart-solver

let size_sub' (x y: size_t) (sq: squash (size_v x >= size_v y)) : Pure size_t
  (requires True)
  (ensures (fun z -> size_v z == size_v x - size_v y))
= size_sub x y

#restart-solver

let array_conn_fpu_compatible
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (x: Ghost.erased (array_pcm_carrier t (to `size_sub` from)) { ~ (Ghost.reveal x == one (array_pcm t (to `size_sub` from))) })
  (v: frame_preserving_upd_dom (array_pcm t base_len) (array_small_to_large_f t base_len from to sq x))
: Lemma
  (
    let z = size_sub to from in
    let v_small : array_pcm_carrier t z = array_large_to_small_f t base_len from to sq v in
    compatible (array_pcm t z) x v_small
  )
=
  let z = size_sub to from in
  let v_small : array_pcm_carrier t z = array_large_to_small_f t base_len from to sq v in
  let frame : Ghost.erased (array_pcm_carrier t base_len) = Ghost.hide (compatible_elim (array_pcm t base_len) (array_small_to_large_f t base_len from to sq x) v) in
  let frame_small : Ghost.erased (array_pcm_carrier t (z)) = Ghost.hide (array_large_to_small_f t base_len from to sq (Ghost.reveal frame)) in
  S.prod_pcm_composable_intro
    (array_elements_pcm t z)
    x
    frame_small
    (fun h ->
      assert (composable (Steel.C.Opt.opt_pcm #t) (array_small_to_large_f t base_len from to sq x (from `size_add` h)) (Ghost.reveal frame (from `size_add` h))
      )
    );
  assert (composable (array_pcm t (z)) x frame_small);
  array_pcm_carrier_ext t z (op (array_pcm t (z)) x frame_small) v_small (fun i ->
    assert (op (Steel.C.Opt.opt_pcm #t) (array_small_to_large_f t base_len from to sq x (from `size_add` i)) (Ghost.reveal frame (from `size_add` i)) == v (from `size_add` i))
  );
  compatible_intro (array_pcm t (z)) x v_small frame_small

let array_conn_fpu_refine
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (x: Ghost.erased (array_pcm_carrier t (to `size_sub` from)) { ~ (Ghost.reveal x == one (array_pcm t (to `size_sub` from))) })
  (v: frame_preserving_upd_dom (array_pcm t base_len) (array_small_to_large_f t base_len from to sq x))
: Lemma
  (
    let z = size_sub to from in
    let v_small : array_pcm_carrier t z = array_large_to_small_f t base_len from to sq v in
    p_refine (array_pcm t (z)) v_small
  )
=
  let z = size_sub to from in
  let v_small : array_pcm_carrier t z = array_large_to_small_f t base_len from to sq v in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (exists (x: array_domain t z) . True)
  then ()
  else assert (Ghost.reveal x `feq` one (array_pcm t z))

let overwrite_array_slice
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (v: array_pcm_carrier t base_len)
  (v_small' : array_pcm_carrier t (to `size_sub` from))
: Tot (array_pcm_carrier t base_len)
=
    on_dom (array_domain t base_len) (fun (k: array_domain t base_len) ->
      if from `size_le` k && not (to `size_le` k)
      then begin
        let sq2 : squash (size_v k >= size_v from) = assert (size_v k >= size_v from) in
        v_small' (size_sub' k from sq2) <: option t
      end
      else v k
    )

let overwrite_array_slice_index
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (v: array_pcm_carrier t base_len)
  (v_small' : array_pcm_carrier t (to `size_sub` from))
  (k: array_domain t base_len)
: Lemma (
    overwrite_array_slice t base_len from to sq v v_small' k == (
    if size_v from <= size_v k && size_v k < size_v to
    then v_small' (k `size_sub` from)
    else v k
  ))
= ()

let overwrite_array_slice_index_in
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (v: array_pcm_carrier t base_len)
  (v_small' : array_pcm_carrier t (to `size_sub` from))
  (k: array_domain t base_len)
: Lemma
  (requires (
    size_v from <= size_v k /\ size_v k < size_v to
  ))
  (ensures (
    overwrite_array_slice t base_len from to sq v v_small' k == v_small' (k `size_sub` from)
  ))
= ()

let overwrite_array_slice_index_out
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from: size_t)
  (to: size_t)
  (sq: squash (
    size_v from <= size_v to /\
    size_v to <= size_v base_len
  ))
  (v: array_pcm_carrier t base_len)
  (v_small' : array_pcm_carrier t (to `size_sub` from))
  (k: array_domain t base_len)
: Lemma
  (requires (
    ~ (size_v from <= size_v k /\ size_v k < size_v to)
  ))
  (ensures (
    overwrite_array_slice t base_len from to sq v v_small' k == v k
  ))
= ()

let overwrite_array_slice_id
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (v: array_pcm_carrier t base_len)
  (v_small' : array_pcm_carrier t base_len)
: Lemma
  (overwrite_array_slice t base_len zero_size base_len () v v_small' == v_small')
= array_pcm_carrier_ext t base_len
    (overwrite_array_slice t base_len zero_size base_len () v v_small')
    v_small'
    (fun i -> ())

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
  array_conn_fpu_compatible t base_len from to sq x v;
  array_conn_fpu_refine t base_len from to sq x v;
  let v_small' : array_pcm_carrier t z = f v_small in
  overwrite_array_slice t base_len from to sq v v_small'

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
  Steel.C.Connection.mkconnection1
    (array_small_to_large t base_len from to sq)
    (array_large_to_small t base_len from to sq)
    (array_small_to_large_to_small t base_len from to sq)
    (array_conn_fpu_f t base_len from to sq)
    (fun x y f v -> assume False)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2 --query_stats --z3cliopt smt.arith.nl=false"
#restart-solver

let array_conn_fpu_eq
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
  (f: Steel.C.Connection.restricted_frame_preserving_upd (array_pcm t (to `size_sub` from)) x y)
  (v: frame_preserving_upd_dom (array_pcm t base_len) (array_small_to_large_f t base_len from to sq x))  
: Lemma
  (let open Steel.C.Connection in
  ((array_conn t base_len from to sq).conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v == array_conn_fpu_f t base_len from to sq x y f v)
= ()

#restart-solver

let connection_eq_gen
  #a (#p: pcm a) #b1 (#q1: pcm b1) (c1: p `Steel.C.Connection.connection` q1)
  #b2 (#q2: pcm b2) (c2: p `Steel.C.Connection.connection` q2)
  (sq: squash (
    b1 == b2 /\
    q1 == q2 /\
    c1.conn_small_to_large.morph `feq` c2.conn_small_to_large.morph /\
    c1.conn_large_to_small.morph `feq` c2.conn_large_to_small.morph
  ))
  (phi:
    (x1: Ghost.erased b1 { ~ (Ghost.reveal x1 == one q1) }) ->
    (y1: Ghost.erased b1) ->
    (f1: Steel.C.Connection.restricted_frame_preserving_upd q1 x1 y1) ->
    (v1: frame_preserving_upd_dom p (c1.conn_small_to_large.morph x1)) ->
    (x2: Ghost.erased b2 { ~ (Ghost.reveal x2 == one q2) }) ->
    (y2: Ghost.erased b2) ->
    (f2: Steel.C.Connection.restricted_frame_preserving_upd q2 x2 y2) ->
    (v2: frame_preserving_upd_dom p (c2.conn_small_to_large.morph x2)) ->
    (sq': squash (
      x1 == x2 /\
      y1 == y2 /\
      f1 == f2 /\
      v1 == v2
    )) ->
    Tot
    (squash ((c1.conn_lift_frame_preserving_upd Steel.C.Connection.({ fpu_lift_dom_x = x1; fpu_lift_dom_y = y1; fpu_lift_dom_f = f1 })).fpu_f v1 == (c2.conn_lift_frame_preserving_upd Steel.C.Connection.({ fpu_lift_dom_x = x2; fpu_lift_dom_y = y2; fpu_lift_dom_f = f2 })).fpu_f v2))
  )
: Lemma
  (c1 == c2)
= Steel.C.Connection.connection_eq_gen c1 c2 () (fun x y f v -> phi x y f v x y f v ())

#restart-solver
let array_conn_id
  (t: Type0)
  (base_len: Ghost.erased size_t)
: Lemma
  (array_conn t base_len (mk_size_t (FStar.UInt32.uint_to_t 0)) base_len () == Steel.C.Connection.connection_id (array_pcm t base_len))
= let z = mk_size_t (FStar.UInt32.uint_to_t 0) in
  assert (forall x . array_small_to_large_f t base_len z base_len () x `feq` x);
  assert (forall x . array_small_to_large_f t base_len z base_len () x == x);
  assert (forall x . array_large_to_small_f t base_len z base_len () x `feq` x);
  assert (forall x . array_large_to_small_f t base_len z base_len () x == x);
  let c = array_conn t base_len z base_len () in
  connection_eq_gen
    c
    (Steel.C.Connection.connection_id (array_pcm t base_len))
    ()
    (fun x1 y1 f1 v1 x2 y2 f2 v2 sq12 ->
      let v_small : array_pcm_carrier t base_len = array_large_to_small_f t base_len z base_len () v1 in
      assert (v_small == v1);
      array_conn_fpu_compatible t base_len z base_len () x1 v1;
      array_conn_fpu_refine t base_len z base_len () x1 v1;
      let v_small' : array_pcm_carrier t base_len = f1 v1 in
      overwrite_array_slice_id t base_len v1 v_small';
      let s' : array_pcm_carrier t base_len = overwrite_array_slice t base_len z base_len () v1 v_small' in
      assert (array_conn_fpu_f t base_len z base_len () x1 y1 f1 v1 == s');
      assert (s' == f1 v1);
      assert ((c.Steel.C.Connection.conn_lift_frame_preserving_upd Steel.C.Connection.({ fpu_lift_dom_x = x1; fpu_lift_dom_y = y1; fpu_lift_dom_f = f1; })).Steel.C.Connection.fpu_f v1 == array_conn_fpu_f t base_len z base_len () x1 y1 f1 v1);
      Steel.C.Connection.connection_id_fpu (array_pcm t base_len) x2 y2 f2 v2;
      assert (((Steel.C.Connection.connection_id (array_pcm t base_len)).conn_lift_frame_preserving_upd Steel.C.Connection.({ fpu_lift_dom_x = x2; fpu_lift_dom_y = y2; fpu_lift_dom_f = f2; })).Steel.C.Connection.fpu_f v2 == f2 v2);
      ()
    )

let ifthenelse_prf
  (p: prop)
  (cond: bool)
  (iftrue: squash (cond == true) -> Lemma p)
  (iffalse: squash (cond == false) -> Lemma p)
: Lemma p
= if cond
  then iftrue ()
  else iffalse ()

#restart-solver
let array_conn_compose_morphisms
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from1: size_t)
  (to1: size_t)
  (from2: size_t)
  (to2: size_t)
  (h: squash (
    size_v from1 <= size_v to1 /\
    size_v to1 <= size_v base_len /\
    size_v from2 <= size_v to2 /\
    size_v from1 + size_v to2 <= size_v to1
  ))
: Tot (squash (
      let z = to1 `size_sub` from1 in
      let c1 = array_conn t base_len from1 to1 () in
      let c2 = array_conn t z from2 to2 () in
      let cc = c1 `Steel.C.Connection.connection_compose` c2 in
      let c = array_conn t base_len (from1 `size_add` from2) (from1 `size_add` to2) () in
      cc.conn_small_to_large.morph `feq` c.conn_small_to_large.morph /\
      cc.conn_large_to_small.morph `feq` c.conn_large_to_small.morph
  ))
=
  let z = to1 `size_sub` from1 in
  let sz = size_sub (size_add from1 to2) (size_add from1 from2) in
  let _ : squash (sz == size_sub to2 from2) = () in
  assert (forall x . array_small_to_large_f t base_len from1 to1 () (array_small_to_large_f t z from2 to2 ()  x) `feq` array_small_to_large_f t base_len (from1 `size_add` from2) (from1 `size_add` to2) () x);
  assert (forall x . array_large_to_small_f t z from2 to2 () (array_large_to_small_f t base_len from1 to1 () x) `feq` array_large_to_small_f t base_len (from1 `size_add` from2) (from1 `size_add` to2) () x)

#push-options "--print_implicits --z3rlimit 256"

let size_sub_size_add_l
  (from1: size_t)
  (to1: size_t)
  (from2: size_t)
  (to2: size_t)
  (sq: squash (
    size_v from1 <= size_v to1 /\
    size_v from2 <= size_v to2 /\
    size_v from1 + size_v to2 <= size_v to1
  ))
: Lemma
  ((from1 `size_add` to2) `size_sub` (from1 `size_add` from2) == to2 `size_sub` from2)
= ()

let size_sub_size_sub
  (from1: size_t)
  (to1: size_t)
  (from2: size_t)
  (to2: size_t)
  (i: size_t)
  (sq: squash (
    size_v from1 <= size_v to1 /\
    size_v from1 + size_v to2 <= size_v to1 /\
    size_v from1 + size_v from2 <= size_v i /\
    size_v i <= size_v from1 + size_v to2
  ))
: Lemma
  ((i `size_sub` from1) `size_sub` from2 == i `size_sub` (from1 `size_add` from2))
= ()

let array_large_to_small_f_compose
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from1: size_t)
  (to1: size_t)
  (from2: size_t)
  (to2: size_t)
  (sq: squash (
    size_v from1 <= size_v to1 /\
    size_v to1 <= size_v base_len /\
    size_v from2 <= size_v to2 /\
    size_v from1 + size_v to2 <= size_v to1
  ))
  (a: array_pcm_carrier t base_len)
: Lemma
  (array_large_to_small_f t (to1 `size_sub` from1) from2 to2 () (array_large_to_small_f t base_len from1 to1 () a) ==
    array_large_to_small_f t base_len (from1 `size_add` from2) (from1 `size_add` to2) () a)
= assert (
  (array_large_to_small_f t (to1 `size_sub` from1) from2 to2 () (array_large_to_small_f t base_len from1 to1 () a) `feq`
    array_large_to_small_f t base_len (from1 `size_add` from2) (from1 `size_add` to2) () a)
  )

#restart-solver
let array_conn_compose_fpu
  (t: Type0)
  (base_len: Ghost.erased size_t)
  (from1: size_t)
  (to1: size_t)
  (from2: size_t)
  (to2: size_t)
  (sq: squash (
    size_v from1 <= size_v to1 /\
    size_v to1 <= size_v base_len /\
    size_v from2 <= size_v to2 /\
    size_v from1 + size_v to2 <= size_v to1
  ))
  (x: Ghost.erased (array_pcm_carrier t (to2 `size_sub` from2)) {~ (Ghost.reveal x == one (array_pcm t (to2 `size_sub` from2)))})
  (y: Ghost.erased (array_pcm_carrier t (to2 `size_sub` from2)))
  (f: frame_preserving_upd (array_pcm t (to2 `size_sub` from2)) x y)
  (x2: Ghost.erased (array_pcm_carrier t (to1 `size_sub` from1)))
  (sqx2: squash (
    Ghost.reveal x2 == array_small_to_large_f t (to1 `size_sub` from1) from2 to2 () x /\
    (~ (Ghost.reveal x2 == one (array_pcm t (to1 `size_sub` from1))))
  ))
  (y2: Ghost.erased (array_pcm_carrier t (to1 `size_sub` from1)))
  (sqy2: squash (
    Ghost.reveal y2 == array_small_to_large_f t (to1 `size_sub` from1) from2 to2 () y
  ))
  (f2: frame_preserving_upd (array_pcm t (to1 `size_sub` from1)) x2 y2)
  (sqf2: (
    (v: frame_preserving_upd_dom (array_pcm t (to1 `size_sub` from1)) x2) ->
    Lemma
    (f2 v == array_conn_fpu_f t (to1 `size_sub` from1) from2 to2 () x y f v)
  ))
  (x0: Ghost.erased (array_pcm_carrier t base_len))
  (sqx0: squash (
    Ghost.reveal x0 == array_small_to_large_f t base_len (from1 `size_add` from2) (from1 `size_add` to2) () x /\
    Ghost.reveal x0 == array_small_to_large_f t base_len from1 to1 () x2 /\
    (~ (Ghost.reveal x0 == one (array_pcm t base_len)))
  ))
  (v: frame_preserving_upd_dom (array_pcm t base_len) x0)
: Lemma
  (ensures (
    array_conn_fpu_f t base_len from1 to1 () x2 y2 f2 v == array_conn_fpu_f t base_len (from1 `size_add` from2) (from1 `size_add` to2) () x y f v
  ))
= let al : array_pcm_carrier t base_len = array_conn_fpu_f t base_len from1 to1 () x2 y2 f2 v in
  array_conn_fpu_compatible t base_len from1 to1 () x2 v;
  array_conn_fpu_refine t base_len from1 to1 () x2 v;
  let sz1 = to1 `size_sub` from1 in
  let v_l_out_small : array_pcm_carrier t sz1 = array_large_to_small_f t base_len from1 to1 () v in
  sqf2 v_l_out_small;
  array_conn_fpu_compatible t sz1 from2 to2 () x v_l_out_small;
  array_conn_fpu_refine t sz1 from2 to2 () x v_l_out_small;
  let sz2 = to2 `size_sub` from2 in
  let v_l_in_small : array_pcm_carrier t sz2 = array_large_to_small_f t sz1 from2 to2 () v_l_out_small in
  let v_l_in_small' : array_pcm_carrier t sz2 = f v_l_in_small in
  let v_l_in' : array_pcm_carrier t sz1 = overwrite_array_slice t sz1 from2 to2 () v_l_out_small v_l_in_small' in
  let v_l' : array_pcm_carrier t base_len = overwrite_array_slice t base_len from1 to1 () v v_l_in' in
  assert (v_l' == al);
  let from = from1 `size_add` from2 in
  let to = from1 `size_add` to2 in
  let _ : squash (sz2 == to `size_sub` from) = size_sub_size_add_l from1 to1 from2 to2 () in
  let ar : array_pcm_carrier t base_len = array_conn_fpu_f t base_len from to () x y f v in
  array_conn_fpu_compatible t base_len from to () x v;
  array_conn_fpu_refine t base_len from to () x v;
  let v_r_small : array_pcm_carrier t sz2 = array_large_to_small_f t base_len from to () v in
  let _ : squash (v_r_small == v_l_in_small) = array_large_to_small_f_compose t base_len from1 to1 from2 to2 () v in
  let v_r_small' : array_pcm_carrier t sz2 = f v_r_small in
  assert (v_r_small' == v_l_in_small');
  let v_r' : array_pcm_carrier t base_len = overwrite_array_slice t base_len from to () v v_r_small' in
  assert (v_r' == ar);
  array_pcm_carrier_ext t base_len v_l' v_r' (fun i ->
    overwrite_array_slice_index t base_len from1 to1 () v v_l_in' i;
    overwrite_array_slice_index t base_len from to () v v_r_small' i;
    if size_v from1 <= size_v i && size_v i < size_v to1
    then begin
      let i' : array_domain t sz1 = i `size_sub` from1 in
      let b = (size_v from2 <= size_v i' && size_v i' < size_v to2) in
      assert ((size_v (from1 `size_add` from2) <= size_v i && size_v i < size_v (from1 `size_add` to2)) == b);
      overwrite_array_slice_index t sz1 from2 to2 () v_l_out_small v_l_in_small' i';
      if size_v from2 <= size_v i' && size_v i' < size_v to2
      then begin
        size_sub_size_sub from1 to1 from2 to2 i ()
      end else begin
        assert (f2 v_l_out_small i' == v_l_out_small i');
        array_large_to_small_f_eq' t base_len from1 to1 () v i
      end
    end else begin
      assert ((size_v (from1 `size_add` from2) <= size_v i && size_v i < size_v (from1 `size_add` to2)) == false)
    end
  )

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
  let sz = size_sub (size_add from1 to2) (size_add from1 from2) in
  let _ : squash (sz == size_sub to2 from2) = () in
  let c1 = array_conn t base_len from1 to1 () in
  let c2 = array_conn t z from2 to2 () in
  let cc = c1 `Steel.C.Connection.connection_compose` c2 in
  let c = array_conn t base_len (from1 `size_add` from2) (from1 `size_add` to2) () in
  let sq : squash (
      cc.conn_small_to_large.morph `feq` c.conn_small_to_large.morph /\
      cc.conn_large_to_small.morph `feq` c.conn_large_to_small.morph
  ) =
    array_conn_compose_morphisms t base_len from1 to1 from2 to2 ()
  in
  Steel.C.Connection.connection_eq_gen cc c sq (fun x y f v ->
    let open Steel.C.Connection in
    let x' : Ghost.erased (array_pcm_carrier t z) = c2.conn_small_to_large.morph x in
    let y' : Ghost.erased (array_pcm_carrier t z) = c2.conn_small_to_large.morph y in
    let phi = mk_restricted_frame_preserving_upd (c2.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })) in
    connection_compose_fpu
      c1
      c2
      x y f
      phi;
    array_conn_fpu_eq t base_len from1 to1 () x' y' phi v;
    array_conn_fpu_eq t base_len (from1 `size_add` from2) (from1 `size_add` to2) () x y f v;
    array_conn_compose_fpu
      t base_len from1 to1 from2 to2 ()
      x y f
      x' () y' ()
      phi
      (fun v' ->
        array_conn_fpu_eq t z from2 to2 () x y f v'
      )
      (cc.conn_small_to_large.morph x)
      ()
      v
  )


#pop-options

#restart-solver

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

let array_as_ref_conn
  (#base: Type)
  (#t: Type)
  (a: array base t)
: Tot (Steel.C.Connection.connection (array_pcm t a.base_len) (array_pcm t (len a)))
= array_conn t a.base_len a.from a.to a.prf

let array_as_ref
  (#base: Type)
  (#t: Type)
  (a: array base t)
: GTot (Steel.C.Reference.ref base (array_view_type t (len a)) (array_pcm t (len a)))
= Steel.C.Ref.ref_focus a.base_ref (array_as_ref_conn a)

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

let gsplit r i = 
  let (rl, rr) = tsplit r i in
  GPair rl rr

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

let pts_to_split t n x i =
  let z = mk_size_t 0ul in
  let xl = array_small_to_large_f t n z i () (array_large_to_small_f t n z i () x) in
  let xr = array_small_to_large_f t n i n () (array_large_to_small_f t n i n () x) in
  assert (composable (array_pcm t n) xl xr);
  assert (op (array_pcm t n) xl xr `feq` x)

val to_carrier_split
  (t: Type)
  (n: size_t)
  (x: array_pcm_carrier t n)
  (v: array_view_type t n)
  (i: size_t)
: Lemma
  (requires (
    size_v i <= size_v n /\
    (array_view' t n).Steel.C.Ref.to_carrier v == x
  ))
  (ensures (
    let z = mk_size_t 0ul in
    let xl = (array_large_to_small_f t n z i () x) in
    let xr = (array_large_to_small_f t n i n () x) in
    (array_view' t i).Steel.C.Ref.to_carrier (Seq.slice v 0 (size_v i)) == xl /\
    (array_view' t (n `size_sub` i)).Steel.C.Ref.to_carrier (Seq.slice v (size_v i) (size_v n)) == xr
  ))

#push-options "--z3rlimit 32"
#restart-solver

let to_carrier_split t n x v i =
    let z = mk_size_t 0ul in
    let xl = (array_large_to_small_f t n z i () x) in
    let xr = (array_large_to_small_f t n i n () x) in
    assert ((array_view' t i).Steel.C.Ref.to_carrier (Seq.slice v 0 (size_v i)) `feq` xl);
    assert ((array_view' t (n `size_sub` i)).Steel.C.Ref.to_carrier (Seq.slice v (size_v i) (size_v n)) `feq` xr)

let array_as_ref_split_left
  (base: Type)
  (t: Type)
  (x: array base t)
  (i: size_t)
: Lemma
  (requires (size_v i <= length x))
  (ensures (
    array_as_ref (fst (tsplit x i)) == Steel.C.Ref.ref_focus (array_as_ref x) (array_conn t (len x) zero_size i ())
  ))
= array_conn_compose t x.base_len x.from x.to zero_size i;
  Steel.C.Ref.ref_focus_comp x.base_ref (array_as_ref_conn x) (array_conn t (len x) zero_size i ())

let array_as_ref_split_right
  (base: Type)
  (t: Type)
  (x: array base t)
  (i: size_t)
: Lemma
  (requires (size_v i <= length x))
  (ensures (
    array_as_ref (snd (tsplit x i)) == Steel.C.Ref.ref_focus (array_as_ref x) (array_conn t (len x) i (len x) ())
  ))
= array_conn_compose t x.base_len x.from x.to i (len x);
  Steel.C.Ref.ref_focus_comp x.base_ref (array_as_ref_conn x) (array_conn t (len x) i (len x) ())

val split' (#opened: _) (#base: Type) (#t:Type) (a:array base t) (i:size_t)
  : SteelGhost (array base t `gpair` array base t) opened
          (varray a)
          (fun res -> varray (GPair?.fst res) `star` varray (GPair?.snd res))
          (fun _ -> size_v i <= length a)
          (fun h res h' ->
            let s = h (varray a) in
            let sl = h' (varray (GPair?.fst res)) in
            let sr = h' (varray (GPair?.snd res)) in
            size_v i <= length a /\
            res == gsplit a i /\
            sl == Seq.slice s 0 (size_v i) /\
            sr == Seq.slice s (size_v i) (length a)
          )

let split'
  #j #base #t x i
=
  let gv = gget (varray x) in
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
  pts_to_split t (len x) v i;
  let (xl, xr) = tsplit x i in
  let n = len x in
  let z = mk_size_t 0ul in
  let vl' : array_pcm_carrier t (len xl) = array_large_to_small_f t n z i () v in
  let vl : array_pcm_carrier t (len x) = array_small_to_large_f t n z i () vl' in
  let vr' : array_pcm_carrier t (len xr) = array_large_to_small_f t n i n () v in
  let vr : array_pcm_carrier t (len x) = array_small_to_large_f t n i n () vr' in
  Steel.C.Ref.split
    (array_as_ref #base #t x)
    v
    vl
    vr;
  let cl : (cl: Steel.C.Connection.connection
    (array_pcm t (len x))
    (array_pcm t (len xl)) {
      cl === array_conn t n z i ()
    })
  = magic () // array_conn t n z i ()  // FIXME: WHY WHY WHY does this send F* off rails (> 35 GB RAM consumption and going)
  in
  Steel.C.Ref.gfocus
    (array_as_ref #base #t x)
    cl
    vl
    vl';
  array_as_ref_split_left _ t x i;
  assert (array_as_ref xl == Steel.C.Ref.ref_focus (array_as_ref x) cl);
  change_equal_slprop
    (_ `Steel.C.Ref.pts_to` vl')
    (array_as_ref xl `Steel.C.Ref.pts_to` vl');
  to_carrier_split t n v gv i;
  let gvl : array_view_type t (len xl) = Seq.slice gv 0 (size_v i) in
  Steel.C.Ref.pts_to_view_intro
    #j
    #base
    #(array_pcm_carrier t (len xl))
    #(array_pcm t (len xl))
    (array_as_ref xl)
    vl'
    #(array_view_type t (len xl))
    #(size_v (len xl) = 0)
    (array_view' t (len xl))
    gvl;
  change_equal_slprop // necessary, otherwise F* goes off rails
    (array_as_ref xl `Steel.C.Ref.pts_to_view` _)
    (varray0 xl);
  intro_varray1 xl;
  let cr : (cr: Steel.C.Connection.connection
    (array_pcm t (len x))
    (array_pcm t (len xr)) {
      cr === array_conn t n i n ()
    })
  = magic () // array_conn t n i n ()  // FIXME: WHY WHY WHY does this send F* off rails (> 35 GB RAM consumption and going)
  in
  Steel.C.Ref.gfocus
    (array_as_ref #base #t x)
    cr
    vr
    vr';
  array_as_ref_split_right _ t x i;
  assert (array_as_ref xr == Steel.C.Ref.ref_focus (array_as_ref x) cr);
  change_equal_slprop
    (_ `Steel.C.Ref.pts_to` vr')
    (array_as_ref xr `Steel.C.Ref.pts_to` vr');
  let gvr : array_view_type t (len xr) = Seq.slice gv (size_v i) (size_v n) in
//  let _ : squash ((Ghost.reveal gv <: Seq.seq t) == gvl `Seq.append` gvr) =
//    Seq.lemma_split gv (size_v i)
//  in
  Steel.C.Ref.pts_to_view_intro
    #j
    #base
    #(array_pcm_carrier t (len xr))
    #(array_pcm t (len xr))
    (array_as_ref xr)
    vr'
    #(array_view_type t (len xr))
    #(size_v (len xr) = 0)
    (array_view' t (len xr))
    gvr;
  change_equal_slprop // necessary, otherwise F* goes off rails
    (array_as_ref xr `Steel.C.Ref.pts_to_view` _)
    (varray0 xr);
  intro_varray1 xr;
  let res = GPair xl xr in
  change_equal_slprop
    (varray xl)
    (varray (GPair?.fst res));
  change_equal_slprop
    (varray xr)
    (varray (GPair?.snd res));
  res

let split
  #_ #_ #t a i
=
  let g = gget (varray a) in
  Seq.lemma_split #t (Ghost.reveal g) (size_v i);
  split' a i

let split_left
  a i
=
  return (fst (tsplit a i))

let split_right
  a i
=
  return (snd (tsplit a i))

let join' = admit ()

let joinc
  al ar
=
  return (t_merge al ar)

let array_as_one_ref_iso
  (base: Type)
  (t: Type)
: Tot (Steel.C.Connection.isomorphism (array_pcm t one_size) (Steel.C.Opt.opt_pcm #t))
= let c1 = (Steel.C.Struct.struct_to_field (array_elements_pcm t one_size) zero_size) in
  let c2 = (Steel.C.Struct.field_to_struct (array_elements_pcm t one_size) zero_size) in
  Steel.C.Connection.mkisomorphism
    c1
    c2
    ()
    (Steel.C.Connection.is_inverse_of_intro
      c2.Steel.C.Connection.morph
      c1.Steel.C.Connection.morph
      (fun x ->
        array_pcm_carrier_ext t one_size (c2.Steel.C.Connection.morph (c1.Steel.C.Connection.morph x)) x (fun i ->
          ()
        )
      )
    )
    (fun x -> ())
    (fun x -> ())

let array_as_one_ref_conn
  (base: Type)
  (t: Type)
: Tot (Steel.C.Connection.connection (array_pcm t one_size) (Steel.C.Opt.opt_pcm #t))
= Steel.C.Connection.connection_of_isomorphism (array_as_one_ref_iso base t)

let g_ref_of_array
  #base #t r
=
  array_as_ref r `Steel.C.Ref.ref_focus` array_as_one_ref_conn base t

let array_as_one_ref_conn'
  (#base: Type) (#t:Type0) (r:array base t)
: Pure (Steel.C.Connection.connection (array_pcm t r.base_len) (Steel.C.Opt.opt_pcm #t))
  (requires (length r == 1))
  (ensures (fun _ -> True))
=
  array_conn t r.base_len r.from r.to () `Steel.C.Connection.connection_compose` array_as_one_ref_conn base t

let array_as_one_ref_conn'_small_to_large
  (#base: Type) (#t:Type0) (r:array base t)
  (x: option t)
  (i: array_domain t r.base_len)
: Lemma
  (requires (length r == 1))
  (ensures ((array_as_one_ref_conn' r).Steel.C.Connection.conn_small_to_large.Steel.C.Connection.morph x i == (if i = r.from then x else None)))
= ()

let g_ref_of_array'
  (#base: Type) (#t:Type0) (r:array base t)
: Ghost (Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t))
  (requires (length r == 1))
  (ensures (fun _ -> True))
= r.base_ref `Steel.C.Ref.ref_focus` array_as_one_ref_conn' r

let g_ref_of_array'_correct
  (#base: Type) (#t:Type0) (r:array base t)
: Lemma
  (requires (length r == 1))
  (ensures (g_ref_of_array r == g_ref_of_array' r))
=
  Steel.C.Ref.ref_focus_comp r.base_ref (array_conn t r.base_len r.from r.to ()) (array_as_one_ref_conn base t)

let get_pts_to
  (#inames: _)
  (#a: Type u#0) (#b: Type u#b) (#p: Steel.C.PCM.pcm b)
  (r: Steel.C.Ref.ref a p) (v: Ghost.erased b)
: SteelGhost (Ghost.erased b) inames
    (Steel.C.Ref.pts_to r v)
    (fun _ -> Steel.C.Ref.pts_to r v)
    (fun _ -> True)
    (fun _ v' _ -> v' == v)
= noop(); v

(*
assume
val abstract_id
  (#t: Type)
  (x: t)
: Pure t
  (requires True)
  (ensures (fun y -> x == y))
*)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2 --query_stats --z3cliopt smt.arith.nl=false --print_implicits"

#restart-solver
let ref_of_array_ghost #inames #base #t x sq =
  let gv = gget (varray x) in
  elim_varray1 x;
  let v : Ghost.erased (array_pcm_carrier t (len x)) = Steel.C.Ref.pts_to_view_elim
    #inames
    #base
    #(array_pcm_carrier t (len x))
    #(array_pcm t (len x))
    (array_as_ref #base #t x)
    #(array_view_type t (len x))
    #(size_v (len x) = 0)
    (array_view' t (len x))
  in
  assert (len x == one_size);
  let z : array_domain t one_size = zero_size in
  assert (Ghost.reveal v `feq` (array_as_one_ref_conn base t).Steel.C.Connection.conn_small_to_large.Steel.C.Connection.morph (Ghost.reveal v z));
  Steel.C.Ref.gfocus
    #base
    #(array_pcm_carrier t (len x))
    #(option t)
    #_
    #(array_pcm t (len x))
    (array_as_ref x)
    #(Steel.C.Opt.opt_pcm #t)
    (array_as_one_ref_conn base t)
    _
    (Ghost.reveal v z);
  Steel.C.Ref.pts_to_view_intro
    _
    _
    (Steel.C.Opt.opt_view t)
    (Ghost.hide (Seq.index (Ghost.reveal gv <: Seq.seq t) 0));
  change_equal_slprop
    (Steel.C.Ref.pts_to_view _ _)
    (Steel.C.Ref.pts_to_view (g_ref_of_array x) (Steel.C.Opt.opt_view t))

#restart-solver
let ref_of_array #base #t x =
  let gv = gget (varray x) in
  elim_varray1 x;
  let v = Steel.C.Ref.pts_to_view_elim
    #_
    #base
    #(array_pcm_carrier t (len x))
    #(array_pcm t (len x))
    (array_as_ref #base #t x)
    #(array_view_type t (len x))
    #(size_v (len x) = 0)
    (array_view' t (len x))
  in
  Steel.C.Ref.unfocus _ x.base_ref (array_conn t x.base_len x.from x.to ()) _;
  let s = get_pts_to x.base_ref _ in
  let ar : Ghost.erased (array_pcm_carrier t x.base_len) = Ghost.hide ((array_as_one_ref_conn' x).Steel.C.Connection.conn_small_to_large.Steel.C.Connection.morph (Ghost.reveal v zero_size)) in
  array_pcm_carrier_ext t x.base_len (Ghost.reveal s) (Ghost.reveal ar) (fun i ->
    array_as_one_ref_conn'_small_to_large x (Ghost.reveal v zero_size) i
  );
  g_ref_of_array'_correct x;
  let r = Steel.C.Ref.focus x.base_ref (array_as_one_ref_conn' x) s (Ghost.reveal v zero_size) in
  Steel.C.Ref.pts_to_view_intro
    _
    _
    (Steel.C.Opt.opt_view t)
    (Ghost.hide (Seq.index (Ghost.reveal gv <: Seq.seq t) 0));
  return r

let array_of_ref = admit ()

let mk_array_of_ref = admit ()

#pop-options

let seq_equal_1
  (t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (requires (
    Seq.length s1 == 1 /\
    Seq.length s2 == 1 /\
    Seq.index s1 0 == Seq.index s2 0
  ))
  (ensures (s1 == s2))
= assert (s1 `Seq.equal` s2)

#push-options "--z3rlimit 128 --fuel 1 --ifuel 2 --query_stats --z3cliopt smt.arith.nl=false"
#restart-solver

let index
  #_ #t r i
=
  let rr = split_right r i in
  let rs = split r i in
  change_equal_slprop
    (varray (GPair?.snd rs))
    (varray rr);
  let rrl = split_left rr one_size in
  let rrs = split rr one_size in
  change_equal_slprop
    (varray (GPair?.fst rrs))
    (varray rrl);
  let grl = gget (varray rrl) in
  let r0 = ref_of_array rrl in
  let res = Steel.C.Opt.ref_opt_read r0 in
  array_of_ref rrl r0;
  let grl' = gget (varray rrl) in
  seq_equal_1 t (Ghost.reveal grl) (Ghost.reveal grl');
  let rr' = join' rrl (GPair?.snd rrs) in
  let r' = join' (GPair?.fst rs) rr' in
  change_equal_slprop
    (varray r')
    (varray r);
  return res

let seq_append_append_upd
  (t: Type)
  (i: nat)
  (x: t)
  (s1 s2 s2' s3: Seq.seq t)
: Lemma
  (requires (
    Seq.length s1 == i /\
    Seq.length s2 == 1 /\
    Seq.length s2' == 1 /\
    Seq.index s2' 0 == x
  ))
  (ensures (
    s1 `Seq.append` (s2' `Seq.append` s3) == Seq.upd (s1 `Seq.append` (s2 `Seq.append` s3)) i x
  ))
= assert (
    (s1 `Seq.append` (s2' `Seq.append` s3)) `Seq.equal` (Seq.upd (s1 `Seq.append` (s2 `Seq.append` s3)) i x)
  )

let upd
  #_ #t r i x
=
  let rr = split_right r i in
  let rs = split r i in
  let s1 = gget (varray (GPair?.fst rs)) in
  change_equal_slprop
    (varray (GPair?.snd rs))
    (varray rr);
  let rrl = split_left rr one_size in
  let rrs = split rr one_size in
  let s3 = gget (varray (GPair?.snd rrs)) in
  change_equal_slprop
    (varray (GPair?.fst rrs))
    (varray rrl);
  let s2 = gget (varray rrl) in
  let r0 = ref_of_array rrl in
  Steel.C.Opt.ref_opt_write r0 x;
  array_of_ref rrl r0;
  let s2' = gget (varray rrl) in
  seq_append_append_upd t (size_v i) x s1 s2 s2' s3;
  let rr' = join' rrl (GPair?.snd rrs) in
  let r' = join' (GPair?.fst rs) rr' in
  change_equal_slprop
    (varray r')
    (varray r)
