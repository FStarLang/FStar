module Steel.C.Array.Base

module S = Steel.C.Model.Struct

#push-options "--smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"
let half_perm
  (p: Steel.FractionalPermission.perm)
: Pure Steel.FractionalPermission.perm
  (requires True)
  (ensures (fun y ->
    y `Steel.FractionalPermission.sum_perm` y == p /\
    y == Steel.FractionalPermission.half_perm p
  ))
= 
  let open Steel.FractionalPermission in
  let open FStar.Real in
  assert ((p.v /. 2.0R) +. (p.v /. 2.0R) == p.v);
  MkPerm (p.v /. 2.0R)
#pop-options

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
: Tot (Steel.C.Model.PCM.pcm (array_range t n x))
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
: Tot (Steel.C.Model.Ref.sel_view (array_elements_pcm t n k) (array_elements_view_type t n k) false)
= Steel.C.Opt.opt_view _

let intro_array_view_init
  (t: Type u#0)
  (n: size_t)
  (x: restricted_t (Steel.C.Model.Ref.refine (array_domain t n) (S.mem (included_indices t n))) (array_elements_view_type t n))
  (k: nat { k < size_v n })
: Tot t
= x (int_to_size_t k)

let intro_array_view
  (t: Type u#0)
  (n: size_t)
  (x: restricted_t (Steel.C.Model.Ref.refine (array_domain t n) (S.mem (included_indices t n))) (array_elements_view_type t n))
: Tot (array_view_type t n)
= Seq.init (size_v n) (intro_array_view_init t n x)

let array_to_view
  (t: Type u#0)
  (n: size_t)
  (x: Steel.C.Model.Ref.refine (array_pcm_carrier t n) (S.struct_view_to_view_prop (array_elements_view t n) (included_indices t n)))
: Tot (array_view_type t n)
= intro_array_view t n (S.struct_view_to_view (array_elements_view t n) (included_indices t n) x)

let elim_array_view_f
  (t: Type u#0)
  (n: size_t)
  (x: array_view_type t n)
  (k: Steel.C.Model.Ref.refine (array_domain t n) (S.mem (included_indices t n)))
: Tot (array_elements_view_type t n k)
= Seq.index x (size_v k)

let elim_array_view
  (t: Type u#0)
  (n: size_t)
  (x: array_view_type t n)
: Tot (restricted_t (Steel.C.Model.Ref.refine (array_domain t n) (S.mem (included_indices t n))) (array_elements_view_type t n))
= on_dom (Steel.C.Model.Ref.refine (array_domain t n) (S.mem (included_indices t n))) (elim_array_view_f t n x)

let array_to_carrier
  (t: Type u#0)
  (n: size_t)
  (x: array_view_type t n)
: Tot (Steel.C.Model.Ref.refine (array_pcm_carrier t n) (S.struct_view_to_view_prop (array_elements_view t n) (included_indices t n)))
= S.struct_view_to_carrier (array_elements_view t n) (included_indices t n) (elim_array_view t n x)

open Steel.C.Model.PCM

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
  : Tot (Steel.C.Model.Ref.sel_view (array_pcm t n) (array_view_type t n) (size_v n = 0))
=
  let open Steel.C.Model.Ref in
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
type array_from0 t = {
  base_len: Ghost.erased size_t;
  base_ref: Steel.C.Reference.ref (array_view_type t base_len) (array_pcm t base_len);
  from: size_t;
  perm_ref: Steel.Reference.ghost_ref unit;
}

[@@erasable]
noeq
type array_to0 = {
  to: size_t;
  perm_val: Steel.FractionalPermission.perm;
}

let array0_spec
  (#t: _)
  (from: array_from0 t)
  (to: array_to0)
: Tot prop
=
    size_v from.base_len >= 0 /\
    size_v from.from <= size_v to.to /\
    size_v to.to <= size_v from.base_len

let array_or_null_from t = option (array_from0 t)
let array_or_null_to t = Ghost.erased (option array_to0)
let array_or_null_spec (from, to) =
  None? from == None? to /\
  ((Some? from \/ Some? to) ==> array0_spec (Some?.v from) (Some?.v to))

let len (from, to) =
  match from with
  | Some from ->
    let Some to = Ghost.reveal to in to.to `size_sub` from.from
  | _ -> zero_size

let null_from _ = None
let null_to _ = None
let null_to_unique _ = ()

let g_is_null a = None? (fst a)

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
: Tot (Steel.C.Model.Connection.morphism #(array_pcm_carrier t base_len) #(array_pcm_carrier t (to `size_sub` from))  (array_pcm t base_len) (array_pcm t (to `size_sub` from)))
= Steel.C.Model.Connection.mkmorphism
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
: Tot (Steel.C.Model.Connection.morphism (array_pcm t (to `size_sub` from))  (array_pcm t base_len))
= Steel.C.Model.Connection.mkmorphism
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
  (array_large_to_small_f t base_len from to sq `Steel.C.Model.Connection.is_inverse_of` array_small_to_large_f t base_len from to sq)
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
: Steel.C.Model.Connection.connection
    (array_pcm t base_len)
    (array_pcm t (to `size_sub` from))
=
  Steel.C.Model.Connection.mkconnection1
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
  (f: Steel.C.Model.Connection.restricted_frame_preserving_upd (array_pcm t (to `size_sub` from)) x y)
  (v: frame_preserving_upd_dom (array_pcm t base_len) (array_small_to_large_f t base_len from to sq x))  
: Lemma
  (let open Steel.C.Model.Connection in
  ((array_conn t base_len from to sq).conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v == array_conn_fpu_f t base_len from to sq x y f v)
= ()

#restart-solver

let connection_eq_gen
  #a (#p: pcm a) #b1 (#q1: pcm b1) (c1: p `Steel.C.Model.Connection.connection` q1)
  #b2 (#q2: pcm b2) (c2: p `Steel.C.Model.Connection.connection` q2)
  (sq: squash (
    b1 == b2 /\
    q1 == q2 /\
    c1.conn_small_to_large.morph `feq` c2.conn_small_to_large.morph /\
    c1.conn_large_to_small.morph `feq` c2.conn_large_to_small.morph
  ))
  (phi:
    (x1: Ghost.erased b1 { ~ (Ghost.reveal x1 == one q1) }) ->
    (y1: Ghost.erased b1) ->
    (f1: Steel.C.Model.Connection.restricted_frame_preserving_upd q1 x1 y1) ->
    (v1: frame_preserving_upd_dom p (c1.conn_small_to_large.morph x1)) ->
    (x2: Ghost.erased b2 { ~ (Ghost.reveal x2 == one q2) }) ->
    (y2: Ghost.erased b2) ->
    (f2: Steel.C.Model.Connection.restricted_frame_preserving_upd q2 x2 y2) ->
    (v2: frame_preserving_upd_dom p (c2.conn_small_to_large.morph x2)) ->
    (sq': squash (
      x1 == x2 /\
      y1 == y2 /\
      f1 == f2 /\
      v1 == v2
    )) ->
    Tot
    (squash ((c1.conn_lift_frame_preserving_upd Steel.C.Model.Connection.({ fpu_lift_dom_x = x1; fpu_lift_dom_y = y1; fpu_lift_dom_f = f1 })).fpu_f v1 == (c2.conn_lift_frame_preserving_upd Steel.C.Model.Connection.({ fpu_lift_dom_x = x2; fpu_lift_dom_y = y2; fpu_lift_dom_f = f2 })).fpu_f v2))
  )
: Lemma
  (c1 == c2)
= Steel.C.Model.Connection.connection_eq_gen c1 c2 () (fun x y f v -> phi x y f v x y f v ())

#restart-solver
let array_conn_id
  (t: Type0)
  (base_len: Ghost.erased size_t)
: Lemma
  (array_conn t base_len (mk_size_t (FStar.UInt32.uint_to_t 0)) base_len () == Steel.C.Model.Connection.connection_id (array_pcm t base_len))
= let z = mk_size_t (FStar.UInt32.uint_to_t 0) in
  assert (forall x . array_small_to_large_f t base_len z base_len () x `feq` x);
  assert (forall x . array_small_to_large_f t base_len z base_len () x == x);
  assert (forall x . array_large_to_small_f t base_len z base_len () x `feq` x);
  assert (forall x . array_large_to_small_f t base_len z base_len () x == x);
  let c = array_conn t base_len z base_len () in
  connection_eq_gen
    c
    (Steel.C.Model.Connection.connection_id (array_pcm t base_len))
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
      assert ((c.Steel.C.Model.Connection.conn_lift_frame_preserving_upd Steel.C.Model.Connection.({ fpu_lift_dom_x = x1; fpu_lift_dom_y = y1; fpu_lift_dom_f = f1; })).Steel.C.Model.Connection.fpu_f v1 == array_conn_fpu_f t base_len z base_len () x1 y1 f1 v1);
      Steel.C.Model.Connection.connection_id_fpu (array_pcm t base_len) x2 y2 f2 v2;
      assert (((Steel.C.Model.Connection.connection_id (array_pcm t base_len)).conn_lift_frame_preserving_upd Steel.C.Model.Connection.({ fpu_lift_dom_x = x2; fpu_lift_dom_y = y2; fpu_lift_dom_f = f2; })).Steel.C.Model.Connection.fpu_f v2 == f2 v2);
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
      let cc = c1 `Steel.C.Model.Connection.connection_compose` c2 in
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
    array_conn t base_len from1 to1 () `Steel.C.Model.Connection.connection_compose` array_conn t (to1 `size_sub` from1) from2 to2 () ==
    array_conn t base_len (from1 `size_add` from2) (from1 `size_add` to2) ()
  ))
=
  let z = to1 `size_sub` from1 in
  let sz = size_sub (size_add from1 to2) (size_add from1 from2) in
  let _ : squash (sz == size_sub to2 from2) = () in
  let c1 = array_conn t base_len from1 to1 () in
  let c2 = array_conn t z from2 to2 () in
  let cc = c1 `Steel.C.Model.Connection.connection_compose` c2 in
  let c = array_conn t base_len (from1 `size_add` from2) (from1 `size_add` to2) () in
  let sq : squash (
      cc.conn_small_to_large.morph `feq` c.conn_small_to_large.morph /\
      cc.conn_large_to_small.morph `feq` c.conn_large_to_small.morph
  ) =
    array_conn_compose_morphisms t base_len from1 to1 from2 to2 ()
  in
  Steel.C.Model.Connection.connection_eq_gen cc c sq (fun x y f v ->
    let open Steel.C.Model.Connection in
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

let array__base_len
  (#t: _)
  (a: array t)
: GTot size_t
= (Some?.v (fst a)).base_len

let array__base_ref
  (#t: _)
  (a: array t)
: Tot (Steel.C.Reference.ref (array_view_type t (array__base_len a)) (array_pcm t (array__base_len a)))
= (Some?.v (fst a)).base_ref

let array__from
  (#t: _)
  (a: array t)
: Tot size_t
= (Some?.v (fst a)).from

let array__to
  (#t: _)
  (a: array t)
: GTot size_t
= (Some?.v (snd a)).to

let array__perm_ref
  (#t: _)
  (a: array t)
: Tot (Steel.Reference.ghost_ref unit)
= (Some?.v (fst a)).perm_ref

let array__perm_val
  (#t: _)
  (a: array t)
: Tot Steel.FractionalPermission.perm
= (Some?.v (snd a)).perm_val

let array_as_ref_conn
  (#t: Type)
  (a: array t)
: GTot (Steel.C.Model.Connection.connection (array_pcm t (array__base_len a)) (array_pcm t (len a)))
= array_conn t (array__base_len a) (array__from a) (array__to a) ()

let array_as_ref
  (#t: Type)
  (a: array t)
: GTot (Steel.C.Reference.ref (array_view_type t (len a)) (array_pcm t (len a)))
= Steel.C.Model.Ref.ref_focus (array__base_ref a) (array_as_ref_conn a)

[@@__steel_reduce__]
let varray0
  (#t: Type)
  (x: array t)
: Tot vprop
= Steel.C.Model.Ref.pts_to_view
    #(array_pcm_carrier t (len x))
    #(array_pcm t (len x))
    (array_as_ref #t x)
    #(array_view_type t (len x))
    #(size_v (len x) = 0)
    (array_view' t (len x))

[@@__steel_reduce__]
let varray9
  (#t: Type)
  (x: array t)
: Tot vprop
= (varray0 x `star` Steel.Reference.ghost_vptrp (array__perm_ref x)  (array__perm_val x)) `vrewrite` fst

let varray_hp #t x = hp_of (varray9 #t x)

#push-options "--debug Steel.C.Array --debug_level Extreme"

let varray_sel #t x = sel_of (varray9 #t x)

#pop-options

let intro_varray1
  (#inames: _)
  (#t: Type)
  (x: array t)
: SteelGhost unit inames
    (varray0 x `star` Steel.Reference.ghost_vptrp (array__perm_ref x) (array__perm_val x))
    (fun _ -> varray x)
    (fun _ -> True)
    (fun h _ h' -> h' (varray x) == h (varray0 x))
= intro_vrewrite
    (varray0 x `star` Steel.Reference.ghost_vptrp (array__perm_ref x) (array__perm_val x))
    fst;
  change_slprop_rel
    ((varray0 x `star` Steel.Reference.ghost_vptrp (array__perm_ref x) (array__perm_val x)) `vrewrite` fst)
    (varray x)
    (fun u v -> u == v)
    (fun m -> ())

let elim_varray1
  (#inames: _)
  (#t: Type)
  (x: array t)
: SteelGhost unit inames
    (varray x)
    (fun _ -> varray0 x `star` Steel.Reference.ghost_vptrp (array__perm_ref x) (array__perm_val x))
    (fun _ -> True)
    (fun h _ h' -> h' (varray0 x) == h (varray x))
= change_slprop_rel
    (varray x)
    ((varray0 x `star` Steel.Reference.ghost_vptrp (array__perm_ref x) (array__perm_val x)) `vrewrite` fst)
    (fun u v -> u == v)
    (fun m -> ());
  elim_vrewrite
    (varray0 x `star` Steel.Reference.ghost_vptrp (array__perm_ref x) (array__perm_val x))
    fst

let g_mk_array_from'
  (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref (array_view_type t n) (array_pcm t n))
  (a: array_or_null_from t)
: Tot prop
= 
  Some? a /\
  size_v n > 0 /\
  begin let a = Some?.v a in
  Ghost.reveal a.base_len == n /\
  a.base_ref == r /\
  a.from == mk_size_t 0ul
  end

let g_mk_array #t #n r a =
  g_mk_array_from' r (fst a) /\
  (array__to a) == n /\
  (array__perm_val a) == Steel.FractionalPermission.full_perm

let g_mk_array_weak r a = ()

let g_mk_array_from r a = g_mk_array_from' r a

let g_mk_array_to #t #n r a
=
  Some ({
    to = n;
    perm_val = Steel.FractionalPermission.full_perm
  })

#push-options "--z3rlimit 32"

val intro_varray0 (#t: Type u#0) (#opened: _) (#n: size_t) (r: Steel.C.Reference.ref (array_view_type t n) (array_pcm t n))
  (_: squash (size_v n > 0))
: SteelAtomicBase (array t)
    false opened Unobservable
    (Steel.C.Model.Ref.pts_to_view r (array_view t n))
    (fun a -> varray a)
    (requires fun _ -> True)
  (ensures (fun h a h' ->
    g_mk_array r a /\
    snd a == g_mk_array_to r (fst a) /\
    h' (varray a) == h (Steel.C.Model.Ref.pts_to_view r (array_view t n))
  ))

let intro_varray0
  #t #_ #n r sq
=
  let perm_ref = Steel.Reference.ghost_alloc #unit () in
  let from = Some ({
    base_len = n;
    base_ref = r;
    from = mk_size_t 0ul;
    perm_ref = perm_ref;
  }) in
  let res = (from, g_mk_array_to r from) in
  change_equal_slprop
    (Steel.Reference.ghost_vptr perm_ref)
    (Steel.Reference.ghost_vptrp (array__perm_ref res) (array__perm_val res));
  assert ((array_as_ref res <: Steel.C.Model.Ref.ref (array_pcm t n)) == Steel.C.Model.Ref.ref_focus r (array_conn t n (mk_size_t 0ul) n ()));
  array_conn_id t n;
  assert (array_conn t n (mk_size_t 0ul) n () == Steel.C.Model.Connection.connection_id (array_pcm t n));
  assert (array_as_ref res == Steel.C.Model.Ref.ref_focus r (Steel.C.Model.Connection.connection_id (array_pcm t n)));
  Steel.C.Model.Ref.ref_focus_id r;
  assert (Steel.C.Model.Ref.ref_focus r (Steel.C.Model.Connection.connection_id (array_pcm t n)) == r);
  assert (array_as_ref res == r);
  change_equal_slprop
    (r `Steel.C.Model.Ref.pts_to_view` _)
    (varray0 res);
  intro_varray1 res;
  return res

let intro_varray_from r _ =
  let a = intro_varray0 r () in
  let res = fst a in
  change_equal_slprop
    (varray a)
    (varray (res, g_mk_array_to r res));
  return res

let elim_varray
  #_ #t #n r res sq
=
  assert (g_mk_array r res);
  assert (array_as_ref res == Steel.C.Model.Ref.ref_focus r (array_conn t n (mk_size_t 0ul) n ()));
  array_conn_id t n;
  assert (array_conn t n (mk_size_t 0ul) n () == Steel.C.Model.Connection.connection_id (array_pcm t n));
  assert (array_as_ref res == Steel.C.Model.Ref.ref_focus r (Steel.C.Model.Connection.connection_id (array_pcm t n)));
  Steel.C.Model.Ref.ref_focus_id r;
  assert (Steel.C.Model.Ref.ref_focus r (Steel.C.Model.Connection.connection_id (array_pcm t n)) == r);
  assert (array_as_ref res == r);
  elim_varray1 res;
  change_equal_slprop
    (varray0 res)
    (r `Steel.C.Model.Ref.pts_to_view` _);
  let perm_ref = (array__perm_ref res) in
  change_equal_slprop
    (Steel.Reference.ghost_vptrp ((array__perm_ref res)) ((array__perm_val res)))
    (Steel.Reference.ghost_vptr perm_ref);
  Steel.Reference.ghost_free perm_ref

#pop-options

let adjacent r1 r2 =
  (array__base_len r1) == (array__base_len r2) /\
  (array__base_ref r1) == (array__base_ref r2) /\
  (array__perm_ref r1) == (array__perm_ref r2) /\
  (array__to r1) == (array__from r2)

val t_merge
  (#t: Type)
  (r1 r2: array t)
: Pure (array t)
  (requires (adjacent r1 r2))
  (ensures (fun r -> length r == length r1 + length r2))

let t_merge r1 r2 =
  (fst r1, Ghost.hide (Some ({
    to = (array__to r2);
    perm_val = (array__perm_val r1) `Steel.FractionalPermission.sum_perm` (array__perm_val r2);
  })))

let merge r1 r2 = t_merge r1 r2

let merge_assoc r1 r2 r3 = ()

let merge_inj_right a b1 b2 = ()

let merge_inj_left a1 a2 b = ()

let no_self_merge_1 (#t: Type) (a b: array t) : Lemma
  (~ (merge_into a b a))
= let aux () : Lemma
    (requires (merge_into a b a))
    (ensures False)
  = assert (
      let open Steel.FractionalPermission in
      let open FStar.Real in
      (array__perm_val a).v +. (array__perm_val b).v >. (array__perm_val a).v
    )
  in
  Classical.move_requires aux ()

let no_self_merge_2 (#t: Type) (a b: array t) : Lemma
  (~ (merge_into a b b))
= let aux () : Lemma
    (requires (merge_into a b a))
    (ensures False)
  = assert (
      let open Steel.FractionalPermission in
      let open FStar.Real in
      (array__perm_val a).v +. (array__perm_val b).v >. (array__perm_val b).v
    )
  in
  Classical.move_requires aux ()

val tsplit
  (#t: Type)
  (r: array t)
  (i: size_t)
: Pure (array t & array t)
  (requires (size_v i <= length r))
  (ensures (fun (rl, rr) ->
    merge_into rl rr r /\
    length rl == size_v i
  ))

let tsplit #t r i =
  let h = half_perm (array__perm_val r) in
  let r1 : array t =
    (fst r, Ghost.hide (Some ({
      to = (array__from r) `size_add` i;
      perm_val = h;
    })))
  in
  let r2 : array t = (Some ({
    base_len = (array__base_len r);
    base_ref = (array__base_ref r);
    from = (array__from r) `size_add` i;
    perm_ref = (array__perm_ref r);
  }), Ghost.hide (Some ({
    to = (array__to r);
    perm_val = h;
  })))
  in
  (r1, r2)

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
    (array_view' t n).Steel.C.Model.Ref.to_carrier v == x
  ))
  (ensures (
    let z = mk_size_t 0ul in
    let xl = (array_large_to_small_f t n z i () x) in
    let xr = (array_large_to_small_f t n i n () x) in
    (array_view' t i).Steel.C.Model.Ref.to_carrier (Seq.slice v 0 (size_v i)) == xl /\
    (array_view' t (n `size_sub` i)).Steel.C.Model.Ref.to_carrier (Seq.slice v (size_v i) (size_v n)) == xr
  ))

#push-options "--z3rlimit 32"
#restart-solver

let to_carrier_split t n x v i =
    let z = mk_size_t 0ul in
    let xl = (array_large_to_small_f t n z i () x) in
    let xr = (array_large_to_small_f t n i n () x) in
    assert ((array_view' t i).Steel.C.Model.Ref.to_carrier (Seq.slice v 0 (size_v i)) `feq` xl);
    assert ((array_view' t (n `size_sub` i)).Steel.C.Model.Ref.to_carrier (Seq.slice v (size_v i) (size_v n)) `feq` xr)

let array_as_ref_split_left
  (t: Type)
  (x: array t)
  (i: size_t)
: Lemma
  (requires (size_v i <= length x))
  (ensures (
    array_as_ref (fst (tsplit x i)) == Steel.C.Model.Ref.ref_focus (array_as_ref x) (array_conn t (len x) zero_size i ())
  ))
=
  array_conn_compose t (array__base_len x) (array__from x) (array__to x) zero_size i;
  Steel.C.Model.Ref.ref_focus_comp (array__base_ref x) (array_as_ref_conn x) (array_conn t (len x) zero_size i ())

#restart-solver
let array_as_ref_split_right
  (t: Type)
  (x: array t)
  (i: size_t)
: Lemma
  (requires (size_v i <= length x))
  (ensures (
    array_as_ref (snd (tsplit x i)) == Steel.C.Model.Ref.ref_focus (array_as_ref x) (array_conn t (len x) i (len x) ())
  ))
=
  array_conn_compose t (array__base_len x) (array__from x) (array__to x) i (len x);
  Steel.C.Model.Ref.ref_focus_comp (array__base_ref x) (array_as_ref_conn x) (array_conn t (len x) i (len x) ())

val split_ (#opened: _) (#t:Type) (a:array t) (i:size_t)
  : SteelGhost (array t `gpair` array t) opened
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

#pop-options
#push-options "--z3rlimit 128"

#restart-solver
let split_
  #j #t x i
=
  let gv = gget (varray x) in
  elim_varray1 x;
  let v = Steel.C.Model.Ref.pts_to_view_elim
    #j
    #(array_pcm_carrier t (len x))
    #(array_pcm t (len x))
    (array_as_ref #t x)
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
  Steel.C.Model.Ref.split
    (array_as_ref #t x)
    v
    vl
    vr;
  let cl : (cl: Steel.C.Model.Connection.connection
    (array_pcm t (len x))
    (array_pcm t (len xl)) {
      cl === array_conn t n z i ()
    })
  = magic () // array_conn t n z i ()  // FIXME: WHY WHY WHY does this send F* off rails (> 35 GB RAM consumption and going)
  in
  Steel.C.Model.Ref.gfocus
    (array_as_ref #t x)
    cl
    vl
    vl';
  array_as_ref_split_left t x i;
  assert (array_as_ref xl == Steel.C.Model.Ref.ref_focus (array_as_ref x) cl);
  change_equal_slprop
    (_ `Steel.C.Model.Ref.pts_to` vl')
    (array_as_ref xl `Steel.C.Model.Ref.pts_to` vl');
  to_carrier_split t n v gv i;
  let gvl : array_view_type t (len xl) = Seq.slice gv 0 (size_v i) in
  Steel.C.Model.Ref.pts_to_view_intro
    #j
    #(array_pcm_carrier t (len xl))
    #(array_pcm t (len xl))
    (array_as_ref xl)
    vl'
    #(array_view_type t (len xl))
    #(size_v (len xl) = 0)
    (array_view' t (len xl))
    gvl;
  change_equal_slprop // necessary, otherwise F* goes off rails
    (array_as_ref xl `Steel.C.Model.Ref.pts_to_view` _)
    (varray0 xl);
  Steel.Reference.ghost_share (array__perm_ref x);
  change_equal_slprop
    (Steel.Reference.ghost_vptrp (array__perm_ref x) (Steel.FractionalPermission.half_perm (array__perm_val x)))
    (Steel.Reference.ghost_vptrp (array__perm_ref xl) (array__perm_val xl));
  intro_varray1 xl;
  let cr : (cr: Steel.C.Model.Connection.connection
    (array_pcm t (len x))
    (array_pcm t (len xr)) {
      cr === array_conn t n i n ()
    })
  = magic () // array_conn t n i n ()  // FIXME: WHY WHY WHY does this send F* off rails (> 35 GB RAM consumption and going)
  in
  Steel.C.Model.Ref.gfocus
    (array_as_ref #t x)
    cr
    vr
    vr';
  array_as_ref_split_right t x i;
  assert (array_as_ref xr == Steel.C.Model.Ref.ref_focus (array_as_ref x) cr);
  change_equal_slprop
    (_ `Steel.C.Model.Ref.pts_to` vr')
    (array_as_ref xr `Steel.C.Model.Ref.pts_to` vr');
  let gvr : array_view_type t (len xr) = Seq.slice gv (size_v i) (size_v n) in
//  let _ : squash ((Ghost.reveal gv <: Seq.seq t) == gvl `Seq.append` gvr) =
//    Seq.lemma_split gv (size_v i)
//  in
  Steel.C.Model.Ref.pts_to_view_intro
    #j
    #(array_pcm_carrier t (len xr))
    #(array_pcm t (len xr))
    (array_as_ref xr)
    vr'
    #(array_view_type t (len xr))
    #(size_v (len xr) = 0)
    (array_view' t (len xr))
    gvr;
  change_equal_slprop // necessary, otherwise F* goes off rails
    (array_as_ref xr `Steel.C.Model.Ref.pts_to_view` _)
    (varray0 xr);
  change_equal_slprop
    (Steel.Reference.ghost_vptrp (array__perm_ref x) (Steel.FractionalPermission.half_perm (array__perm_val x)))
    (Steel.Reference.ghost_vptrp (array__perm_ref xr) (array__perm_val xr));
  intro_varray1 xr;
  let res = GPair xl xr in
  change_equal_slprop
    (varray xl)
    (varray (GPair?.fst res));
  change_equal_slprop
    (varray xr)
    (varray (GPair?.snd res));
  res

let split'
  #_ #t a i
=
  let g = gget (varray a) in
  Seq.lemma_split #t (Ghost.reveal g) (size_v i);
  split_ a i

let split_right_from
  a i
=
  return (fst (snd (tsplit a i)))

let join' = admit ()

let array_as_one_ref_iso
  (t: Type)
: Tot (Steel.C.Model.Connection.isomorphism (array_pcm t one_size) (Steel.C.Opt.opt_pcm #t))
= let c1 = (Steel.C.Model.Struct.struct_to_field (array_elements_pcm t one_size) zero_size) in
  let c2 = (Steel.C.Model.Struct.field_to_struct (array_elements_pcm t one_size) zero_size) in
  Steel.C.Model.Connection.mkisomorphism
    c1
    c2
    ()
    (Steel.C.Model.Connection.is_inverse_of_intro
      c2.Steel.C.Model.Connection.morph
      c1.Steel.C.Model.Connection.morph
      (fun x ->
        array_pcm_carrier_ext t one_size (c2.Steel.C.Model.Connection.morph (c1.Steel.C.Model.Connection.morph x)) x (fun i ->
          ()
        )
      )
    )
    (fun x -> ())
    (fun x -> ())

let array_as_one_ref_conn
  (t: Type)
: Tot (Steel.C.Model.Connection.connection (array_pcm t one_size) (Steel.C.Opt.opt_pcm #t))
= Steel.C.Model.Connection.connection_of_isomorphism (array_as_one_ref_iso t)

let g_ref_of_array
  #t r
=
  array_as_ref r `Steel.C.Model.Ref.ref_focus` array_as_one_ref_conn t

let array_as_one_ref_conn'
  (#t:Type0) (r:array t)
: Pure (Steel.C.Model.Connection.connection (array_pcm t (array__base_len r)) (Steel.C.Opt.opt_pcm #t))
  (requires (size_v (len r) == 1))
  (ensures (fun _ -> True))
=
  array_conn t (array__base_len r) (array__from r) ((array__from r) `size_add` one_size) () `Steel.C.Model.Connection.connection_compose` array_as_one_ref_conn t

#restart-solver
let array_as_one_ref_conn'_small_to_large
  (#t:Type0) (r:array t)
  (x: option t)
  (i: array_domain t (array__base_len r))
: Lemma
  (requires (size_v (len r) == 1))
  (ensures ((array_as_one_ref_conn' r).Steel.C.Model.Connection.conn_small_to_large.Steel.C.Model.Connection.morph x i == (if i = (array__from r) then x else None)))
= Steel.C.Model.Connection.morphism_compose_morph
    (array_as_one_ref_conn t).Steel.C.Model.Connection.conn_small_to_large
    (array_conn t (array__base_len r) (array__from r) (array__from r `size_add` one_size) ()).Steel.C.Model.Connection.conn_small_to_large
    x

let g_ref_of_array'
  (#t:Type0) (r:array t)
: Ghost (Steel.C.Reference.ref t (Steel.C.Opt.opt_pcm #t))
  (requires (size_v (len r) == 1))
  (ensures (fun _ -> True))
= (array__base_ref r) `Steel.C.Model.Ref.ref_focus` array_as_one_ref_conn' r

let g_ref_of_array'_correct
  (#t:Type0) (r:array t)
: Lemma
  (requires (length r == 1))
  (ensures (g_ref_of_array r == g_ref_of_array' r))
=
  Steel.C.Model.Ref.ref_focus_comp (array__base_ref r) (array_conn t (array__base_len r) (array__from r) (array__to r) ()) (array_as_one_ref_conn t)

let get_pts_to
  (#inames: _)
  (#b: Type u#b) (#p: Steel.C.Model.PCM.pcm b)
  (r: Steel.C.Model.Ref.ref p) (v: Ghost.erased b)
: SteelGhost (Ghost.erased b) inames
    (Steel.C.Model.Ref.pts_to r v)
    (fun v' -> Steel.C.Model.Ref.pts_to r v)
    (fun _ -> True)
    (fun _ v' _ -> v' == v)
= noop(); v

let v_ref_of_array r =
  Steel.Reference.ghost_vptrp (array__perm_ref r) (array__perm_val r)

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
let ref_of_array_ghost #inames #t x sq =
  let gv = gget (varray x) in
  elim_varray1 x;
  let v : Ghost.erased (array_pcm_carrier t (len x)) = Steel.C.Model.Ref.pts_to_view_elim
    #inames
    #(array_pcm_carrier t (len x))
    #(array_pcm t (len x))
    (array_as_ref #t x)
    #(array_view_type t (len x))
    #(size_v (len x) = 0)
    (array_view' t (len x))
  in
  assert (len x == one_size);
  let z : array_domain t one_size = zero_size in
  assert (Ghost.reveal v `feq` (array_as_one_ref_conn t).Steel.C.Model.Connection.conn_small_to_large.Steel.C.Model.Connection.morph (Ghost.reveal v z));
  Steel.C.Model.Ref.gfocus
    #(array_pcm_carrier t (len x))
    #(option t)
    #_
    #(array_pcm t (len x))
    (array_as_ref x)
    #(Steel.C.Opt.opt_pcm #t)
    (array_as_one_ref_conn t)
    _
    (Ghost.reveal v z);
  Steel.C.Model.Ref.pts_to_view_intro
    #inames
    #(option t)
    #(Steel.C.Opt.opt_pcm #t)
    (Steel.C.Model.Ref.ref_focus (array_as_ref x) (array_as_one_ref_conn t))
    (Ghost.reveal v z)
    #t
    #false
    (Steel.C.Opt.opt_view t)
    (Ghost.hide (Seq.index (Ghost.reveal gv <: Seq.seq t) 0));
  change_equal_slprop
    (Steel.C.Model.Ref.pts_to_view _ _)
    (Steel.C.Model.Ref.pts_to_view (g_ref_of_array x) (Steel.C.Opt.opt_view t))

#restart-solver
val ref_of_array0 (#t:Type0) (#opened: _) (r:array t) (sq: squash (length r == 1)) (v0: Ghost.erased t)
  : SteelAtomicBase (Steel.C.Reference.ref t (Steel.C.Opt.opt_pcm #t))
             false opened Unobservable
             (varray r)
             (fun r' -> (Steel.C.Model.Ref.pts_to_view r' (Steel.C.Opt.opt_view t) `vrefine` (fun v' -> v' == Ghost.reveal v0)) `star` pure (g_ref_of_array #t r == r') `star` v_ref_of_array r)
             (requires fun h0 -> Seq.index (h0 (varray r)) 0 == Ghost.reveal v0)
             (ensures fun h0 r' h1 -> True)

#restart-solver
let ref_of_array0 #t x sq v0 =
  let gv : Ghost.erased (array_view_type t (len x)) = gget (varray x) in
  assert (Seq.index (Ghost.reveal gv) 0 == Ghost.reveal v0);
  elim_varray1 x;
  let v : Ghost.erased (array_pcm_carrier t (len x)) = Steel.C.Model.Ref.pts_to_view_elim
    #_
    #(array_pcm_carrier t (len x))
    #(array_pcm t (len x))
    (array_as_ref #t x)
    #(array_view_type t (len x))
    #(size_v (len x) = 0)
    (array_view' t (len x))
  in
  Steel.C.Model.Ref.unfocus _ (array__base_ref x) (array_as_ref_conn x) _;
  let s = get_pts_to (array__base_ref x) _ in
  let ar : Ghost.erased (array_pcm_carrier t (array__base_len x)) = Ghost.hide ((array_as_one_ref_conn' x).Steel.C.Model.Connection.conn_small_to_large.Steel.C.Model.Connection.morph (Ghost.reveal v zero_size)) in
  array_pcm_carrier_ext t (array__base_len x) (Ghost.reveal s) (Ghost.reveal ar) (fun i ->
    array_as_one_ref_conn'_small_to_large x (Ghost.reveal v zero_size) i
  );
  g_ref_of_array'_correct x;
  let r : Steel.C.Reference.ref t (Steel.C.Opt.opt_pcm #t) = Steel.C.Model.Ref.focus (array__base_ref x) (array_as_one_ref_conn' x) s (Ghost.reveal v zero_size) in
  Steel.C.Model.Ref.pts_to_view_intro
    #_
    #(option t)
    #(Steel.C.Opt.opt_pcm #t)
    r
    (Ghost.reveal v zero_size)
    #t
    #false
    (Steel.C.Opt.opt_view t)
    (Ghost.hide (Seq.index (Ghost.reveal gv <: Seq.seq t) 0));
  intro_vrefine
    (Steel.C.Model.Ref.pts_to_view r (Steel.C.Opt.opt_view t))
    (fun v' -> v' == Ghost.reveal v0);
  intro_pure (g_ref_of_array #t x == r);
  return r

#restart-solver
let ref_of_array_from #t r_from r_to sq =
  let x : array t = (r_from, r_to) in
  change_equal_slprop
    (varray (r_from, r_to))
    (varray x);
  let gv : Ghost.erased (array_view_type t (len x)) = gget (varray x) in
  let v0 = Ghost.hide (Seq.index (Ghost.reveal gv) 0) in
  let r = ref_of_array0 x () v0 in
  elim_pure (g_ref_of_array x == r);
  elim_vrefine
    (Steel.C.Model.Ref.pts_to_view r (Steel.C.Opt.opt_view t))
    (fun v' -> v' == Ghost.reveal v0);
  change_equal_slprop
    (v_ref_of_array x)
    (v_ref_of_array (r_from, r_to));
  return r

#restart-solver
let array_of_ref
  #_ #t r' r sq
=
  let g : Ghost.erased t = gget (Steel.C.Model.Ref.pts_to_view r (Steel.C.Opt.opt_view t)) in
  let v = Steel.C.Model.Ref.pts_to_view_elim
    r
    (Steel.C.Opt.opt_view t)
  in
  Steel.C.Model.Ref.unfocus
    r
    (array_as_ref r')
    (array_as_one_ref_conn t)
    v;
  let g' : Ghost.erased (array_view_type t (len r')) =
    (Ghost.hide (Seq.create 1 (Ghost.reveal g)))
  in
  let v' : Ghost.erased (array_pcm_carrier t (len r')) =
    get_pts_to (array_as_ref r') _
  in
  array_pcm_carrier_ext t (len r') ((array_view t (len r')).Steel.C.Model.Ref.to_carrier g') (Ghost.reveal v') (fun i ->
    assert (i == zero_size)
  );
  Steel.C.Model.Ref.pts_to_view_intro
    _
    _
    (array_view t (len r'))
    g';
  change_equal_slprop
    (Steel.C.Model.Ref.pts_to_view (array_as_ref r') (array_view t (len r')))
    (varray0 r');
  intro_varray1 r'

#restart-solver
let one_ref_as_array_conn
  (t:Type0)
: Tot (Steel.C.Model.Connection.connection (Steel.C.Opt.opt_pcm #t) (array_pcm t one_size))
=
  Steel.C.Model.Connection.(connection_of_isomorphism (isomorphism_inverse (array_as_one_ref_iso t)))

let mk_array_of_ref' (#t:Type0) (r: Steel.C.Reference.ref t (Steel.C.Opt.opt_pcm #t)) (perm_ref: Steel.Reference.ghost_ref unit) : GTot (array t) =
  (Some ({
    base_len = one_size;
    base_ref = r `Steel.C.Model.Ref.ref_focus` one_ref_as_array_conn t;
    from = zero_size;
    perm_ref = perm_ref;
  }), Ghost.hide (Some ({
    to = one_size;
    perm_val = Steel.FractionalPermission.full_perm;
  })))

#restart-solver
let mk_array_of_ref'_correct
  (#t:Type0) (r: Steel.C.Reference.ref t (Steel.C.Opt.opt_pcm #t)) (perm_ref: Steel.Reference.ghost_ref unit)
: Lemma
  (g_ref_of_array (mk_array_of_ref' r perm_ref) == r)
=
  g_ref_of_array'_correct (mk_array_of_ref' r perm_ref);
  array_conn_id t one_size;
  Steel.C.Model.Connection.connection_compose_id_left (array_as_one_ref_conn t);
  Steel.C.Model.Ref.ref_focus_comp r (one_ref_as_array_conn t) (array_as_one_ref_conn t);
  Steel.C.Model.Connection.connection_of_isomorphism_inverse_left (array_as_one_ref_iso t);
  Steel.C.Model.Ref.ref_focus_id r

#restart-solver
let array_as_ref_eq_base_ref
  (#t:Type0) (a: array t)
: Lemma
  (requires (
    array__base_len a == one_size /\
    array__from a == zero_size /\
    array__to a == one_size
  ))
  (ensures (
    array_as_ref a == (array__base_ref a)
  ))
=
  array_conn_id t one_size;
  Steel.C.Model.Ref.ref_focus_id (array__base_ref a)

#restart-solver
let array_as_ref_mk_array_of_ref'
  (#t:Type0) (r: Steel.C.Reference.ref t (Steel.C.Opt.opt_pcm #t)) (perm_ref: Steel.Reference.ghost_ref unit)
: Lemma
  (ensures (
    let x = mk_array_of_ref' r perm_ref in
    array_as_ref x == (array__base_ref x)
  ))
=
  let x = mk_array_of_ref' r perm_ref in
  array_as_ref_eq_base_ref x

let array_domain_one_size
  (t: Type)
  (i: array_domain t one_size)
: Lemma
  (i == zero_size)
= ()

#restart-solver
let mk_array_of_ref_view_intro (#t:Type0)
  (g: Ghost.erased t)
  (v: Ghost.erased (option t))
  (v' : Ghost.erased (array_pcm_carrier t one_size))
  (g' : Ghost.erased (array_view_type t one_size))
: Lemma
  (requires (
    Ghost.reveal v == (Steel.C.Opt.opt_view t).Steel.C.Model.Ref.to_carrier (Ghost.reveal g) /\
    Ghost.reveal v' == (array_as_one_ref_conn t).Steel.C.Model.Connection.conn_small_to_large.Steel.C.Model.Connection.morph (Ghost.reveal v) /\
    Ghost.reveal g' == Seq.create 1 (Ghost.reveal g)
  ))
  (ensures (
    (array_view t one_size).Steel.C.Model.Ref.to_carrier g' == (Ghost.reveal v')
  ))
= array_pcm_carrier_ext t one_size ((array_view t one_size).Steel.C.Model.Ref.to_carrier g') (Ghost.reveal v') (fun i ->
    ()
  )

let mk_array_of_ref_to'
  (t:Type0)
: Tot (array_or_null_to t)
= Some ({
    to = one_size;
    perm_val = Steel.FractionalPermission.full_perm;
  })

let mk_array_of_ref_from_spec
  #t r from
=
  let a = (from, mk_array_of_ref_to' t) in
  array_or_null_spec a /\
  g_is_null a == false /\
  array__base_len a == one_size /\
  array__from a == zero_size /\
  array__base_ref a == r `Steel.C.Model.Ref.ref_focus` one_ref_as_array_conn t

let mk_array_of_ref_to #t r from = mk_array_of_ref_to' t

val mk_array_of_ref0 (#t:Type0) (#opened: _) (r: Steel.C.Reference.ref t (Steel.C.Opt.opt_pcm #t))
  : SteelAtomicBase (array t)
             false opened Unobservable
             (Steel.C.Model.Ref.pts_to_view r (Steel.C.Opt.opt_view t))
             (fun r' -> varray r')
             (requires fun _ -> True)
             (ensures fun h0 r' h1 ->
               let s = h1 (varray r') in
               Seq.length s == 1 /\
               g_ref_of_array r' == r /\
               r' == mk_array_of_ref' r (array__perm_ref r') /\
               h0 (Steel.C.Model.Ref.pts_to_view r (Steel.C.Opt.opt_view t)) == Seq.index s 0
             )

#restart-solver
let mk_array_of_ref0
  #t r
=
  let g : Ghost.erased t = gget (Steel.C.Model.Ref.pts_to_view r (Steel.C.Opt.opt_view t)) in
  let v : Ghost.erased (option t) = Steel.C.Model.Ref.pts_to_view_elim r (Steel.C.Opt.opt_view t) in
  let v' : Ghost.erased (array_pcm_carrier t one_size) = Ghost.hide ((array_as_one_ref_conn t).Steel.C.Model.Connection.conn_small_to_large.Steel.C.Model.Connection.morph (Ghost.reveal v)) in
  let _ : squash (Ghost.reveal v == (one_ref_as_array_conn t).Steel.C.Model.Connection.conn_small_to_large.Steel.C.Model.Connection.morph (Ghost.reveal v')) =
    Steel.C.Model.Connection.connection_of_isomorphism_inverse_left (array_as_one_ref_iso t)
  in
  let r' = Steel.C.Model.Ref.focus r (one_ref_as_array_conn t) v v' in
  let perm_ref = Steel.Reference.ghost_alloc #unit () in
  let res : array t = (Some ({
    base_len = one_size;
    base_ref = r';
    from = zero_size;
    perm_ref = perm_ref;
  }), Ghost.hide (Some ({
    to = one_size;
    perm_val = Steel.FractionalPermission.full_perm;
  })))
  in
  assert (res == mk_array_of_ref' r perm_ref);
  mk_array_of_ref'_correct r perm_ref;
  let g' : Ghost.erased (array_view_type t one_size) =
    Ghost.hide (Seq.create 1 (Ghost.reveal g))
  in
  mk_array_of_ref_view_intro g v v' g' ;
  Steel.C.Model.Ref.pts_to_view_intro
    _
    _
    (array_view t one_size)
    g';
  array_as_ref_mk_array_of_ref' r perm_ref;
  change_equal_slprop
    (Steel.C.Model.Ref.pts_to_view r' (array_view t one_size))
    (varray0 res);
  change_equal_slprop
    (Steel.Reference.ghost_vptr perm_ref)
    (Steel.Reference.ghost_vptrp (array__perm_ref res) (array__perm_val res));
  intro_varray1 res;
  return res

let mk_array_of_ref_from
  #t r
=
  let a = mk_array_of_ref0 r in
  let res = fst a in
  change_equal_slprop
    (varray a)
    (varray (res, mk_array_of_ref_to r res));
  return res

#pop-options

let varray_or_null0_rewrite
  (#a: Type0)
  (r: array_or_null a)
  (_: t_of emp)
: Tot (option (array_view_type a (len r)))
= None

[@@__steel_reduce__]
let varray_or_null0
  (#a: Type0)
  (r: array_or_null a)
: Tot vprop
= if g_is_null r
  then emp `vrewrite` varray_or_null0_rewrite r
  else varray r `vrewrite` Some

let is_array_or_null r = hp_of (varray_or_null0 r)
let array_or_null_sel r = sel_of (varray_or_null0 r)

let intro_varray_or_null_none x =
  intro_vrewrite emp (varray_or_null0_rewrite x);
  change_equal_slprop
    (emp `vrewrite` varray_or_null0_rewrite x)
    (varray_or_null0 x);
  change_slprop_rel
    (varray_or_null0 x)
    (varray_or_null x)
    (fun u v -> u == v)
    (fun _ -> ())

let intro_varray_or_null_some x =
  intro_vrewrite (varray x) Some;
  change_equal_slprop
    (varray x `vrewrite` Some)
    (varray_or_null0 x);
  change_slprop_rel
    (varray_or_null0 x)
    (varray_or_null x)
    (fun u v -> u == v)
    (fun _ -> ())

let elim_varray_or_null_some x =
  change_slprop_rel
    (varray_or_null x)
    (varray_or_null0 x)
    (fun u v -> u == v)
    (fun _ -> ());
  if g_is_null x
  then begin
    change_equal_slprop
      (varray_or_null0 x)
      (emp `vrewrite` varray_or_null0_rewrite x);
    elim_vrewrite emp (varray_or_null0_rewrite x);
    assert False;
    change_equal_slprop
      emp
      (varray x)
  end else begin
    change_equal_slprop
      (varray_or_null0 x)
      (varray x `vrewrite` Some);
    elim_vrewrite (varray x) Some
  end

let elim_varray_or_null_none x =
  change_slprop_rel
    (varray_or_null x)
    (varray_or_null0 x)
    (fun u v -> u == v)
    (fun _ -> ());
  if g_is_null x
  then begin
    change_equal_slprop
      (varray_or_null0 x)
      (emp `vrewrite` varray_or_null0_rewrite x);
    elim_vrewrite emp (varray_or_null0_rewrite x)
  end else begin
    change_equal_slprop
      (varray_or_null0 x)
      (varray x `vrewrite` Some);
    elim_vrewrite (varray x) Some;
    assert False;
    change_equal_slprop
      (varray x)
      emp
  end

#restart-solver
let freeable
  #t a
=
  Steel.C.Model.Ref.freeable (array__base_ref a) /\
  size_v (array__base_len a) > 0 /\
  (array__perm_val a) == Steel.FractionalPermission.full_perm /\
  (array__from a) == zero_size /\
  (array__to a) == (array__base_len a)

#restart-solver
let array_to_carrier_refine
  (#t: Type0)
  (n: size_t)
  (v: array_view_type t n)
: Lemma
  (requires (size_v n > 0))
  (ensures (p_refine (array_pcm t n) (array_to_carrier t n v)))
= FStar.Classical.exists_intro (fun (k: array_domain t n) -> True) zero_size

let malloc_to'
 (#t: Type0)
  (x: t)
  (n: size_t)
  (from: array_or_null_from t)
: Tot (array_or_null_to t)
= if None? from
  then None
  else Some ({
    to = n;
    perm_val = Steel.FractionalPermission.full_perm;
  })

let malloc_from_spec
  #t x n from
=
  let a = (from, malloc_to' x n from) in
  array_or_null_spec a /\
  (g_is_null a == false ==> freeable a)

let malloc_to x n from = malloc_to' x n from

val malloc0
  (#t: Type0)
  (x: t)
  (n: size_t)
: Steel (array_or_null t)
    emp
    (fun r -> varray_or_null r)
    (requires fun _ -> size_v n > 0)
    (ensures fun _ r h' ->
      size_v n > 0 /\
      malloc_from_spec x n (fst r) /\
      snd r == malloc_to x n (fst r) /\
      (g_is_null r == false ==> (freeable r /\ len r == n /\ h' (varray_or_null r) == Some (Seq.create (size_v n) x)))
    )

#restart-solver
let malloc0
  #t x n
=
  let v = Seq.create (size_v n) x in
  let c = array_to_carrier t n v in
  array_to_carrier_refine n v;
  let r0 = Steel.C.Model.Ref.ref_alloc (array_pcm t n) c in
  Steel.C.Model.Ref.pts_to_view_intro r0 c (array_view t n) v;
  let r = intro_varray r0 () in
  intro_varray_or_null_some r;
  return r

let malloc_from
  #t x n sq
= let a = malloc0 x n in
  let res = fst a in
  change_equal_slprop
    (varray_or_null a)
    (varray_or_null (res, malloc_to x n res));
  return res
 
val free0
  (#t: Type0)
  (a: array t)
: Steel unit
    (varray a)
    (fun _ -> emp)
    (requires (fun _ -> freeable a))
    (ensures (fun _ _ _ -> True))

#restart-solver
#push-options "--print_implicits"
let free0
  #t a
=
  let r = (array__base_ref a) in
  elim_varray r a ();
  let v = Steel.C.Model.Ref.pts_to_view_elim
    #_
    #(array_pcm_carrier t (Ghost.hide (Ghost.reveal (array__base_len a))))
    #(array_pcm t (Ghost.hide (Ghost.reveal (array__base_len a))))
    r
    (array_view t (array__base_len a))
  in
  Steel.C.Model.Ref.ref_free
    #(array_pcm_carrier t (Ghost.hide (Ghost.reveal (array__base_len a))))
    #(array_pcm t (Ghost.hide (Ghost.reveal (array__base_len a))))
    #v
    r

let free_from
  #t a a' sq
=
  let a0 : array t = (a, a') in
  change_equal_slprop
    (varray (a, a'))
    (varray a0);
  free0 a0

let is_null_from a a' sq =
  return (None? a)
