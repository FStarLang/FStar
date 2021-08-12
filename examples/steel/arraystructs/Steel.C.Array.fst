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

let array_view_type_sized t n' n = array_view_type t n

let unfold_array_view_type_sized t n' n = ()

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



(*
let array_as_ref
  (#base: Type)
  (#t: Type)
  (a: array base t)
: GTot (Steel.C.Reference.ref base (array_view_type t (len a)) (array_pcm t (len a)))

