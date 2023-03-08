module Steel.C.Model.Array

open Steel.C.Model.PCM
open Steel.C.Model.Connection
open Steel.C.Model.Ref
open Steel.C.Model.Struct
open Steel.Effect
module R = Steel.C.Model.Ref
module A = Steel.Effect.Atomic
module SZ = FStar.SizeT

(* Base array type *)

let size_t = SZ.t
let size_v = SZ.v

let array_domain
  (n: Ghost.erased size_t)
: Tot Type0
= (x: size_t { size_v x < size_v n })

let array_range
  (t: Type u#0)
  (n: Ghost.erased size_t)
  (x: array_domain n)
: Tot Type0
= t

open FStar.FunctionalExtensionality

let array_pcm_carrier
  (t: Type)
  (n: Ghost.erased size_t)
: Tot Type
= restricted_t (array_domain n) (array_range t n)

let array_pcm_carrier_ext
  (t: Type)
  (n: size_t)
  (x1 x2: array_pcm_carrier t n)
  (f: (
    (i: array_domain n) ->
    Lemma
    (x1 i == x2 i)
  ))
: Lemma
  (ensures (x1 == x2))
= Classical.forall_intro f;
  assert (x1 `feq` x2)

let array_elements_pcm
  (#t: Type u#0)
  (p: pcm t)
  (n: Ghost.erased size_t)
  (x: array_domain n)
: Tot (Steel.C.Model.PCM.pcm (array_range t n x))
= p

let array_pcm
  (#t: Type u#0)
  (p: pcm t)
  (n: Ghost.erased size_t)
: Tot (pcm (array_pcm_carrier t n))
= prod_pcm (array_elements_pcm p n)

noeq
type array
  (base_t: Type)
  (#t: Type)
  (p: pcm t)
= {
    base_len: Ghost.erased size_t;
    base: R.ref base_t (array_pcm p base_len);
    offset: size_t;
    len: Ghost.erased size_t;
    prf: squash (size_v offset + size_v len <= size_v base_len);
  }

let length
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (a: array base_t p)
: GTot nat
= size_v a.len

let adjacent
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (a1 a2: array base_t p)
: Tot prop
= a1.base_len == a2.base_len /\
  a1.base == a2.base /\
  size_v a1.offset + size_v a1.len == size_v a2.offset

let size_add = SZ.add

let merge
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (a1 a2: array base_t p)
: Pure (array base_t p)
    (requires (adjacent a1 a2))
    (ensures (fun y -> length y == length a1 + length a2))
= {
    base_len = a1.base_len;
    base = a1.base;
    offset = a1.offset;
    len = size_add a1.len a2.len;
    prf = ();
  }

let size_le = SZ.lte
let size_lt = SZ.lt
let size_sub = SZ.sub

let large_to_small_index
  (large_len: size_t)
  (offset: size_t)
  (small_len: size_t)
  (sq: squash (size_v offset + size_v small_len <= size_v large_len))
  (x: array_domain large_len)
: Tot (option (array_domain small_len))
= if if offset `size_le` x then x `size_lt` (offset `size_add` small_len) else false
  then Some (x `size_sub` offset)
  else None

let small_to_large_index
  (large_len: size_t)
  (offset: size_t)
  (small_len: size_t)
  (sq: squash (size_v offset + size_v small_len <= size_v large_len))
  (x: array_domain small_len)
: Tot (array_domain large_len)
= offset `size_add` x

let ref_of_array_conn
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
: GTot (connection (array_pcm p r.base_len) (array_pcm p r.len))
= substruct (array_elements_pcm p r.base_len) (array_elements_pcm p r.len) (small_to_large_index r.base_len r.offset r.len ()) (large_to_small_index r.base_len r.offset r.len ()) ()

let ref_of_array
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
: GTot (R.ref base_t (array_pcm p r.len))
= R.ref_focus r.base (ref_of_array_conn r)

let ref_of_array_id
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
: Lemma
  (requires (
    size_v r.offset == 0 /\
    r.len == r.base_len
  ))
  (ensures (
    ref_of_array r == r.base
  ))
= substruct_id (array_elements_pcm p r.len) (small_to_large_index r.base_len r.offset r.len ()) (large_to_small_index r.base_len r.offset r.len ()) ();
  R.ref_focus_id r.base

let array_pcm_carrier_of_seq
  (#t: Type)
  (n: Ghost.erased size_t)
  (s: Seq.lseq t (size_v n))
: Tot (array_pcm_carrier t n)
= on_dom (array_domain n) (fun i -> Seq.index s (size_v i) <: array_range t n i)

let array_pcm_carrier_of_seq_eq
  (#t: Type)
  (n: Ghost.erased size_t)
  (s: Seq.lseq t (size_v n))
  (i: array_domain n)
: Lemma
  (array_pcm_carrier_of_seq n s i == Seq.index s (SZ.v i))
  [SMTPat (array_pcm_carrier_of_seq n s i)]
= ()

let int_to_size_t = SZ.uint_to_t

let seq_of_array_pcm_carrier
  (#t: Type)
  (#n: Ghost.erased size_t)
  (x: array_pcm_carrier t n)
: GTot (Seq.lseq t (size_v n))
= Seq.init (size_v n) (fun i -> x (int_to_size_t i) <: t)

let array_pcm_carrier_of_seq_of_array_pcm_carrier
  (#t: Type)
  (#n: size_t)
  (x: array_pcm_carrier t n)
: Lemma
  (array_pcm_carrier_of_seq n (seq_of_array_pcm_carrier x) `feq` x)
= ()

let seq_of_array_pcm_carrier_of_seq
  (#t: Type)
  (n: Ghost.erased size_t)
  (s: Seq.lseq t (size_v n))
: Lemma
  (seq_of_array_pcm_carrier (array_pcm_carrier_of_seq n s) `Seq.equal` s)
= ()

let pts_to0
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (x: Seq.seq t)
: Tot vprop
= if Seq.length x = size_v r.len
  then R.pts_to (ref_of_array r) (array_pcm_carrier_of_seq r.len x)
  else pure False

let trivial_selector
  (hp: Steel.Memory.slprop u#1)
: Tot (selector unit hp)
= fun _ -> ()

[@@__steel_reduce__]
let pts_to
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (x: Seq.seq t)
: Tot vprop
= VUnit ({
    hp = hp_of (pts_to0 r x);
    t = unit;
    sel = trivial_selector _;
  })

let intro_pts_to'
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (x: Seq.lseq t (size_v r.len))
: A.SteelGhostT unit opened
   (R.pts_to (ref_of_array r) (array_pcm_carrier_of_seq r.len x))
   (fun _ -> pts_to r x)
= A.rewrite_slprop
    (R.pts_to (ref_of_array r) (array_pcm_carrier_of_seq r.len x))
    (pts_to r x)
    (fun _ -> ())

let intro_pts_to
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (s: array_pcm_carrier t r.len)
: A.SteelGhostT unit opened
   (R.pts_to (ref_of_array r) s)
   (fun _ -> pts_to r (seq_of_array_pcm_carrier s))
= array_pcm_carrier_of_seq_of_array_pcm_carrier s;
  A.change_equal_slprop (R.pts_to _ _) (R.pts_to _ _);
  intro_pts_to' r (seq_of_array_pcm_carrier s)

let intro_pts_to0
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (s: array_pcm_carrier t r.len)
  (s': Seq.seq t)
: A.SteelGhost unit opened
   (R.pts_to (ref_of_array r) s)
   (fun _ -> pts_to r s')
   (fun _ -> seq_of_array_pcm_carrier s `Seq.equal` s')
   (fun _ _ _ -> True)
= intro_pts_to r s;
  A.change_equal_slprop (pts_to r (seq_of_array_pcm_carrier s)) (pts_to r s')

let intro_pts_to1
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (r0: R.ref base_t (array_pcm p r.len))
  (s: array_pcm_carrier t r.len)
  (s': Seq.seq t)
: A.SteelGhost unit opened
   (R.pts_to r0 s)
   (fun _ -> pts_to r s')
   (fun _ ->
     r0 == ref_of_array r /\
     seq_of_array_pcm_carrier s `Seq.equal` s'
   )
   (fun _ _ _ -> True)
= A.change_equal_slprop (R.pts_to r0 s) (R.pts_to (ref_of_array r) s);
  intro_pts_to0 r s s'

let intro_pts_to2
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (#base_t0: Type)
  (#t0: Type)
  (#p0: pcm t0)
  (r0: R.ref base_t0 p0)
  (s: t0)
  (s': Seq.seq t)
: A.SteelGhost unit opened
   (R.pts_to r0 s)
   (fun _ -> pts_to r s')
   (fun _ ->
     base_t0 == base_t /\
     t0 == array_pcm_carrier t r.len /\
     p0 == array_pcm p r.len /\
     r0 == ref_of_array r /\
     seq_of_array_pcm_carrier (s <: array_pcm_carrier t r.len) `Seq.equal` s'
   )
   (fun _ _ _ -> True)
= A.change_equal_slprop
    (R.pts_to r0 s)
    (R.pts_to (r0 <: R.ref base_t (array_pcm p r.len)) s);
  intro_pts_to1 r r0 s s'

let elim_pts_to
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (x: Seq.seq t)
: A.SteelGhostT (squash (Seq.length x == size_v r.len)) opened
   (pts_to r x)
   (fun _ -> R.pts_to (ref_of_array r) (array_pcm_carrier_of_seq r.len (x <: Seq.lseq t (size_v r.len))))
= if Seq.length x = size_v r.len
  then begin
    let sq : squash (Seq.length x == size_v r.len) = () in
    A.rewrite_slprop
      (pts_to r x)
      (R.pts_to (ref_of_array r) (array_pcm_carrier_of_seq r.len (x <: Seq.lseq t (size_v r.len))))
      (fun _ -> ());
    let sq : squash (Seq.length x == size_v r.len) = () in
    A.noop ();
    sq
  end else begin
    A.change_slprop_rel
      (pts_to r x)
      (pure False)
      (fun _ _ -> False)
      (fun m -> 
        assert (Steel.Memory.interp (hp_of (pure False)) m);
        Steel.Memory.pure_interp False m 
      );
    assert False;
    A.rewrite_slprop
      (pure False)
      (R.pts_to (ref_of_array r) (array_pcm_carrier_of_seq r.len x))
      (fun _ -> ());
    let sq : squash (Seq.length x == size_v r.len) = () in
    A.noop ();
    sq
  end

let pts_to_length
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (x: Seq.seq t)
: A.SteelGhostT (squash (Seq.length x == size_v r.len)) opened
    (pts_to r x)
    (fun _ -> pts_to r x)
=
  let _ = elim_pts_to r _ in
  intro_pts_to0 r _ x

let cell
  (#t: Type)
  (p: pcm t) 
  (len: Ghost.erased size_t)
  (i: size_t)
: Pure (connection (array_pcm p len) p)
    (requires (size_v i < size_v len))
    (ensures (fun _ -> True))
= struct_field (array_elements_pcm p len) i

let g_focus_cell
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (s: Seq.seq t)
  (i: size_t)
  (sq: squash (size_v i < size_v r.len \/ size_v i < Seq.length s))
: A.SteelGhostT (squash (size_v i < size_v r.len /\ size_v r.len == Seq.length s)) opened
    (pts_to r s)
    (fun _ -> pts_to r (Seq.upd s (size_v i) (one p)) `star` R.pts_to (ref_focus (ref_of_array r) (cell p r.len i)) (Seq.index s (size_v i)))
= let _ = elim_pts_to r _ in
  g_addr_of_struct_field (ref_of_array r) i _;
  intro_pts_to0 r _ (Seq.upd s (size_v i) (one p));
  A.change_equal_slprop (R.pts_to (ref_focus _ _) _) (R.pts_to (ref_focus _ _) _)

#push-options "--z3rlimit 16"

let pts_to_elim_to_base
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (x: Seq.seq t)
: A.SteelGhost (Ghost.erased (array_pcm_carrier t r.base_len)) opened
    (pts_to r x)
    (fun y -> R.pts_to r.base y)
    (fun _ -> True)
    (fun _ y _ ->
      Seq.length x == size_v r.len /\
      Ghost.reveal y == (ref_of_array_conn r).conn_small_to_large.morph (array_pcm_carrier_of_seq r.len x) /\
      Ghost.reveal y == substruct_to_struct_f (array_elements_pcm p r.base_len) (array_elements_pcm p r.len) (small_to_large_index r.base_len r.offset r.len ()) (large_to_small_index r.base_len r.offset r.len ()) () (array_pcm_carrier_of_seq r.len x)
    )
= let _ = elim_pts_to r _ in
  unfocus (ref_of_array r) r.base (ref_of_array_conn r) _;
  let y = Ghost.hide ((ref_of_array_conn r).conn_small_to_large.morph (array_pcm_carrier_of_seq r.len x)) in
  A.change_equal_slprop (R.pts_to _ _) (R.pts_to _ _);
  y

#pop-options

let pts_to_intro_from_base
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (y: array_pcm_carrier t r.base_len)
  (x: Seq.seq t)
: A.SteelGhost unit opened
    (R.pts_to r.base y)
    (fun _ -> pts_to r x)
    (fun _ ->
      Seq.length x == size_v r.len /\
      y `feq` substruct_to_struct_f (array_elements_pcm p r.base_len) (array_elements_pcm p r.len) (small_to_large_index r.base_len r.offset r.len ()) (large_to_small_index r.base_len r.offset r.len ()) () (array_pcm_carrier_of_seq r.len x)
    )
    (fun _ _ _ -> True)
= gfocus r.base (ref_of_array_conn r) _ (array_pcm_carrier_of_seq r.len x);
  A.change_equal_slprop (R.pts_to _ _) (R.pts_to (ref_of_array r) (array_pcm_carrier_of_seq r.len x));
  intro_pts_to0 r _ x

#push-options "--z3rlimit 16 --split_queries"

#restart-solver
let focus_cell
  (#base_t: Type)
  (#t: Type)
  (#opened: _)
  (#p: pcm t)
  (r: array base_t p)
  (s: Ghost.erased (Seq.seq t))
  (i: size_t)
  (sq: squash (size_v i < size_v r.len \/ size_v i < Seq.length s))
: A.SteelAtomicBase (_: ref base_t p { (size_v i < size_v r.len /\ size_v r.len == Seq.length s) }) false opened Unobservable
    (pts_to r s)
    (fun r' -> pts_to r (Seq.upd s (size_v i) (one p)) `star` R.pts_to r' (Seq.index s (size_v i)))
    (fun _ -> True)
    (fun _ r' _ ->
      r' == ref_focus (ref_of_array r) (cell p r.len i)
    )
= let y = pts_to_elim_to_base r _ in
  ref_focus_comp r.base (ref_of_array_conn r) (cell p r.len i);
  substruct_field (array_elements_pcm p r.base_len) (array_elements_pcm p r.len) (small_to_large_index r.base_len r.offset r.len ()) (large_to_small_index r.base_len r.offset r.len ()) () i;
  let r' = addr_of_struct_field r.base (r.offset `size_add` i) _ in
  pts_to_intro_from_base r _ _;
  A.change_equal_slprop (R.pts_to r' _) (R.pts_to r' _);
  A.return r'

#pop-options

let unfocus_cell
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (s: Seq.seq t)
  (i: size_t)
  (r': R.ref base_t p)
  (v: t)
  (sq: squash (size_v i < size_v r.len /\ size_v i < Seq.length s))
: A.SteelGhost unit opened
    (pts_to r s `star` R.pts_to r' v)
    (fun _ -> pts_to r (Seq.upd s (size_v i) v))
    (fun _ -> 
      r' == ref_focus (ref_of_array r) (cell p r.len i) /\
      Seq.index s (size_v i) == one p
    )
    (fun _ _ _ -> True)
= let _ = elim_pts_to r _ in
  unaddr_of_struct_field #_ #_ #_ #_ #(array_elements_pcm p r.len) i r' (ref_of_array r) _ _;
  intro_pts_to0 r _ (Seq.upd s (size_v i) v)

let share
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (s s1 s2: Seq.seq t)
: A.SteelGhost unit opened
    (pts_to r s)
    (fun _ -> pts_to r s1 `star` pts_to r s2)
    (fun _ ->
      Seq.length s1 == Seq.length s /\
      Seq.length s2 == Seq.length s /\
      (forall (i: nat) .
        i < Seq.length s ==> (
        composable p (Seq.index s1 i) (Seq.index s2 i) /\
        op p (Seq.index s1 i) (Seq.index s2 i) == Seq.index s i
      ))
    )
    (fun _ _ _ -> True)
= let _ = elim_pts_to r _ in
  let a1 = array_pcm_carrier_of_seq r.len s1 in
  let a2 = array_pcm_carrier_of_seq r.len s2 in
  assert (
    composable (array_pcm p r.len) a1 a2 /\
    op (array_pcm p r.len) a1 a2 `feq` array_pcm_carrier_of_seq r.len s
  );
  R.split _ _ a1 a2;
  intro_pts_to0 r a1 s1;
  intro_pts_to0 r a2 s2

let gather
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: array base_t p)
  (s s1 s2: Seq.seq t)
: A.SteelGhost unit opened
    (pts_to r s1 `star` pts_to r s2)
    (fun _ -> pts_to r s)
    (fun _ ->
      Seq.length s1 == Seq.length s /\
      Seq.length s2 == Seq.length s /\
      (forall (i: nat) .
        (i < Seq.length s /\ composable p (Seq.index s1 i) (Seq.index s2 i)) ==> (
        op p (Seq.index s1 i) (Seq.index s2 i) == Seq.index s i
      ))
    )
    (fun _ _ _ -> True)
= let _ = elim_pts_to r s1 in
  let _ = elim_pts_to r s2 in
  let a1 = array_pcm_carrier_of_seq r.len s1 in
  let a2 = array_pcm_carrier_of_seq r.len s2 in
  let _ = R.gather _ (array_pcm_carrier_of_seq r.len s1) _ in
  assert (
    composable (array_pcm p r.len) a1 a2 /\
    op (array_pcm p r.len) a1 a2 `feq` array_pcm_carrier_of_seq r.len s
  );
  intro_pts_to0 r _ s

let sub
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (a: array base_t p)
  (offset: size_t)
  (len: Ghost.erased size_t)
: Pure (array base_t p)
    (requires (size_v offset + size_v len <= size_v a.len))
    (ensures (fun _ -> True))
= {
    a with
    offset = a.offset `size_add` offset;
    len = len;
  }

let split_l
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (a: array base_t p)
  (i: Ghost.erased size_t)
: Pure (array base_t p)
    (requires (size_v i <= size_v a.len))
    (ensures (fun _ -> True))
= sub a 0sz i

let split_r
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (a: array base_t p)
  (i: size_t)
: Pure (array base_t p)
    (requires (size_v i <= size_v a.len))
    (ensures (fun _ -> True))
= sub a i (a.len `size_sub` i)

#push-options "--z3rlimit 128"

#restart-solver
let g_focus_sub
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (a: array base_t p)
  (s: Seq.seq t)
  (offset: size_t)
  (len: size_t)
  (sq: squash (size_v offset + size_v len <= size_v a.len /\ Seq.length s == size_v a.len))
  (sl: Seq.lseq t (size_v a.len))
  (al: array base_t p)
  (sl0: Seq.lseq t (size_v len))
: A.SteelGhost unit opened
    (pts_to a sl)
    (fun _ -> pts_to al sl0)
    (fun _ ->
      al == sub a offset len /\
      sl0 `Seq.equal` Seq.slice s (size_v offset) (size_v offset + size_v len) /\
      sl `Seq.equal` (Seq.create (size_v offset) (one p) `Seq.append` sl0 `Seq.append` Seq.create (size_v a.len - size_v len - size_v offset) (one p))
    )
    (fun _ _ _ -> True)
=
  substruct_compose
    (array_elements_pcm p a.base_len)
    (array_elements_pcm p a.len)
    (small_to_large_index a.base_len a.offset a.len ())
    (large_to_small_index a.base_len a.offset a.len ())
    ()
    (array_elements_pcm p al.len)
    (small_to_large_index a.len offset al.len ())
    (large_to_small_index a.len offset al.len ())
    ()
    (small_to_large_index al.base_len al.offset al.len ())
    (large_to_small_index al.base_len al.offset al.len ())
    ();
  let cl = 
    substruct
      (array_elements_pcm p a.len)
      (array_elements_pcm p al.len)
      (small_to_large_index a.len offset al.len ())
      (large_to_small_index a.len offset al.len ())
      ()
  in
  let xl = array_pcm_carrier_of_seq a.len sl in
  elim_pts_to a sl;
  ref_focus_comp
    a.base
    (ref_of_array_conn a)
    cl;
  let xl0 = array_pcm_carrier_of_seq al.len sl0 in
  assert (
    xl `feq` 
      substruct_to_struct_f
        (array_elements_pcm p a.len)
        (array_elements_pcm p al.len)
        (small_to_large_index a.len offset al.len ())
        (large_to_small_index a.len offset al.len ())
        ()
        xl0
  );
  gfocus (ref_of_array a) cl _ xl0;
  intro_pts_to2 al (ref_focus (ref_of_array a) cl) _ sl0

#pop-options

#push-options "--z3rlimit 32"

#restart-solver
let g_split
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (a: array base_t p)
  (s: Seq.seq t)
  (i: size_t)
  (sq: squash (size_v i <= size_v a.len))
: A.SteelGhostT (squash (Seq.length s == size_v a.len)) opened
    (pts_to a s)
    (fun _ -> pts_to (split_l a i) (Seq.slice s 0 (size_v i)) `star` pts_to (split_r a i) (Seq.slice s (size_v i) (size_v a.len)))
= let _ = pts_to_length a _ in
  Classical.forall_intro (is_unit p);
  let sl0 = Seq.slice s 0 (size_v i) in
  let sl : Seq.lseq t (size_v a.len) = sl0 `Seq.append` Seq.create (size_v a.len - size_v i) (one p) in
  let sr0 = Seq.slice s (size_v i) (size_v a.len) in
  let sr : Seq.lseq t (size_v a.len) = Seq.create (size_v i) (one p) `Seq.append` sr0 in
  share a s sl sr;
  g_focus_sub a s 0sz i () sl (split_l a i) (Seq.slice s 0 (size_v i));
  g_focus_sub a s i (a.len `size_sub` i) () sr (split_r a i) (Seq.slice s (size_v i) (size_v a.len))

#pop-options

#push-options "--z3rlimit 128"

#restart-solver
let unfocus_sub
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (a: array base_t p)
  (s: Seq.seq t)
  (offset: size_t)
  (len: size_t)
  (sq: squash (size_v offset + size_v len <= size_v a.len /\ Seq.length s == size_v a.len))
  (sl: Seq.lseq t (size_v a.len))
  (al: array base_t p)
  (sl0: Seq.lseq t (size_v len))
: A.SteelGhost unit opened
    (pts_to al sl0)
    (fun _ -> pts_to a sl)
    (fun _ ->
      al == sub a offset len /\
      sl0 `Seq.equal` Seq.slice s (size_v offset) (size_v offset + size_v len) /\
      sl `Seq.equal` (Seq.create (size_v offset) (one p) `Seq.append` sl0 `Seq.append` Seq.create (size_v a.len - size_v len - size_v offset) (one p))
    )
    (fun _ _ _ -> True)
=
  substruct_compose
    (array_elements_pcm p a.base_len)
    (array_elements_pcm p a.len)
    (small_to_large_index a.base_len a.offset a.len ())
    (large_to_small_index a.base_len a.offset a.len ())
    ()
    (array_elements_pcm p al.len)
    (small_to_large_index a.len offset al.len ())
    (large_to_small_index a.len offset al.len ())
    ()
    (small_to_large_index al.base_len al.offset al.len ())
    (large_to_small_index al.base_len al.offset al.len ())
    ();
  let cl = 
    substruct
      (array_elements_pcm p a.len)
      (array_elements_pcm p al.len)
      (small_to_large_index a.len offset al.len ())
      (large_to_small_index a.len offset al.len ())
      ()
  in
  let xl = array_pcm_carrier_of_seq a.len sl in
  let _ = elim_pts_to al sl0 in
  ref_focus_comp
    a.base
    (ref_of_array_conn a)
    cl;
  let xl0 = array_pcm_carrier_of_seq al.len sl0 in
  assert (
    xl `feq` 
      substruct_to_struct_f
        (array_elements_pcm p a.len)
        (array_elements_pcm p al.len)
        (small_to_large_index a.len offset al.len ())
        (large_to_small_index a.len offset al.len ())
        ()
        xl0
  );
  unfocus (ref_of_array al) (ref_of_array a) cl _;
  intro_pts_to2 a (ref_of_array a) _ sl

#pop-options

let mk_lseq
  (#t: Type)
  (s: Seq.seq t)
  (l: nat)
  (sq: squash (Seq.length s == l))
: Tot (Seq.lseq t l)
= s

#push-options "--z3rlimit 256 --fuel 0 --ifuel 1 --z3cliopt smt.arith.nl=false"

#restart-solver
let join
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (a: array base_t p)
  (i: size_t)
  (al ar: array base_t p)
  (sl0 sr0: Seq.seq t)
: A.SteelGhost unit opened
    (pts_to al sl0 `star` pts_to ar sr0)
    (fun _ -> pts_to a (sl0 `Seq.append` sr0))
    (fun _ ->
      size_v i <= size_v a.len /\
      al == split_l a i /\
      ar == split_r a i
    )
    (fun _ _ _ -> True)
=
  let _ = pts_to_length al _ in
  let _ = pts_to_length ar _ in
  Classical.forall_intro (is_unit p);
  let sl : Seq.lseq t (size_v a.len) = mk_lseq (sl0 `Seq.append` Seq.create (size_v a.len - size_v i) (one p)) (size_v a.len) () in
  let sr : Seq.lseq t (size_v a.len) = mk_lseq (Seq.create (size_v i) (one p) `Seq.append` sr0) (size_v a.len) () in
  let s : Seq.lseq t (size_v a.len) = mk_lseq (Seq.append sl0 sr0) (size_v a.len) () in
  assert (i == Ghost.reveal al.len);
  unfocus_sub a s 0sz i () sl al sl0;
  unfocus_sub a s i (a.len `size_sub` i) () sr ar sr0;
  gather a s sl sr;
  A.change_equal_slprop (pts_to a _) (pts_to a _)

#pop-options

#restart-solver
let array_as_one_ref_iso
  (#t: Type)
  (p: pcm t)
: Tot (isomorphism (array_pcm p 1sz) p)
= assert_norm (size_v 1sz == 1);
  let c = cell p 1sz 0sz in
  let c1 = c.conn_large_to_small in
  let c2 = c.conn_small_to_large in
  Steel.C.Model.Connection.mkisomorphism
    c1
    c2
    ()
    (Steel.C.Model.Connection.is_inverse_of_intro
      c2.Steel.C.Model.Connection.morph
      c1.Steel.C.Model.Connection.morph
      (fun x ->
        array_pcm_carrier_ext t 1sz (c2.Steel.C.Model.Connection.morph (c1.Steel.C.Model.Connection.morph x)) x (fun i ->
          ()
        )
      )
    )
    (fun x -> ())
    (fun x -> ())

#restart-solver
let array_as_one_ref_iso_eq
  (#t: Type)
  (p: pcm t)
: Lemma
  (
    let _ = assert_norm (size_v 0sz == 0) in
    let _ = assert_norm (size_v 1sz == 1) in
    let _ : squash (size_v 0sz < size_v 1sz) = () in
    connection_of_isomorphism (array_as_one_ref_iso p) == cell p 1sz 0sz
  )
= assert_norm (size_v 0sz == 0);
  assert_norm (size_v 1sz == 1);
  let l = (connection_of_isomorphism (array_as_one_ref_iso p)) in
  let m = (cell p 1sz 0sz) in
  connection_eq_gen
    l
    m
    ()
    (fun x y f v ->
      connection_of_isomorphism_fpu_eq (array_as_one_ref_iso p) x y f v;
      assert_norm ((m.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v == struct_field_lift_fpu' (array_elements_pcm p 1sz) 0sz x y f v);
      assert (connection_of_isomorphism_fpu' (array_as_one_ref_iso p) x y f v `feq` struct_field_lift_fpu' (array_elements_pcm p 1sz) 0sz x y f v);
      assert ((l.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v == (m.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v)
    )

let array_of_ref_conn
  (#t: Type)
  (p: pcm t) 
: Tot (connection p (array_pcm p 1sz))
= connection_of_isomorphism (isomorphism_inverse (array_as_one_ref_iso p))

let g_array_of_ref
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: ref base_t p)
: Ghost (array base_t p)
    (requires True)
    (ensures (fun a ->
      size_v a.base_len == 1 /\
      size_v a.len == 1
    ))
= assert_norm (size_v 1sz == 1);
  {
    base_len = _;
    base = ref_focus r (array_of_ref_conn p);
    offset = 0sz;
    len = 1sz;
    prf = ();
  }

let ref_of_array_of_ref_base
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: ref base_t p)
: Lemma
  (ref_of_array (g_array_of_ref r) == ref_focus r (array_of_ref_conn p))
= ref_of_array_id (g_array_of_ref r)

#push-options "--split_queries"

#restart-solver
let ref_of_array_of_ref
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: ref base_t p)
: Lemma
  (ref_focus (ref_of_array (g_array_of_ref r)) (cell p 1sz 0sz) == r)
= ref_of_array_of_ref_base r;
  ref_focus_comp r (array_of_ref_conn p) (cell p 1sz 0sz); 
  array_as_one_ref_iso_eq p;
  connection_of_isomorphism_inverse_left (array_as_one_ref_iso p);
  ref_focus_id r

#pop-options

#restart-solver
let ghost_array_of_ref
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (#v: t)
  (r: ref base_t p)
: A.SteelGhostT unit opened
    (R.pts_to r v)
    (fun _ -> pts_to (g_array_of_ref r) (Seq.create 1 v))
= assert_norm (size_v 0sz == 0);
  assert_norm (size_v 1sz == 1);
  let v' : array_pcm_carrier t 1sz = field_to_struct_f (array_elements_pcm p 1sz) 0sz v in
  assert (seq_of_array_pcm_carrier v' `Seq.equal` Seq.create 1 v);
  R.gfocus r (array_of_ref_conn p) _ v';
  ref_of_array_of_ref_base r; 
  intro_pts_to1 _ _ _ _

#restart-solver
let array_of_ref
  (#base_t: Type)
  (#t: Type)
  (#opened: _)
  (#p: pcm t)
  (#v: Ghost.erased t)
  (r: ref base_t p)
: A.SteelAtomicBase (array base_t p) false opened Unobservable
    (R.pts_to r v)
    (fun a -> pts_to a (Seq.create 1 (Ghost.reveal v)))
    (fun _ -> True)
    (fun _ a _ -> a == g_array_of_ref r)
= assert_norm (size_v 0sz == 0);
  assert_norm (size_v 1sz == 1);
  let v' : Ghost.erased (array_pcm_carrier t 1sz) = Ghost.hide (field_to_struct_f (array_elements_pcm p 1sz) 0sz v) in
  assert (seq_of_array_pcm_carrier v' `Seq.equal` Seq.create 1 (Ghost.reveal v));
  let r' = R.focus r (array_of_ref_conn p) _ v' in
  let a : array base_t p = {
    base_len = 1sz;
    base = r';
    offset = 0sz;
    len = 1sz;
    prf = ();    
  }
  in
  ref_of_array_of_ref_base r;
  intro_pts_to1 a _ _ _;
  A.return a

#push-options "--split_queries --z3rlimit 32 --query_stats"

#restart-solver
let unarray_of_ref
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (#v: Seq.seq t)
  (r: ref base_t p)
  (a: array base_t p)
: A.SteelGhost (squash (Seq.length v == 1)) opened
    (pts_to a v)
    (fun _ -> R.pts_to r (Seq.index v 0))
    (fun _ -> a == g_array_of_ref r)
    (fun _ _ _ -> True)
= assert_norm (size_v 0sz == 0);
  assert_norm (size_v 1sz == 1);
  let _ = elim_pts_to _ _ in
  ref_of_array_of_ref_base r;
  R.unfocus (ref_of_array a) r (array_of_ref_conn p) _;
  let x = (array_pcm_carrier_of_seq a.len v) in
  assert_norm ((array_of_ref_conn p).conn_small_to_large.morph x == x 0sz);
  array_pcm_carrier_of_seq_eq a.len v 0sz;
  assert (x 0sz == Seq.index v 0);
  A.change_equal_slprop (R.pts_to _ _) (R.pts_to _ _)

#pop-options
