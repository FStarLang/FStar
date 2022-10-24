module Steel.C.Model.Array

open Steel.C.Model.PCM
open Steel.C.Model.Connection
open Steel.C.Model.Ref
open Steel.C.Model.Struct
open Steel.C.StdInt
open Steel.Effect
module R = Steel.C.Model.Ref
module A = Steel.Effect.Atomic

(* Base array type *)

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
  (#t: Type)
  (p: pcm t)
= {
    base_len: Ghost.erased size_t;
    base: R.ref (array_pcm p base_len);
    offset: size_t;
    len: Ghost.erased size_t;
    prf: squash (size_v offset + size_v len <= size_v base_len);
  }

let length
  (#t: Type)
  (#p: pcm t)
  (a: array p)
: GTot nat
= size_v a.len

let adjacent
  (#t: Type)
  (#p: pcm t)
  (a1 a2: array p)
: Tot prop
= a1.base_len == a2.base_len /\
  a1.base == a2.base /\
  size_v a1.offset + size_v a1.len == size_v a2.offset

let merge
  (#t: Type)
  (#p: pcm t)
  (a1 a2: array p)
: Pure (array p)
    (requires (adjacent a1 a2))
    (ensures (fun y -> length y == length a1 + length a2))
= {
    base_len = a1.base_len;
    base = a1.base;
    offset = a1.offset;
    len = size_add a1.len a2.len;
    prf = ();
  }

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
  (#t: Type)
  (#p: pcm t)
  (r: array p)
: GTot (connection (array_pcm p r.base_len) (array_pcm p r.len))
= substruct (array_elements_pcm p r.base_len) (array_elements_pcm p r.len) (small_to_large_index r.base_len r.offset r.len ()) (large_to_small_index r.base_len r.offset r.len ()) ()

let ref_of_array
  (#t: Type)
  (#p: pcm t)
  (r: array p)
: GTot (R.ref (array_pcm p r.len))
= R.ref_focus r.base (ref_of_array_conn r)

let ref_of_array_id
  (#t: Type)
  (#p: pcm t)
  (r: array p)
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
  (#t: Type)
  (#p: pcm t)
  (r: array p)
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
  (#t: Type)
  (#p: pcm t)
  (r: array p)
  (x: Seq.seq t)
: Tot vprop
= VUnit ({
    hp = hp_of (pts_to0 r x);
    t = unit;
    sel = trivial_selector _;
  })

let intro_pts_to'
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (r: array p)
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
  (#t: Type)
  (#p: pcm t)
  (r: array p)
  (s: array_pcm_carrier t r.len)
: A.SteelGhostT unit opened
   (R.pts_to (ref_of_array r) s)
   (fun _ -> pts_to r (seq_of_array_pcm_carrier s))
= array_pcm_carrier_of_seq_of_array_pcm_carrier s;
  A.change_equal_slprop (R.pts_to _ _) (R.pts_to _ _);
  intro_pts_to' r (seq_of_array_pcm_carrier s)

let intro_pts_to0
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (r: array p)
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
  (#t: Type)
  (#p: pcm t)
  (r: array p)
  (r0: R.ref (array_pcm p r.len))
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
  (#t: Type)
  (#p: pcm t)
  (r: array p)
  (#t0: Type)
  (#p0: pcm t0)
  (r0: R.ref p0)
  (s: t0)
  (s': Seq.seq t)
: A.SteelGhost unit opened
   (R.pts_to r0 s)
   (fun _ -> pts_to r s')
   (fun _ ->
     t0 == array_pcm_carrier t r.len /\
     p0 == array_pcm p r.len /\
     r0 == ref_of_array r /\
     seq_of_array_pcm_carrier (s <: array_pcm_carrier t r.len) `Seq.equal` s'
   )
   (fun _ _ _ -> True)
= A.change_equal_slprop
    (R.pts_to r0 s)
    (R.pts_to (r0 <: R.ref (array_pcm p r.len)) s);
  intro_pts_to1 r r0 s s'

let elim_pts_to
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (r: array p)
  (x: Seq.seq t)
: A.SteelGhostT (squash (Seq.length x == size_v r.len)) opened
   (pts_to r x)
   (fun _ -> R.pts_to (ref_of_array r) (array_pcm_carrier_of_seq r.len x))
= if Seq.length x = size_v r.len
  then begin
    A.rewrite_slprop
      (pts_to r x)
      (R.pts_to (ref_of_array r) (array_pcm_carrier_of_seq r.len x))
      (fun _ -> ())
  end else begin
    A.change_slprop_rel
      (pts_to r x)
      (pure False)
      (fun _ _ -> False)
      (fun m -> 
        assert (Steel.Memory.interp (hp_of (pure False)) m);
        Steel.Memory.pure_interp False m 
      );
    A.rewrite_slprop
      (pure False)
      (R.pts_to (ref_of_array r) (array_pcm_carrier_of_seq r.len x))
      (fun _ -> ())
  end

let pts_to_length
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (r: array p)
  (x: Seq.seq t)
: A.SteelGhostT (squash (Seq.length x == size_v r.len)) opened
    (pts_to r x)
    (fun _ -> pts_to r x)
=
  elim_pts_to r _;
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
  (#t: Type)
  (#p: pcm t)
  (r: array p)
  (s: Seq.seq t)
  (i: size_t)
  (sq: squash (size_v i < size_v r.len \/ size_v i < Seq.length s))
: A.SteelGhostT (squash (size_v i < size_v r.len /\ size_v r.len == Seq.length s)) opened
    (pts_to r s)
    (fun _ -> pts_to r (Seq.upd s (size_v i) (one p)) `star` R.pts_to (ref_focus (ref_of_array r) (cell p r.len i)) (Seq.index s (size_v i)))
= elim_pts_to r _;
  g_addr_of_struct_field (ref_of_array r) i _;
  intro_pts_to0 r _ (Seq.upd s (size_v i) (one p));
  A.change_equal_slprop (R.pts_to (ref_focus _ _) _) (R.pts_to (ref_focus _ _) _)

#push-options "--z3rlimit 16"

let pts_to_elim_to_base
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (r: array p)
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
= elim_pts_to r _;
  unfocus (ref_of_array r) r.base (ref_of_array_conn r) _;
  let y = Ghost.hide ((ref_of_array_conn r).conn_small_to_large.morph (array_pcm_carrier_of_seq r.len x)) in
  A.change_equal_slprop (R.pts_to _ _) (R.pts_to _ _);
  y

#pop-options

let pts_to_intro_from_base
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (r: array p)
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
  (#t: Type)
  (#p: pcm t)
  (r: array p)
  (s: Ghost.erased (Seq.seq t))
  (i: size_t)
  (sq: squash (size_v i < size_v r.len \/ size_v i < Seq.length s))
: Steel (_: ref p { (size_v i < size_v r.len /\ size_v r.len == Seq.length s) })
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
  (#t: Type)
  (#p: pcm t)
  (r: array p)
  (s: Seq.seq t)
  (i: size_t)
  (r': R.ref p)
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
= elim_pts_to r _;
  unaddr_of_struct_field #_ #_ #_ #(array_elements_pcm p r.len) i r' (ref_of_array r) _ _;
  intro_pts_to0 r _ (Seq.upd s (size_v i) v)

let share
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (r: array p)
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
= elim_pts_to r _;
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
  (#t: Type)
  (#p: pcm t)
  (r: array p)
  (s s1 s2: Seq.seq t)
: A.SteelGhost unit opened
    (pts_to r s1 `star` pts_to r s2)
    (fun _ -> pts_to r s)
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
= elim_pts_to r s1;
  elim_pts_to r s2;
  let a1 = array_pcm_carrier_of_seq r.len s1 in
  let a2 = array_pcm_carrier_of_seq r.len s2 in
  assert (
    composable (array_pcm p r.len) a1 a2 /\
    op (array_pcm p r.len) a1 a2 `feq` array_pcm_carrier_of_seq r.len s
  );
  R.gather _ (array_pcm_carrier_of_seq r.len s1) _;
  intro_pts_to0 r _ s

let sub
  (#t: Type)
  (#p: pcm t)
  (a: array p)
  (offset: size_t)
  (len: Ghost.erased size_t)
: Pure (array p)
    (requires (size_v offset + size_v len <= size_v a.len))
    (ensures (fun _ -> True))
= {
    a with
    offset = a.offset `size_add` offset;
    len = len;
  }

let split_l
  (#t: Type)
  (#p: pcm t)
  (a: array p)
  (i: Ghost.erased size_t)
: Pure (array p)
    (requires (size_v i <= size_v a.len))
    (ensures (fun _ -> True))
= sub a zero_size i

let split_r
  (#t: Type)
  (#p: pcm t)
  (a: array p)
  (i: size_t)
: Pure (array p)
    (requires (size_v i <= size_v a.len))
    (ensures (fun _ -> True))
= sub a i (a.len `size_sub` i)

#push-options "--z3rlimit 64"

#restart-solver
let g_focus_sub
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (a: array p)
  (s: Seq.seq t)
  (offset: size_t)
  (len: size_t)
  (sq: squash (size_v offset + size_v len <= size_v a.len /\ Seq.length s == size_v a.len))
  (sl: Seq.lseq t (size_v a.len))
  (al: array p)
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

#push-options "--z3rlimit 16"

#restart-solver
let g_split
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (a: array p)
  (s: Seq.seq t)
  (i: size_t)
  (sq: squash (size_v i <= size_v a.len))
: A.SteelGhostT (squash (Seq.length s == size_v a.len)) opened
    (pts_to a s)
    (fun _ -> pts_to (split_l a i) (Seq.slice s 0 (size_v i)) `star` pts_to (split_r a i) (Seq.slice s (size_v i) (size_v a.len)))
= pts_to_length a _;
  Classical.forall_intro (is_unit p);
  let sl0 = Seq.slice s 0 (size_v i) in
  let sl : Seq.lseq t (size_v a.len) = sl0 `Seq.append` Seq.create (size_v a.len - size_v i) (one p) in
  let sr0 = Seq.slice s (size_v i) (size_v a.len) in
  let sr : Seq.lseq t (size_v a.len) = Seq.create (size_v i) (one p) `Seq.append` sr0 in
  share a s sl sr;
  g_focus_sub a s zero_size i () sl (split_l a i) (Seq.slice s 0 (size_v i));
  g_focus_sub a s i (a.len `size_sub` i) () sr (split_r a i) (Seq.slice s (size_v i) (size_v a.len))

#pop-options

#push-options "--z3rlimit 64"

#restart-solver
let unfocus_sub
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (a: array p)
  (s: Seq.seq t)
  (offset: size_t)
  (len: size_t)
  (sq: squash (size_v offset + size_v len <= size_v a.len /\ Seq.length s == size_v a.len))
  (sl: Seq.lseq t (size_v a.len))
  (al: array p)
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
  elim_pts_to al sl0;
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

#push-options "--z3rlimit 128 --fuel 0 --ifuel 1 --z3cliopt smt.arith.nl=false"

#restart-solver
let join
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (a: array p)
  (i: size_t)
  (al ar: array p)
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
  pts_to_length al _;
  pts_to_length ar _;
  Classical.forall_intro (is_unit p);
  let sl : Seq.lseq t (size_v a.len) = sl0 `Seq.append` Seq.create (size_v a.len - size_v i) (one p) in
  let sr : Seq.lseq t (size_v a.len) = Seq.create (size_v i) (one p) `Seq.append` sr0 in
  let s : Seq.lseq t (size_v a.len) = Seq.append sl0 sr0 in
  assert (i == Ghost.reveal al.len);
  assert (size_v zero_size == 0);
  unfocus_sub a s zero_size i () sl al sl0;
  unfocus_sub a s i (a.len `size_sub` i) () sr ar sr0;
  gather a s sl sr;
  A.change_equal_slprop (pts_to a _) (pts_to a _)

#pop-options
