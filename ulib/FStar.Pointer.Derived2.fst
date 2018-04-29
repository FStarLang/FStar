module FStar.Pointer.Derived2

module HH = FStar.HyperStack
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

private
let copy_buffer_contents_precond' (#t: typ) (a: buffer t) (b: buffer t) (h: HS.mem) : GTot Type0 =
  (* source *)
  (* destination *)
  buffer_live h b /\ buffer_readable h a /\ buffer_length b == buffer_length a /\
  loc_disjoint (loc_buffer a) (loc_buffer b)

private
let copy_buffer_contents_postcond' (#t: typ) (a: buffer t) (b: buffer t) (h: HS.mem) (h': HS.mem)
  : GTot Type0 =
  (* source *)
  (* destination *)
  copy_buffer_contents_precond' a b h /\ modifies (loc_buffer b) h h' /\ buffer_readable h' b /\
  buffer_as_seq h' b == buffer_as_seq h a

private
let copy_buffer_contents_inv
  (#t: typ) (a: buffer t) (b: buffer t) (len': UInt32.t) (h: HS.mem) (h': HS.mem)
  : GTot Type0 =
  (* source *)
  (* destination *)
  copy_buffer_contents_precond' a b h /\ modifies (loc_buffer b) h h' /\
  UInt32.v len' <= UInt32.v (buffer_length a) /\ buffer_readable h' (gsub_buffer b 0ul len') /\
  buffer_as_seq h' (gsub_buffer b 0ul len') == buffer_as_seq h (gsub_buffer a 0ul len')

private
val copy_buffer_contents_init: 
  #t: typ ->
  a:
  (* source *)
  buffer t ->
  b:
  (* destination *)
  buffer t ->
  h: HS.mem ->
  Lemma (requires (copy_buffer_contents_precond' a b h))
    (ensures (copy_buffer_contents_inv a b 0ul h h))

let copy_buffer_contents_init #t a b h =
  buffer_readable_intro_empty h (gsub_buffer b 0ul 0ul);
  Seq.lemma_eq_intro (buffer_as_seq h (gsub_buffer b 0ul 0ul))
    (buffer_as_seq h (gsub_buffer a 0ul 0ul))

private
val copy_buffer_contents_advance: 
  #t: typ ->
  a:
  (* source *)
  buffer t ->
  b:
  (* destination *)
  buffer t ->
  len': UInt32.t ->
  h: Ghost.erased HS.mem ->
  HST.Stack unit
    (requires
      (fun h0 ->
          copy_buffer_contents_inv a b len' (Ghost.reveal h) h0 /\
          UInt32.v len' < UInt32.v (buffer_length a)))
    (ensures
      (fun h1 _ h2 ->
          copy_buffer_contents_inv a b len' (Ghost.reveal h) h1 /\
          UInt32.v len' < UInt32.v (buffer_length a) /\
          copy_buffer_contents_inv a b (UInt32.add len' 1ul) (Ghost.reveal h) h2))

#set-options "--z3rlimit 16"

let copy_buffer_contents_advance #t a b len' h =
  let v = read_buffer a len' in
  buffer_snoc b 0ul len' v;
  buffer_as_seq_gsub_buffer_snoc (Ghost.reveal h) a 0ul len'

private
val copy_buffer_contents_aux: 
  #t: typ ->
  a:
  (* source *)
  buffer t ->
  b:
  (* destination *)
  buffer t ->
  len: UInt32.t ->
  len': UInt32.t ->
  h: Ghost.erased HS.mem ->
  HST.Stack unit
    (requires
      (fun h0 -> copy_buffer_contents_inv a b len' (Ghost.reveal h) h0 /\ len == buffer_length a))
    (ensures
      (fun h0 _ h1 ->
          copy_buffer_contents_inv a b len' (Ghost.reveal h) h0 /\
          copy_buffer_contents_postcond' a b (Ghost.reveal h) h1))
    (decreases (UInt32.v (buffer_length a) - UInt32.v len'))

let rec copy_buffer_contents_aux #t a b len len' h =
  if len = len'
  then ()
  else
    (copy_buffer_contents_advance a b len' h;
      copy_buffer_contents_aux a b len (UInt32.add len' 1ul) h)

let copy_buffer_contents_fin
  (#t: typ) (a: buffer t) (idx_a: UInt32.t) (b: buffer t) (idx_b: UInt32.t) (len: UInt32.t)
  (h: HS.mem) (h': HS.mem)
  : Lemma
    ((* source *)
      (* destination *)
      requires
      (copy_buffer_contents_precond a idx_a b idx_b len h /\
        copy_buffer_contents_postcond' (gsub_buffer a idx_a len) (gsub_buffer b idx_b len) h h'))
    (ensures
      (copy_buffer_contents_precond a idx_a b idx_b len h /\
        copy_buffer_contents_postcond a idx_a b idx_b len h h')) = ()

(* FIXME: Does not work if I directly try to define copy_buffer_contents *)

(* FIXME: Works in batch mode (even with --record_hints --use_hints --detail_hint_replay --query_stats) but fails in interactive mode *)

let copy_buffer_contents'
  (#t: typ) (a: buffer t) (idx_a: UInt32.t) (b: buffer t) (idx_b: UInt32.t) (len: UInt32.t)
  : HST.Stack unit
    ((* source *)
      (* destination *)
      requires (fun h -> copy_buffer_contents_precond a idx_a b idx_b len h))
    (ensures (fun h0 _ h1 -> copy_buffer_contents_postcond a idx_a b idx_b len h0 h1)) =
  let h0 = HST.get () in
  let a' = sub_buffer a idx_a len in
  let b' = sub_buffer b idx_b len in
  copy_buffer_contents_init a' b' h0;
  copy_buffer_contents_aux a' b' len 0ul (Ghost.hide h0);
  let h1 = HST.get () in
  copy_buffer_contents_fin a idx_a b idx_b len h0 h1

let copy_buffer_contents = copy_buffer_contents'

