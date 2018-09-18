module FStar.Pointer.Derived3

module HH = FStar.HyperStack
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

private
let fill_buffer_precond' (#t: typ) (b: buffer t) (h: HS.mem) : GTot Type0 =
  buffer_live h b (* destination *)

private
let fill_buffer_postcond' (#t: typ) (b: buffer t) (v: type_of_typ t) (h: HS.mem) (h': HS.mem)
  : GTot Type0 =
  (* destination *)
  fill_buffer_precond' b h /\ modifies (loc_buffer b) h h' /\ buffer_readable h' b /\
  buffer_as_seq h' b == Seq.create (UInt32.v (buffer_length b)) v

private
let fill_buffer_inv
  (#t: typ) (b: buffer t) (len': UInt32.t) (v: type_of_typ t) (h: HS.mem) (h': HS.mem)
  : GTot Type0 =
  (* destination *)
  fill_buffer_precond' b h /\ modifies (loc_buffer b) h h' /\
  UInt32.v len' <= UInt32.v (buffer_length b) /\ buffer_readable h' (gsub_buffer b 0ul len') /\
  buffer_as_seq h' (gsub_buffer b 0ul len') == Seq.create (UInt32.v len') v

private
val fill_buffer_init: 
  #t: typ ->
  b:
  (* destination *)
  buffer t ->
  v: type_of_typ t ->
  h: HS.mem ->
  Lemma (requires (fill_buffer_precond' b h)) (ensures (fill_buffer_inv b 0ul v h h))

let fill_buffer_init #t b v h =
  buffer_readable_intro_empty h (gsub_buffer b 0ul 0ul);
  Seq.lemma_eq_intro (buffer_as_seq h (gsub_buffer b 0ul 0ul)) (Seq.create 0 v)

private
val fill_buffer_advance: 
  #t: typ ->
  b:
  (* destination *)
  buffer t ->
  len': UInt32.t ->
  v: type_of_typ t ->
  h: Ghost.erased HS.mem ->
  HST.Stack unit
    (requires
      (fun h0 ->
          fill_buffer_inv b len' v (Ghost.reveal h) h0 /\ UInt32.v len' < UInt32.v (buffer_length b)
      ))
    (ensures
      (fun h1 _ h2 ->
          fill_buffer_inv b len' v (Ghost.reveal h) h1 /\ UInt32.v len' < UInt32.v (buffer_length b) /\
          fill_buffer_inv b (UInt32.add len' 1ul) v (Ghost.reveal h) h2))

#set-options "--z3rlimit 16"

let fill_buffer_advance #t b len' v h =
  buffer_snoc b 0ul len' v;
  Seq.lemma_eq_intro (Seq.snoc (Seq.create (UInt32.v len') v) v)
    (Seq.create (UInt32.v (UInt32.add len' 1ul)) v)

private
val fill_buffer_aux: 
  #t: typ ->
  b:
  (* destination *)
  buffer t ->
  len: UInt32.t ->
  len': UInt32.t ->
  v: type_of_typ t ->
  h: Ghost.erased HS.mem ->
  HST.Stack unit
    (requires (fun h0 -> fill_buffer_inv b len' v (Ghost.reveal h) h0 /\ len == buffer_length b))
    (ensures
      (fun h0 _ h1 ->
          fill_buffer_inv b len' v (Ghost.reveal h) h0 /\
          fill_buffer_postcond' b v (Ghost.reveal h) h1))
    (decreases (UInt32.v (buffer_length b) - UInt32.v len'))

let rec fill_buffer_aux #t b len len' v h =
  if len = len'
  then ()
  else
    (fill_buffer_advance b len' v h;
      fill_buffer_aux b len (UInt32.add len' 1ul) v h)

let fill_buffer_fin
  (#t: typ) (b: buffer t) (idx_b: UInt32.t) (len: UInt32.t) (v: type_of_typ t) (h: HS.mem)
  (h': HS.mem)
  : Lemma
    (* destination *)
    (requires
      (fill_buffer_precond b idx_b len h /\ fill_buffer_postcond' (gsub_buffer b idx_b len) v h h'))
    (ensures (fill_buffer_precond b idx_b len h /\ fill_buffer_postcond b idx_b len v h h')) = ()

let fill_buffer' (#t: typ) (b: buffer t) (idx_b: UInt32.t) (len: UInt32.t) (v: type_of_typ t)
  : HST.Stack unit
    (* destination *)
    (requires (fun h -> fill_buffer_precond b idx_b len h))
    (ensures (fun h0 _ h1 -> fill_buffer_postcond b idx_b len v h0 h1)) =
  let h0 = HST.get () in
  let b' = sub_buffer b idx_b len in
  fill_buffer_init b' v h0;
  fill_buffer_aux b' len 0ul v (Ghost.hide h0);
  let h1 = HST.get () in
  fill_buffer_fin b idx_b len v h0 h1


let fill_buffer = fill_buffer'

