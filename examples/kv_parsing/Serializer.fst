module Serializer

open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Ghost
module B = FStar.Buffer
module U16 = FStar.UInt16
module U32 = FStar.UInt32

open KeyValue
open Slice
open PureEncoder

(*! Efficient serializing *)

(* NOTE: I'm using ser out of laziness, but they should NOT be abbreviated, we
can serialize everywhere *)

unfold
let offset_into (buf:bslice) = off:U32.t{U32.v off <= U32.v buf.len}

let serialized (enc:bytes) (buf:bslice) (r:option (offset_into buf)) (h0 h1:mem) :
    Pure Type0
    (requires (live h1 buf))
    (ensures (fun _ -> True)) =
    match r with
    | Some off ->
      let (b1, b2) = bslice_split_at buf off in
      modifies_slice b1 h0 h1 /\
      as_seq h1 b1 == enc
    | None ->
      modifies_slice buf h0 h1

let buffer_fun (inputs:erased (TSet.set bslice)) =
    f:(h:mem{forall b. TSet.mem b (reveal inputs) ==> live h b} -> GTot bytes){
      forall (h0 h1: h:mem{forall b. TSet.mem b (reveal inputs) ==> live h b}).
      (forall b. TSet.mem b (reveal inputs) ==> as_seq h0 b == as_seq h1 b) ==>
      f h0 == f h1}

let disjoint_in (h:mem) (inputs:TSet.set bslice) (buf:bslice) =
  forall b. TSet.mem b inputs ==> live h b /\ B.disjoint b.p buf.p

let serializer_any (inputs:erased (TSet.set bslice))
                   (enc: buffer_fun inputs) =
  buf:bslice ->
  Stack (option (off:offset_into buf))
     (requires (fun h0 -> live h0 buf /\
                       disjoint_in h0 (reveal inputs) buf))
     (ensures (fun h0 r h1 ->
        live h0 buf /\
        live h1 buf /\
        (forall b. TSet.mem b (reveal inputs) ==>
           live h0 b /\
           live h1 b /\
           as_seq h0 b == as_seq h1 b) /\
        serialized (enc h1) buf r h0 h1))

let serializer (enc:erased bytes) = serializer_any (hide TSet.empty) (fun _ -> reveal enc)

let serializer_1 (input:bslice) (enc: buffer_fun (hide (TSet.singleton input))) =
    serializer_any (hide (TSet.singleton input)) (fun h -> enc h)

let lemma_index_upd_gt (#a:Type) (s:Seq.seq a) (n:nat{n < length s}) (i:nat{n < i /\ i < length s}) (v:a) :
  Lemma (index (Seq.upd s n v) i == index s i)
  [SMTPat (index (Seq.upd s n v) i)] = ()

#reset-options "--z3rlimit 10"

val upd_len_1 : #a:Type -> s:Seq.seq a{length s == 1} -> v:a ->
  Lemma (Seq.upd s 0 v == Seq.create 1 v)
let upd_len_1 #a s v =
  lemma_eq_intro (Seq.upd s 0 v) (Seq.create 1 v)

val ser_byte: v:byte -> serializer (hide (Seq.create 1 v))
let ser_byte v = fun buf ->
  if U32.lt buf.len 1ul then None
  else
    let (buf, _) = bslice_split_at buf 1ul in
    let h0 = get() in
    B.upd buf.p 0ul v;
    begin
      let s0 = as_seq h0 buf in
      upd_len_1 s0 v
    end;
    Some 1ul

let upd_len_2 (#a:Type) (s:Seq.seq a{length s == 2}) (vs:Seq.seq a{length vs == 2}) :
  Lemma (Seq.upd (Seq.upd s 0 (index vs 0)) 1 (index vs 1) == vs) =
  lemma_eq_intro (Seq.upd (Seq.upd s 0 (index vs 0)) 1 (index vs 1)) vs

val ser_u16: v:U16.t -> serializer (hide (u16_to_be v))
let ser_u16 v = fun buf ->
  if U32.lt buf.len 2ul then None
  else
    let bs = u16_to_be v in
    let (buf, _) = bslice_split_at buf 2ul in
    let h0 = get() in
    B.upd buf.p 0ul (index bs 0);
    B.upd buf.p 1ul (index bs 1);
    begin
      let s0 = as_seq h0 buf in
      upd_len_2 s0 bs
    end;
    Some 2ul

let upd_len_4 (#a:Type) (s:Seq.seq a{length s == 4}) (vs:Seq.seq a{length vs == 4}) :
  Lemma (Seq.upd
          (Seq.upd
            (Seq.upd
              (Seq.upd s 0 (index vs 0))
            1 (index vs 1))
          2 (index vs 2))
        3 (index vs 3) == vs) =
  lemma_eq_intro (Seq.upd
  (Seq.upd
  (Seq.upd
  (Seq.upd s 0 (index vs 0))
  1 (index vs 1))
  2 (index vs 2))
  3 (index vs 3)) vs

val ser_u32: v:U32.t -> serializer (hide (u32_to_be v))
let ser_u32 v = fun buf ->
  if U32.lt buf.len 4ul then None
  else
    let bs = u32_to_be v in
    let (buf, _) = bslice_split_at buf 4ul in
    let h0 = get() in
    B.upd buf.p 0ul (index bs 0);
    B.upd buf.p 1ul (index bs 1);
    B.upd buf.p 2ul (index bs 2);
    B.upd buf.p 3ul (index bs 3);
    begin
      let s0 = as_seq h0 buf in
      upd_len_4 s0 bs
    end;
    Some 4ul

// this is really a coercion that lifts a pure bytes serializer to one that
// takes an input buffer (and ignores it)
let ser_input (input:bslice) (#b:erased bytes) (s:serializer b) : serializer_1 input (fun _ -> reveal b) =
    fun buf -> s buf

// coercion to increase the size of the inputs set
let ser_inputs (#inputs1:erased (TSet.set bslice))
               (inputs2:erased (TSet.set bslice){TSet.subset (reveal inputs1) (reveal inputs2)})
               (#b: buffer_fun inputs1)
               (s:serializer_any inputs1 b) : serializer_any inputs2 (fun h -> b h) =
    fun buf -> s buf

#reset-options "--z3rlimit 30"

let ser_append (#inputs1 #inputs2:erased (TSet.set bslice))
               (#b1: buffer_fun inputs1) (#b2: buffer_fun inputs2)
               (s1:serializer_any inputs1 b1) (s2:serializer_any inputs2 b2) :
               serializer_any (elift2 TSet.union inputs1 inputs2) (fun h -> append (b1 h) (b2 h)) =
  fun buf ->
  let h0 = get() in
  match s1 buf with
  | Some off ->
    begin
      let h1 = get() in
      let buf0 = buf in
      let (buf1, buf) = bslice_split_at buf off in
      match s2 buf with
      | Some off' -> (if u32_add_overflows off off' then None
                     else begin
                      begin
                        let h2 = get() in
                        let (buf2, buf3) = bslice_split_at buf off' in
                        let (buf12, buf3') = bslice_split_at buf0 (U32.add off off') in
                        assert (live h2 buf12);
                        assert (as_seq h2 buf2 == b2 h2);
                        assert (as_seq h2 buf1 == b1 h2);
                        is_concat_append buf12.p buf1.p buf2.p h2;
                        assert (as_seq h2 buf12 == append (b1 h2) (b2 h2));
                        //assert (modifies_slice buf1 h0 h1);
                        //assert (modifies_slice buf2 h1 h2);
                        modifies_grow_from_b1 buf12 buf1 buf2 h0 h1;
                        modifies_grow_from_b2 buf12 buf1 buf2 h1 h2;
                        assert (modifies_slice buf12 h0 h2)
                      end;
                      Some (U32.add off off')
                     end)
      | None -> None
    end
  | None -> None

#reset-options

val ser_copy : data:bslice -> serializer_1 data (fun h -> as_seq h data)
let ser_copy data = fun buf ->
  if U32.lt buf.len data.len then None
  else begin
    let (buf1, buf2) = bslice_split_at buf data.len in
    B.blit data.p 0ul buf1.p 0ul data.len;
    Some data.len
  end

let enc_u16_array_st (a: u16_array_st) (h:mem{live h a.a16_st}) : GTot bytes =
    u16_to_be a.len16_st `append` as_seq h a.a16_st

// inline_for_extraction unfold [@"substitute"]
val ser_u16_array : a:u16_array_st ->
  serializer_any (hide (TSet.singleton a.a16_st)) (fun h -> enc_u16_array_st a h)
let ser_u16_array a = fun buf ->
  (ser_u16 a.len16_st `ser_append` ser_copy a.a16_st) buf

let ser_u16_array' a buf = ser_u16_array a buf

let enc_u32_array_st (a: u32_array_st) (h:mem{live h a.a32_st}) : GTot bytes =
  u32_to_be a.len32_st `append` as_seq h a.a32_st

val ser_u32_array : a:u32_array_st ->
  serializer_any (hide (TSet.singleton a.a32_st)) (fun h -> enc_u32_array_st a h)
let ser_u32_array a = fun buf ->
  (ser_u32 a.len32_st `ser_append`
   ser_copy a.a32_st) buf

noextract
val entry_st_bufs : e:entry_st -> TSet.set bslice
noextract
let entry_st_bufs (e: entry_st) = TSet.union (TSet.singleton e.key_st.a16_st) (TSet.singleton e.val_st.a32_st)

val enc_entry_st : e:entry_st -> h:mem{forall b. TSet.mem b (entry_st_bufs e) ==> live h b} -> GTot bytes
let enc_entry_st (e:entry_st) h =
    enc_u16_array_st e.key_st h `append` enc_u32_array_st e.val_st h

let ser_entry (e:entry_st) : serializer_any (hide (entry_st_bufs e)) (fun h -> enc_entry_st e h) =
    fun buf ->
    (ser_u16_array e.key_st `ser_append` ser_u32_array e.val_st) buf

(*! Incremental key-value store writer *)

let adjacent_entries_disjoint (#t:Type) (b1 b2:B.buffer t) :
    Lemma (requires (buffers_adjacent b1 b2))
          (ensures (B.disjoint b1 b2)) = ()

open FStar.Ghost

// TODO: the writer is tracking a few more pointers than strictly necessary; we
// really only need a pointer to the beginning and a bslice at the current write
// position, and entries_written_buf can be reconstructed from these two. This
// requires keeping a large buffer in the writer and then projecting out
// sub-buffers for the current fields.
noeq type writer =
     { length_field: b:lbuffer 4;
       entries_written_buf: bslice;
       entries_written_list: erased (list encoded_entry);
       num_entries_written: U32.t;
       entries_scratch: bslice; }

let writer_valid (w:writer) : Type0 =
    buffers_adjacent w.length_field w.entries_written_buf.p /\
    buffers_adjacent w.entries_written_buf.p w.entries_scratch.p /\
    // so that total size of written data fits in a bslice
    4 + U32.v w.num_entries_written < pow2 32

let writer_inv (h:mem) (w:writer) : Type0 =
    writer_valid w /\
    B.live h w.length_field /\
    B.live h w.entries_scratch.p /\
    (let entries_buf = w.entries_written_buf in
     let enc_entries = as_seq h entries_buf in
     let num_entries = U32.v w.num_entries_written in
     let entries = reveal w.entries_written_list in
     live h entries_buf /\
     List.length entries == num_entries /\
     enc_entries == encode_many entries encode_entry num_entries)

val adjacent_advance (b:bslice) (off:U32.t{U32.v off <= U32.v b.len}) :
  Lemma (buffers_adjacent (truncated_slice b off).p (advance_slice b off).p)
  [SMTPat (buffers_adjacent (truncated_slice b off).p (advance_slice b off).p)]
let adjacent_advance b off = ()

val adjacent_truncate (b b':bslice) (len:U32.t{U32.v len <= U32.v b'.len}) :
  Lemma (requires (buffers_adjacent b.p b'.p))
        (ensures (buffers_adjacent b.p (truncated_slice b' len).p))
  [SMTPat (buffers_adjacent b.p (truncated_slice b' len).p)]
let adjacent_truncate b b' len = ()

val adjacent_0len (b:bslice) :
    Lemma (buffers_adjacent (truncated_slice b 0ul).p b.p)
    [SMTPat (buffers_adjacent (truncated_slice b 0ul).p b.p)]
let adjacent_0len b = ()

let writer_init (b:bslice) : Stack (option writer)
    (requires (fun h0 -> live h0 b))
    (ensures (fun h0 r h1 ->
             h0 == h1 /\
             Some? r ==>
             writer_inv h1 (Some?.v r))) =
    if U32.lt b.len 4ul then None
    else
    let w = { length_field = (truncated_slice b 4ul).p;
              entries_written_buf = truncated_slice (advance_slice b 4ul) 0ul;
              entries_written_list = hide [];
              num_entries_written = 0ul;
              entries_scratch = advance_slice b 4ul } in
    assert (writer_valid w);
    Some w

#reset-options "--z3rlimit 10"

// writer_reinit takes an encoded store at b (and its parsed number of entries)
// and some adjacent scratch space and allows to extend that store
// NOTE: the obligation is that b contains the encoded store; it would be more
// natural to allow any validated store; a proof that parsing is invertible
// should allow validated stores to be used, via an elift)
val writer_reinit (b:bslice) (num_entries: U32.t) (s: erased store) (scratch: bslice) : Stack writer
    (requires (fun h0 -> live h0 b /\
                      buffers_adjacent b.p scratch.p /\
                      4 + U32.v num_entries < pow2 32 /\
                      begin
                        let s = reveal s in
                        let enc = encode_store s in
                        num_entries == s.num_entries /\
                        as_seq h0 b == enc
                      end))
    (ensures (fun h0 w h1 ->
                h0 == h1 /\
                writer_inv h1 w /\
                reveal w.entries_written_list == (reveal s).entries))
let writer_reinit b num_entries s scratch =
    assert (U32.v b.len >= 4);
    let (length_field, entries_written_buf) = bslice_split_at b 4ul in
    let w = { length_field = length_field.p;
              entries_written_buf = entries_written_buf;
              entries_written_list = elift1 (fun s -> s.entries) s;
              num_entries_written = num_entries;
              entries_scratch = scratch; } in
    begin
      let h = get() in
      let s = reveal s in
      assert (writer_valid w);
      is_concat_append b.p length_field.p entries_written_buf.p h;
      lemma_append_inj (u32_to_be s.num_entries) (encode_many s.entries encode_entry (U32.v s.num_entries))
                       (as_seq h length_field) (as_seq h entries_written_buf);
      ()
    end;
    w

#reset-options

let join_slices (b1 b2:bslice) : Pure (option bslice)
    (requires (buffers_adjacent b1.p b2.p))
    (ensures (fun r ->
      match r with
      | Some b -> is_concat_of b.p b1.p b2.p
      | None -> U32.v b1.len + U32.v b2.len >= pow2 32)) =
      if u32_add_overflows b1.len b2.len then None
      else let b' = BSlice (U32.add b1.len b2.len) (B.join b1.p b2.p) in
           Some b'

val enc_one_more (#t:Type) (xs: list t) (enc: t -> bytes) (x: t) :
  Lemma (encode_many xs enc (List.length xs) `append` enc x ==
         encode_many (xs `List.append` [x]) enc (List.length (xs `List.append` [x])))
let rec enc_one_more #t xs enc x =
  match xs with
  | [] -> append_empty_l (enc x); append_empty_r (enc x)
  | x'::xs ->
    enc_one_more xs enc x;
    append_assoc #byte (enc x') (encode_many xs enc (List.length xs)) (enc x)

let max_entries_to_write: n:U32.t{U32.v n == pow2 32 - 5} = 4294967291ul

let lt_max_entries (n:U32.t) :
    Lemma (requires (U32.v n < U32.v max_entries_to_write))
          (ensures (4 + (U32.v n + 1) < pow2 32)) = ()

let join_adjacent_stable (b1 b2 b':bslice) :
    Lemma (requires (buffers_adjacent b1.p b2.p /\
                    buffers_adjacent b2.p b'.p /\
                    Some? (join_slices b1 b2)))
          (ensures (buffers_adjacent b1.p b2.p /\
                    buffers_adjacent (Some?.v (join_slices b1 b2)).p b'.p)) = ()

#set-options "--z3rlimit 30"

val writer_append (w:writer) (e:entry_st) : Stack (option writer)
       (requires (fun h0 -> writer_inv h0 w /\
                         entry_live h0 e /\
                         disjoint_in h0 (entry_st_bufs e) w.entries_scratch ))
       (ensures (fun h0 w' h1 ->
                Some? w' ==>
                begin
                  let w' = Some?.v w' in
                  writer_inv h1 w' /\
                  entry_live h1 e /\
                  (let ee = as_entry h1 e in
                  reveal w'.entries_written_list == reveal w.entries_written_list `List.append` [ee])
                end))
let writer_append w e =
    if U32.gte w.num_entries_written max_entries_to_write then None
    else
    begin
    lt_max_entries w.num_entries_written;
    let r = ser_entry e w.entries_scratch in
    match r with
    | Some off ->
      let (entries_done, entries_scratch') = bslice_split_at w.entries_scratch off in
      begin
        match join_slices w.entries_written_buf entries_done with
        | Some entries_written ->
            join_adjacent_stable w.entries_written_buf entries_done entries_scratch';
            let h = get() in
            let w' = { length_field = w.length_field;
                       entries_written_buf = entries_written;
                       entries_scratch = entries_scratch';
                       entries_written_list = elift1
                         (fun l -> let ee = as_entry h e in
                                l `List.append` [ee])
                         w.entries_written_list;
                       num_entries_written = U32.add w.num_entries_written 1ul } in
            begin
              assert (writer_valid w');
              assert (B.live h w'.length_field);
              assert (B.live h w'.entries_scratch.p);
              assert (live h w'.entries_written_buf);
              let ee = as_entry h e in
              List.append_length (reveal w.entries_written_list) [ee];
              let entries = reveal w'.entries_written_list in
              assert (List.length entries == U32.v w'.num_entries_written);
              enc_one_more (reveal w.entries_written_list) encode_entry ee;
              is_concat_append entries_written.p w.entries_written_buf.p entries_done.p h;
              ()
            end;
            Some w'
        | None -> None
      end
    | None -> None
    end

val join_is_concat (#t:Type) (b1 b2:B.buffer t) :
    Lemma (requires (same_ref b1 b2 /\
                     B.idx b1 + B.length b1 == B.idx b2))
          (ensures (same_ref b1 b2 /\
                    B.idx b1 + B.length b1 == B.idx b2 /\
                    is_concat_of (B.join b1 b2) b1 b2))
let join_is_concat #t b1 b2 = ()

let writer_store_buf (w:writer{writer_valid w}) : Pure bslice
  (requires True)
  (ensures (fun b -> is_concat_of b.p w.length_field w.entries_written_buf.p)) =
  let b1 = w.length_field in
  let b2 = w.entries_written_buf.p in
  join_is_concat b1 b2;
  BSlice (U32.add 4ul w.entries_written_buf.len) (B.join b1 b2)

// XXX: don't have a proof that ser_u32 will not fail if given a buffer of
// length 4 (and somehow F* doesn't prove this by unfolding the definition
// enough)
val writer_finish (w:writer) : Stack (option bslice)
    (requires (fun h0 -> writer_inv h0 w))
    (ensures (fun h0 mb h1 ->
                Some? mb ==>
                begin
                let b = Some?.v mb in
                live h1 b /\
                (let bs = as_seq h1 b in
                 let entries = reveal w.entries_written_list in
                 List.length entries == U32.v w.num_entries_written /\
                 bs == encode_store (Store w.num_entries_written entries))
                end))
let writer_finish w =
    let length_buf = BSlice 4ul w.length_field in
    let r = ser_u32 w.num_entries_written length_buf in
    match r with
    | Some off ->
        let b = writer_store_buf w in
        begin
          let h1 = get() in
          assert (live h1 b);
          let bs = as_seq h1 b in
          let entries = reveal w.entries_written_list in
          let enc_entries = as_seq h1 w.entries_written_buf in
          assert (List.length entries == U32.v w.num_entries_written);
          // this is the only required part of this proof (everything else falls
          // out relatively easily)
          is_concat_append b.p w.length_field w.entries_written_buf.p h1;
          assert (bs == B.as_seq h1 w.length_field `append` enc_entries);
          ()
        end;
      Some b
    | None -> None
