module Serializing

open Slice

open FStar.Seq
module List = FStar.List.Tot
open FStar.HyperStack
open FStar.HyperStack.ST
module B = FStar.Buffer

open FStar.Ghost

// kremlib libraries
module C = C
open C.Loops

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

(* Note the lack of definitions around encoding, the pure specification for serialization.

   An encoded value is simply of type [bytes] ([seq byte]). Encoders are
   functions from whatever they encode to [Tot bytes]. There should be no need for
   failures during encoding, due to restrictions in the types or
   refinements/preconditions on the encoders themselves.

   Note that no connection is made here to parsing. Instead, this can be done
   outside this library by relating the pure parsers to the pure encoders.

*)

/// Encode a list of values and concatenate the results.
val encode_many : #t:Type -> l:list t -> enc:(t -> bytes) -> n:nat{n <= List.length l} -> bytes
let rec encode_many #t l enc n =
  match n with
  | 0 -> Seq.empty
  | _ -> enc (List.hd l) `append`
        encode_many (List.tail l) enc (n-1)

let offset_into (buf:bslice) = off:U32.t{U32.v off <= U32.v buf.len}

/// The core specification of serialization, the stateful analogue of encoding.
/// Note that this condition requires that only the first off bytes of the
/// output buffer are modified if the serializer succeeds, but allows the entire
/// output buffer to be arbitrarily modified if it fails.
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

/// A buffer_fun captures a specification encoder that relies on a fixed set of
/// input bslices. It is required to depend on only those bslices since it
/// returns the same output for any two heaps where all the inputs buffers have
/// equal abstract values. The definition is complicated to do allowing the
/// function to assume all the input buffers are live in any heap it operates
/// on.
let buffer_fun (inputs:erased (TSet.set bslice)) =
    f:(h:mem{forall b. TSet.mem b (reveal inputs) ==> live h b} -> GTot bytes){
      forall (h0 h1: (h:mem{forall b. TSet.mem b (reveal inputs) ==> live h b})).
      (forall b. TSet.mem b (reveal inputs) ==> as_seq h0 b == as_seq h1 b) ==>
      f h0 == f h1}

/// Predicate that buf is disjoint from all the inputs (used to assert that the
/// output buffer while serializing is disjoint from input buffers, since inputs
/// are expected to be immutable while serializing).
let disjoint_from (h:mem) (inputs:TSet.set bslice) (buf:bslice) =
  forall b. TSet.mem b inputs ==> live h b /\ B.disjoint b.p buf.p

/// A general serializer, taking input from some set of buffers. The input
/// buffers are required to be disjoint from the output and are unmodified. The
/// definition of [serialized] enforces that the output buffer has the correct
/// bytes.
///
/// As with parsers (and their stateful variants), we do not enforce a lack of
/// lookahead (or even reading) in these serializers. A more general property
/// not enforced here is that serializers should succeed if given a large enough
/// input buffer (this would forbid success depending on the contents of the
/// output buffer, for example).
inline_for_extraction
let serializer_any (inputs:erased (TSet.set bslice))
                   (enc: buffer_fun inputs) =
  buf:bslice ->
  Stack (option (off:offset_into buf))
     (requires (fun h0 -> live h0 buf /\
                       disjoint_from h0 (reveal inputs) buf))
     (ensures (fun h0 r h1 ->
        live h0 buf /\
        live h1 buf /\
        (forall b. TSet.mem b (reveal inputs) ==>
           live h0 b /\
           live h1 b /\
           as_seq h0 b == as_seq h1 b) /\
        serialized (enc h1) buf r h0 h1))

/// Special case of [serializer_any] with no input buffers and thus a fixed set of
/// bytes to be serialized. Typically the bytes to encode would be computed from
/// the inputs by a pure encoder function.
inline_for_extraction
let serializer (enc:erased bytes) = serializer_any (hide TSet.empty) (fun _ -> reveal enc)

/// Special case of [serializer_any] with only one input buffer.
inline_for_extraction
let serializer_1 (input:bslice) (enc: buffer_fun (hide (TSet.singleton input))) =
    serializer_any (hide (TSet.singleton input)) (fun h -> enc h)

// this is really a coercion that lifts a pure bytes serializer to one that
// takes an input buffer (and ignores it)
[@"substitute"]
let ser_input (input:bslice) (#b:erased bytes) (s:serializer b) : serializer_1 input (fun _ -> reveal b) =
  fun buf -> s buf

// coercion to increase the size of the inputs set
[@"substitute"]
let ser_inputs (#inputs1:erased (TSet.set bslice))
                (inputs2:erased (TSet.set bslice){TSet.subset (reveal inputs1) (reveal inputs2)})
                (#b: buffer_fun inputs1)
                (s:serializer_any inputs1 b) : serializer_any inputs2 (fun h -> b h) =
    fun buf -> s buf

#reset-options "--z3rlimit 30"

/// Run two serializers in sequence (monoidally combines serializers). Fully
/// general; combines the input buffer sets of the two serializers.
[@"substitute"]
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
      // TODO: this overflow should actually be impossible, since off + off' is
      // a valid offset for the original slice, which had length < 2^32.
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

/// Simple serializer_1 that just copies the input buffer. Fails if supplied
/// a short output buffer, and otherwise just performs a memcpy.
[@"substitute"]
val ser_copy : data:bslice -> serializer_1 data (fun h -> as_seq h data)
[@"substitute"]
let ser_copy data = fun buf ->
  if U32.lt buf.len data.len then None
  else begin
    let (buf1, buf2) = bslice_split_at buf data.len in
    B.blit data.p 0ul buf1.p 0ul data.len;
    Some data.len
  end
