module Serializing

open Slice

open FStar.Ghost
open FStar.Seq
module List = FStar.List.Tot
open FStar.HyperStack
open FStar.HyperStack.ST
module B = FStar.Buffer

// kremlib libraries
module C = C
open C.Loops

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

val encode_many : #t:Type -> l:list t -> enc:(t -> bytes) -> n:nat{n <= List.length l} -> bytes
let rec encode_many #t l enc n =
  match n with
  | 0 -> Seq.createEmpty
  | _ -> enc (List.hd l) `append`
        encode_many (List.tail l) enc (n-1)

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

inline_for_extraction
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

inline_for_extraction
let serializer (enc:erased bytes) = serializer_any (hide TSet.empty) (fun _ -> reveal enc)

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
