module VectorParsing

open Parsing
open IntegerParsing
open PureParser
open Validator
open PureEncoder
open Serializer
open Slice

open FStar.Ghost
module List = FStar.List.Tot
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST
open C.Loops

module B = FStar.Buffer

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

assume type t : Type0
assume val parse_elem : parser t

assume val enc_elem : t -> b:bytes{length b > 0}

assume val parse_elem_enc : b:bytes{length b < pow2 32} ->
  Lemma (match parse_elem b with
        | Some (v, off) -> enc_elem v == slice b 0 off
        | None -> True)

val parse_elem_progress : b:bytes{length b < pow2 32} ->
  Lemma (match parse_elem b with
        | Some (_, off) -> off > 0
        | None -> True)
let parse_elem_progress b = parse_elem_enc b;
  // XXX: this pattern match recently became required to trigger the right hint
  match parse_elem b with
  | Some (_, off) -> ()
    // fully explicit (though there's a hint for this)
    // lemma_len_slice b 0 off
  | None -> ()

val parse_elem_enc_length : b:bytes{length b < pow2 32} ->
  Lemma (match parse_elem b with
        | Some (v, off) -> length (enc_elem v) == off
        | None -> True)
let parse_elem_enc_length b = parse_elem_enc b;
    match parse_elem b with
    | Some _ -> ()
    | None -> ()

// for vector of length 0..2^16-1
// (note: no additional length checks, and this fixes the length field as a
// U16.t)

val vector_length: list t -> nat
let vector_length l = List.fold_right (fun v (acc: nat) -> length (enc_elem v) + acc) l 0

type vector = l:list t{vector_length l < pow2 16}

#reset-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 10"

val parse_vector_length_pre : len:U16.t -> b:bytes{length b < pow2 32} ->
  Tot (option (v:vector{vector_length v == U16.v len}))
  (decreases (length b))
let rec parse_vector_length_pre len = fun b ->
  if length b < U16.v len then None else
  if U16.v len = 0 then Some [] else
  match parse_elem b with
  | Some (v, off) ->
    if off > U16.v len then None else
    begin
      parse_elem_progress b;
      parse_elem_enc_length b;
      let b = slice b off (length b) in
      match parse_vector_length_pre (U16.sub len (U16.uint_to_t off)) b with
      | Some vs -> Some (v::vs)
      | None -> None
    end
  | None -> None

// TODO: proof involves recursion to reverse the order of parse_vector_length_pre;
// recursion should be on the length of the vector parsed
assume val parse_vector_length_pre_extend : len:U16.t -> off:nat -> off':nat{off+off' < pow2 16} -> b:bytes{length b < pow2 32} ->
    Lemma (requires (off + off' <= U16.v len /\
                     U16.v len <= length b /\
                     (let bs' = slice b off (length b) in
                      Some? (parse_vector_length_pre (U16.uint_to_t off) b) /\
                      Some? (parse_elem bs') /\
                      snd (Some?.v (parse_elem bs')) == off')))
          (ensures (off + off' <= U16.v len /\
                    U16.v len <= length b /\
                    Some? (parse_vector_length_pre (U16.uint_to_t (off+off')) b)))

val parse_vector_length : len:U16.t -> parser (v:vector{vector_length v == U16.v len})
let parse_vector_length len = fun b ->
  match parse_vector_length_pre len b with
  | Some v -> Some (v, U16.v len)
  | None -> None

let parse_vector_length_0 (b:bytes{length b < pow2 32}) :
    Lemma (parse_vector_length 0us b == Some ([], 0))
    = match parse_vector_length_pre 0us b with
      | Some _ -> ()
      | None -> ()

val parse_vector_length_consumes_len : len:U16.t -> b:bytes{length b < pow2 32} ->
  Lemma (match parse_vector_length len b with
        | Some (_, off) -> off == U16.v len
        | None -> True)
let parse_vector_length_consumes_len len b = ()

val parse_vector : parser vector
let parse_vector =
  parse_u16 `and_then`
  (fun bytes -> parse_vector_length bytes `and_then`
  (fun v -> parse_ret (v <: vector)))

val encode_vector_data : v:vector -> b:bytes{length b == vector_length v}
let rec encode_vector_data v =
  match v with
  | [] -> Seq.empty
  | e::es -> enc_elem e `append` encode_vector_data es

val encode_vector : v:vector -> bytes
let encode_vector v =
  encode_u16 (U16.uint_to_t (vector_length v)) `append`
  encode_vector_data v

assume val validate_elem_st : stateful_validator (hide parse_elem)

val do_while_readonly :
    #t:Type0 ->
    init:t ->
    #a:Type ->
    buf:B.buffer a ->
    inv:(vs:seq a{length vs == B.length buf} -> t -> bool -> GTot Type0) ->
    f:(v:t -> Stack (t*bool)
             (requires (fun h0 -> B.live h0 buf /\
                               inv (B.as_seq h0 buf) v false))
             (ensures (fun h0 (v', done) h1 ->
                         modifies_none h0 h1 /\
                         B.live h1 buf /\
                         inv (B.as_seq h1 buf) v' done ))) ->
    Stack t
    (requires (fun h0 -> B.live h0 buf /\
                      inv (B.as_seq h0 buf) init false))
    (ensures (fun h0 r h1 -> modifies_none h0 h1 /\
                          B.live h1 buf /\
                          inv (B.as_seq h1 buf) r true))
let do_while_readonly #t init #a buf inv f =
    let h0 = get() in
    push_frame();
    let h1 = get() in
    let ptr_val = B.create #t init 1ul in
    assert (ptr_val `B.unused_in` h1 /\
           B.frameOf ptr_val == get_tip h1);
    let h = get() in
    let _ = begin
        do_while
          (fun h break ->
             B.live h buf /\
             B.live h ptr_val /\
             B.modifies_0 h1 h /\
             inv (B.as_seq h buf) (Seq.index (B.as_seq h ptr_val) 0) break)
          (fun _ -> let h0' = get() in
                 let v = B.index ptr_val 0ul in
                 let (v', break) = f v in
                 let h1' = get() in
                 B.upd ptr_val 0ul v';
                 let h2' = get() in
                 B.lemma_modifies_none_1_trans ptr_val h0' h1' h2';
                 B.lemma_modifies_0_unalloc ptr_val h1 h0' h2';
                 break)
        end in
    let v = B.index ptr_val 0ul in
    let h2 = get() in
    pop_frame();
    let h3 = get() in
    B.lemma_modifies_0_push_pop h0 h1 h2 h3;
    v

val u16_bound (n m:nat) (bound:U16.t) :
    Lemma (requires (n + m <= U16.v bound))
          (ensures (n + m <= U16.v bound /\
                    n + m < pow2 16))
let u16_bound n m bound = ()

#reset-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 40"

val validate_vector_data : len:U16.t -> stateful_validator (hide (parse_vector_length len))
let validate_vector_data len = fun b ->
    if U32.gt (Cast.uint16_to_uint32 len) b.len then None else
    let h = get() in
    parse_vector_length_0 (as_seq h b);
    let v = begin
      do_while_readonly (Some 0us) b.p
      (fun bs m_off break ->
         begin
          match m_off with
          | Some off -> Some? (parse_vector_length_pre off bs) /\
                       (break ==> off == len) /\
                       U16.v off <= U16.v len
          | None -> break == true
         end)
      (fun m_off ->
         let off = Some?.v m_off in
         if U16.eq off len then (Some off, true) else
         begin
          let b' = advance_slice b (Cast.uint16_to_uint32 off) in
          match validate_elem_st b' with
          | Some off' ->
            if U32.gt (U32.add (Cast.uint16_to_uint32 off) off') (Cast.uint16_to_uint32 len) then (None, true) else
            begin
            (let h = get() in
             u16_bound (U16.v off) (U32.v off') len;
             parse_vector_length_pre_extend len (U16.v off) (U32.v off') (as_seq h b));
            (Some (U16.add off (Cast.uint32_to_uint16 off')), false)
            end
          | None -> (None, true)
          end)
    end in
    match v with
    | Some _ -> Some (Cast.uint16_to_uint32 len)
    | None -> None
