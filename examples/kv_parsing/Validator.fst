module Validator

open KeyValue
open PureParser
open Slice

open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST
module C = C
// special kremlin support for looping
open C.Loops

module B = FStar.Buffer

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

(*** Stateful validation of input buffer *)

inline_for_extraction
let parser_st_nochk #t (p: erased (parser t)) =
  input:bslice -> Stack (t * off:U32.t{U32.v off <= U32.v input.len})
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                     Some? (reveal p bs))))
  (ensures (fun h0 r h1 -> live h1 input /\
                  modifies_none h0 h1 /\
                  (let bs = B.as_seq h1 input.p in
                    Some? (reveal p bs) /\
                    (let (v, n) = Some?.v (reveal p bs) in
                     let (rv, off) = r in
                       v == rv /\
                       n == U32.v off))))

inline_for_extraction
let parser_st #t (p: erased (parser t)) =
  input:bslice -> Stack (option (t * off:U32.t{U32.v off <= U32.v input.len}))
  (requires (fun h0 -> live h0 input))
  (ensures (fun h0 r h1 -> live h1 input /\
          modifies_none h0 h1 /\
          (let bs = as_seq h1 input in
            match reveal p bs with
            | Some (v, n) -> Some? r /\
              begin
                let (rv, off) = Some?.v r in
                  v == rv /\ n == U32.v off
              end
            | None -> r == None)))

let parse_u8_st_nochk :
    parser_st_nochk (hide parse_u8) = fun input ->
    let b0 = B.index input.p 0ul in
    (b0, 1ul)

let parse_u8_st : parser_st (hide parse_u8) = fun input ->
    if U32.lt input.len 1ul then None
    else (Some (parse_u8_st_nochk input))

let parse_u16_st_nochk :
  parser_st_nochk (hide parse_u16) = fun input ->
  let n = C.load16_be (truncated_slice input 2ul).p in
  (n, 2ul)

let parse_u16_st : parser_st (hide parse_u16) = fun input ->
  if U32.lt input.len 2ul
    then None
  else Some (parse_u16_st_nochk input)

let parse_u32_st_nochk :
  parser_st_nochk (hide parse_u32) = fun input ->
  let n = C.load32_be (truncated_slice input 4ul).p in
  (n, 4ul)

let parse_u32_st : parser_st (hide parse_u32) = fun input ->
  if U32.lt input.len 4ul
    then None
    else Some (parse_u32_st_nochk input)

unfold let validation_checks_parse #t (b: bytes)
  (v: option (off:U32.t{U32.v off <= length b}))
  (p: option (t * n:nat{n <= length b})) : Type0 =
  Some? v ==> (Some? p /\ U32.v (Some?.v v) == snd (Some?.v p))

// TODO: unfold is only for extraction
unfold
inline_for_extraction
let stateful_validator #t (p: erased (parser t)) = input:bslice -> Stack (option (off:U32.t{U32.v off <= U32.v input.len}))
    (requires (fun h0 -> live h0 input))
    (ensures (fun h0 r h1 -> live h1 input /\
                          modifies_none h0 h1 /\
                          (let bs = as_seq h1 input in
                            validation_checks_parse bs r (reveal p bs))))

#reset-options "--z3rlimit 10"

let validate_u16_array_st : stateful_validator (hide parse_u16_array) = fun input ->
  match parse_u16_st input with
  | Some (n, off) -> begin
      let n: U32.t = Cast.uint16_to_uint32 n in
      // overflow is not possible here, since n < pow2 16 and off == 2
      // (any encodable length would fit in a U32)
      let total_len = U32.add n off in
      if U32.lt input.len total_len then None
      else Some total_len
    end
  | None -> None

inline_for_extraction
let u32_array_bound: U32.t = 4294967291ul

let u32_array_bound_is (_:unit) :
  Lemma (U32.v u32_array_bound = pow2 32 - 4 - 1) = ()

let validate_u32_array_st : stateful_validator (hide parse_u32_array) = fun input ->
  match parse_u32_st input with
  | Some (n, off) -> begin
      // we have to make sure that the total length we compute doesn't overflow
      // a U32.t to correctly check if the input is long enough
      if U32.gte n u32_array_bound then None
      else begin
        assert (U32.v n + U32.v off < pow2 32);
        let total_len = U32.add n off in
        if U32.lt input.len total_len then None
        else Some total_len
      end
    end
  | None -> None

[@"substitute"]
let then_check #t (p: erased (parser t)) (v: stateful_validator p)
               #t' (p': erased (parser t')) (v': stateful_validator p')
               #t'' (f: t -> t' -> t'') :
               stateful_validator (elift2 (fun p p' -> p `and_then` (fun x -> p' `and_then` (fun y -> parse_ret (f x y)))) p p') =
fun input ->
  match v input with
  | Some off -> begin
      match v' (advance_slice input off) with
      | Some off' -> (if u32_add_overflows off off' then None
                   else Some (U32.add off off'))
      | None -> None
    end
  | None -> None

// eta expansion is necessary to get the right subtyping check
let validate_entry_st : stateful_validator (hide parse_entry) = fun input ->
  then_check (hide parse_u16_array) validate_u16_array_st
             (hide parse_u32_array) validate_u32_array_st
             (fun key value -> EncodedEntry key.len16 key.a16 value.len32 value.a32) input

module HH = FStar.Monotonic.HyperHeap

val modifies_one_trans (r:HH.rid) (h0 h1 h2:mem) :
    Lemma (requires (modifies_one r h0 h1 /\
                     modifies_one r h1 h2))
          (ensures (modifies_one r h0 h2))
let modifies_one_trans r h0 h1 h2 = ()

#reset-options "--z3rlimit 25"

val parse_many_parse_one (#t:Type) (p:parser t) (n:nat{n > 0}) (bs:bytes{length bs < pow2 32}) :
    Lemma (requires (Some? (parse_many p n bs)))
          (ensures (Some? (p bs)))
let parse_many_parse_one #t p n bs = ()

// TODO: finish this proof; need to think about the induction more
val validate_n_more (#t:Type) (p:parser t) (n m:nat) (buf:bslice)
    (off:U32.t{U32.v off <= U32.v buf.len}) (off':U32.t) (h:mem) :
    Lemma (requires (live h buf /\
                    U32.v off + U32.v off' <= U32.v buf.len /\
                    begin
                      let bs = as_seq h buf in
                      let bs' = as_seq h (advance_slice buf off) in
                      Some? (parse_many p n bs) /\
                      U32.v off == snd (Some?.v (parse_many p n bs)) /\
                      Some? (parse_many p m bs') /\
                      U32.v off' == snd (Some?.v (parse_many p m bs'))
                    end))
          (ensures (live h buf /\
                   begin
                    let bs = as_seq h buf in
                    Some? (parse_many p (n + m) bs) /\
                    U32.v off + U32.v off' == snd (Some?.v (parse_many p (n + m) bs))
                   end))
    (decreases n)
let rec validate_n_more #t p n m buf off off' h =
    match n with
    | 0 -> ()
    | _ -> let bs = as_seq h buf in
          let bs' = as_seq h (advance_slice buf off) in
          parse_many_parse_one p n bs;
          let off_d = snd (Some?.v (p bs)) in
          let off_d_u32 = U32.uint_to_t off_d in
          admit();
          validate_n_more p (n-1) (m+1) buf (U32.add off off_d_u32) (U32.sub off' off_d_u32) h

val validate_one_more (#t:Type) (p:parser t) (n:nat) (buf:bslice)
    (off:U32.t{U32.v off <= U32.v buf.len}) (off':U32.t) (h:mem) :
    Lemma (requires (live h buf /\
                    U32.v off + U32.v off' <= U32.v buf.len /\
                    begin
                      let bs = as_seq h buf in
                      let bs' = as_seq h (advance_slice buf off) in
                      Some? (parse_many p n bs) /\
                      U32.v off == snd (Some?.v (parse_many p n bs)) /\
                      Some? (p bs') /\
                      U32.v off' == snd (Some?.v (p bs'))
                    end))
          (ensures (live h buf /\
                   begin
                    let bs = as_seq h buf in
                    Some? (parse_many p (n + 1) bs) /\
                    U32.v off + U32.v off' == snd (Some?.v (parse_many p (n + 1) bs))
                   end))
let validate_one_more #t p n buf off off' h =
    let bs' = as_seq h (advance_slice buf off) in
    assert (Some? (parse_many p 1 bs') == Some? (p bs'));
    assert (snd (Some?.v (parse_many p 1 bs')) == snd (Some?.v (p bs')));
    validate_n_more p n 1 buf off off' h

// TODO: get this to extract in validate_many_st (even unfold doesn't work,
// though it at least gets to an error "todo: translate_expr [MLE_App]")
//unfold
[@"substitute"]
val for_readonly :
  #t:Type0 ->
  init:t ->
  start:U32.t ->
  finish:U32.t{U32.v finish >= U32.v start} ->
  #a:Type ->
  // buf is logical; it can be captured by f at runtime
  buf:B.buffer a ->
  inv:(vs:seq a{length vs == B.length buf} -> nat -> t -> bool -> GTot Type0) ->
  f:(i:U32.t{U32.(v start <= v i /\ v i < v finish)} -> v:t -> Stack (t * bool)
     (requires (fun h0 -> B.live h0 buf /\
                       inv (B.as_seq h0 buf) (U32.v i) v false))
     (ensures (fun h0 r h1 -> let (v', break) = r in
                           B.live h0 buf /\
                           B.live h1 buf /\
                           inv (B.as_seq h0 buf) (U32.v i) v false /\
                           inv (B.as_seq h1 buf) U32.(v i + 1) v' break /\
                           modifies_none h0 h1))) ->
  Stack (U32.t * t * bool)
    (requires (fun h0 -> B.live h0 buf /\
                      inv (B.as_seq h0 buf) (U32.v start) init false))
    (ensures (fun h0 r h1 -> let (i, v, break) = r in
                          (not break ==> i == finish) /\
                          B.live h1 buf /\
                          inv (B.as_seq h1 buf) (U32.v i) v break /\
                          modifies_none h0 h1))
let for_readonly #t init start finish #a buf inv f =
  let h0 = get() in
  push_frame();
  let h1 = get() in
  let ptr_state = B.create #t init 1ul in
  assert (ptr_state `B.unused_in` h1 /\
          B.frameOf ptr_state == h1.tip);
  let h = get() in
  let (i, break) = begin
    interruptible_for start finish
    (fun h i break ->
      B.live h buf /\
      B.live h ptr_state /\
      B.modifies_0 h1 h /\
      inv (B.as_seq h buf) i (Seq.index (B.as_seq h ptr_state) 0) break)
    (fun i -> let h0' = get() in
           let v = B.index ptr_state 0ul in
           let (v', break) = f i v in
           let h1' = get() in
           B.upd ptr_state 0ul v';
           let h2' = get() in
           B.lemma_modifies_none_1_trans ptr_state h0' h1' h2';
           B.lemma_modifies_0_unalloc ptr_state h1 h0' h2';
           break)
    end in
  let v = B.index ptr_state 0ul in
  let h2 = get() in
  pop_frame();
  let h3 = get() in
  B.lemma_modifies_0_push_pop h0 h1 h2 h3;
  (i, v, break)

inline_for_extraction [@"substitute"]
val validate_many_st (#t:Type) (p:erased (parser t)) (v:stateful_validator p) (n:U32.t) :
    stateful_validator (elift1 (fun p -> (parse_many p (U32.v n))) p)
let validate_many_st #t p v n = fun buf ->
    let (_, off, failed) = for_readonly #(n:U32.t{U32.v n <= U32.v buf.len}) 0ul 0ul n buf.p
      (fun bs i off failed ->
        not failed ==>
          validation_checks_parse bs
            (Some off) (parse_many (reveal p) i bs))
      (fun i off ->
        let buf' = advance_slice buf off in
        match v buf' with
        | Some off' -> begin
          let h = get() in
          validate_one_more (reveal p) (U32.v i) buf off off' h;
          (U32.(off +^ off'), false)
          end
        | None -> (off, true)) in
    if failed then None else Some off

[@"substitute"]
let validate_done_st : stateful_validator (hide parsing_done) = fun input ->
  if U32.eq input.len 0ul then Some 0ul else None

val validate_entries_st (num_entries:U32.t) : stateful_validator (hide (parse_entries num_entries))
let validate_entries_st (num_entries:U32.t) =
  fun input ->
  // XXX: explicitly annotating this type is terrible
  then_check (elift1 (fun p -> parse_many p (U32.v num_entries)) (hide parse_entry))
  (validate_many_st (hide parse_entry) validate_entry_st num_entries)
  (hide parsing_done) validate_done_st
  (fun entries _ -> Store num_entries entries) input

let validate_store_st : stateful_validator (hide parse_abstract_store) = fun input ->
  match parse_u32_st input with
  | Some (num_entries, off) ->
    begin
      let input = advance_slice input off in
      match validate_entries_st num_entries input with
      | Some off' -> if u32_add_overflows off off' then None
                    else Some (U32.add off off')
      | None -> None
    end
  | None -> None
