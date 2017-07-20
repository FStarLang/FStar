module Validator

open KeyValue
open PureParser
open Slice

open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

module B = FStar.Buffer

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

(*** Stateful validation of input buffer *)

type validation (b:bytes) = option U32.t

unfold let validation_checks_parse #t (b: bytes)
  (v: validation b)
  (p: option (t * n:nat{n <= length b})) : Type0 =
  Some? v ==> (Some? p /\ U32.v (Some?.v v) == snd (Some?.v p))

let parser_st_nochk #t (p: parser t) =
  input:bslice -> ST (t * U32.t)
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                     Some? (p bs))))
  (ensures (fun h0 r h1 -> live h1 input /\
                  h0 == h1 /\
                  (let bs = B.as_seq h1 input.p in
                    Some? (p bs) /\
                    (let (v, n) = Some?.v (p bs) in
                     let (rv, off) = r in
                       v == rv /\
                       n == U32.v off))))

let parser_st #t (p: parser t) =
  input:bslice -> ST (option (t * U32.t))
  (requires (fun h0 -> live h0 input))
  (ensures (fun h0 r h1 -> live h1 input /\
          h0 == h1 /\
          (let bs = B.as_seq h1 input.p in
            match p bs with
            | Some (v, n) -> Some? r /\
              begin
                let (rv, off) = Some?.v r in
                  v == rv /\ n == U32.v off
              end
            | None -> r == None)))

let parse_u16_st_nochk :
  parser_st_nochk (parse_u16) = fun input ->
  let b0 = B.index input.p (U32.uint_to_t 0) in
      let b1 = B.index input.p (U32.uint_to_t 1) in
      let twobytes = append (create 1 b0) (create 1 b1) in
      let h = get() in
      lemma_eq_intro twobytes (slice (as_seq h input) 0 2);
      let n = u16_from_be twobytes in
      (n, U32.uint_to_t 2)

let parse_u16_st : parser_st (parse_u16) = fun input ->
  if U32.lt input.len (U32.uint_to_t 2)
    then None
  else Some (parse_u16_st_nochk input)

let parse_u32_st_nochk :
  parser_st_nochk (parse_u32) = fun input ->
  let b0 = B.index input.p (U32.uint_to_t 0) in
  let b1 = B.index input.p (U32.uint_to_t 1) in
  let b2 = B.index input.p (U32.uint_to_t 2) in
  let b3 = B.index input.p (U32.uint_to_t 3) in
  let fourbytes = create 1 b0 `append` create 1 b1 `append` create 1 b2 `append` create 1 b3 in
  let h = get() in
  lemma_eq_intro fourbytes (slice (as_seq h input) 0 4);
  let n = u32_from_be fourbytes in
  (n, U32.uint_to_t 4)

let parse_u32_st : parser_st (parse_u32) = fun input ->
  if U32.lt input.len (U32.uint_to_t 4)
    then None
    else Some (parse_u32_st_nochk input)

let stateful_validator #t (p: parser t) = input:bslice -> ST (option U32.t)
    (requires (fun h0 -> live h0 input))
    (ensures (fun h0 r h1 -> live h1 input /\
                          h0 == h1 /\
                          (let bs = as_seq h1 input in
                            validation_checks_parse bs r (p bs))))

let validate_u16_array_st : stateful_validator parse_u16_array = fun input ->
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

let validate_u32_array_st : stateful_validator parse_u32_array = fun input ->
  match parse_u32_st input with
  | Some (n, off) -> begin
      // we have to make sure that the total length we compute doesn't overflow
      // a U32.t to correctly check if the input is long enough
      if U32.gte n (U32.uint_to_t (pow2 32 - 4 - 1)) then None
      else begin
        assert (U32.v n + U32.v off < pow2 32);
        let total_len = U32.add n off in
        if U32.lt input.len total_len then None
        else Some total_len
      end
    end
  | None -> None

let then_check #t (p: parser t) (v: stateful_validator p)
               #t' (p': parser t') (v': stateful_validator p')
               #t'' (f: t -> t' -> t'') :
               stateful_validator (p `and_then` (fun x -> p' `and_then` (fun y -> parse_ret (f x y)))) =
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
let validate_entry_st : stateful_validator parse_entry = fun input ->
  then_check parse_u16_array validate_u16_array_st
             parse_u32_array validate_u32_array_st
             (fun key value -> EncodedEntry key.len16 key.a16 value.len32 value.a32) input

val validate_many_st (#t:Type) (p:parser t) (v:stateful_validator p) (n:nat) : stateful_validator (parse_many p n)
let rec validate_many_st #t p v (n:nat) : stateful_validator (parse_many p n) = fun input ->
  match n with
  | 0 -> Some (U32.uint_to_t 0)
  | _ -> let n':nat = n - 1 in
        then_check p v
                   (parse_many p n') (validate_many_st p v n')
                   (fun e es -> e::es) input

let validate_done_st : stateful_validator parsing_done = fun input ->
  if U32.eq input.len (U32.uint_to_t 0) then Some (U32.uint_to_t 0) else None

let validate_entries_st (num_entries:U32.t) : stateful_validator (parse_entries num_entries) =
  fun input ->
  let n = U32.v num_entries in
  then_check (parse_many parse_entry n)
  (validate_many_st parse_entry validate_entry_st n)
  parsing_done validate_done_st
  (fun entries _ -> Store num_entries entries) input

let validate_store_st : stateful_validator parse_abstract_store = fun input ->
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
