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

unfold let validation_checks_parse #t (b: bytes)
  (v: option (off:U32.t{U32.v off <= length b}))
  (p: option (t * n:nat{n <= length b})) : Type0 =
  Some? v ==> (Some? p /\ U32.v (Some?.v v) == snd (Some?.v p))

inline_for_extraction
let parser_st_nochk #t (p: parser t) =
  input:bslice -> Stack (t * off:U32.t{U32.v off <= U32.v input.len})
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                     Some? (p bs))))
  (ensures (fun h0 r h1 -> live h1 input /\
                  modifies_none h0 h1 /\
                  (let bs = B.as_seq h1 input.p in
                    Some? (p bs) /\
                    (let (v, n) = Some?.v (p bs) in
                     let (rv, off) = r in
                       v == rv /\
                       n == U32.v off))))

inline_for_extraction
let parser_st #t (p: parser t) =
  input:bslice -> Stack (option (t * off:U32.t{U32.v off <= U32.v input.len}))
  (requires (fun h0 -> live h0 input))
  (ensures (fun h0 r h1 -> live h1 input /\
          modifies_none h0 h1 /\
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
  let b0 = B.index input.p 0ul in
      let b1 = B.index input.p 1ul in
      begin
        let h = get() in
        let twobytes = append (create 1 b0) (create 1 b1) in
        lemma_eq_intro twobytes (slice (as_seq h input) 0 2)
      end;
      let n = u16_from_bytes b0 b1 in
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

unfold
let stateful_validator #t (p: parser t) = input:bslice -> Stack (option (off:U32.t{U32.v off <= U32.v input.len}))
    (requires (fun h0 -> live h0 input))
    (ensures (fun h0 r h1 -> live h1 input /\
                          modifies_none h0 h1 /\
                          (let bs = as_seq h1 input in
                            validation_checks_parse bs r (p bs))))

#reset-options "--z3rlimit 10"

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

inline_for_extraction
let u32_array_bound: U32.t = 4294967291ul

let u32_array_bound_is (_:unit) :
  Lemma (U32.v u32_array_bound = pow2 32 - 4 - 1) = ()

let validate_u32_array_st : stateful_validator parse_u32_array = fun input ->
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

// TODO: oops, how do we import C.Loops? we need kremlib on the include path...

(* To be extracted as:
    int i = <start>;
    bool b = false;
    for (; (!b) && (i != <end>); ++i) {
      b = <f> i;
    }
    // i and b must be in scope after the loop
*)
val interruptible_for:
  start:U32.t ->
  finish:U32.t{U32.v finish >= U32.v start} ->
  inv:(mem -> nat -> bool -> GTot Type0) ->
  f:(i:U32.t{U32.(v start <= v i /\ v i < v finish)} -> Stack bool
                        (requires (fun h -> inv h (U32.v i) false))
                        (ensures (fun h_1 b h_2 -> inv h_1 (U32.v i) false /\ inv h_2 U32.(v i + 1) b)) ) ->
  Stack (U32.t * bool)
    (requires (fun h -> inv h (U32.v start) false))
    (ensures (fun _ res h_2 -> let (i, b) = res in ((if b then True else i == finish) /\ inv h_2 (U32.v i) b)))
let rec interruptible_for start finish inv f =
  if start = finish then
    (finish, false)
  else
    let start' = U32.(start +^ 1ul) in
    if f start
    then (start', true)
    else interruptible_for start' finish inv f

module HH = FStar.Monotonic.HyperHeap

val modifies_one_trans (r:HH.rid) (h0 h1 h2:mem) :
    Lemma (requires (modifies_one r h0 h1 /\
                     modifies_one r h1 h2))
          (ensures (modifies_one r h0 h2))
let modifies_one_trans r h0 h1 h2 = ()

#reset-options "--z3rlimit 25"

val parse_many_parse_one (#t:Type) (p:parser t) (n:nat{n > 0}) (bs:bytes) :
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
    validate_n_more p n 1 buf off off' h

val validate_many_st (#t:Type) (p:parser t) (v:stateful_validator p) (n:U32.t) :
    stateful_validator (parse_many p (U32.v n))
let validate_many_st #t p v n = fun buf ->
    let h0 = get() in
    push_frame();
    let ptr_off = salloc #(n:U32.t{U32.v n <= U32.v buf.len}) 0ul in
    let h0' = get() in
    let (i, failed) = interruptible_for 0ul n
      (fun h i failed ->
        live h buf /\
        contains h ptr_off /\
        poppable h /\
        modifies_one ptr_off.id h0' h /\
        begin
          let bs = as_seq h buf in
          not failed ==> Some? (parse_many p i bs) /\
                         U32.v (sel h ptr_off) == snd (Some?.v (parse_many p i bs))
        end)
      (fun i -> let h = get() in
             let off = !ptr_off in
             let buf' = advance_slice buf off in
             match v buf' with
             | Some off' ->
              if u32_add_overflows off off' then true
              else (ptr_off := U32.(off +^ off');
                   let h1 = get() in
                   modifies_one_trans ptr_off.id h0' h h1;
                   validate_one_more p (U32.v i) buf off off' h1;
                   false)
             | None -> true) in
    let off = !ptr_off in
    pop_frame();
    if failed then None
    // why is the invariant insufficient to prove this?
    else (admit(); Some off)

let validate_done_st : stateful_validator parsing_done = fun input ->
  if U32.eq input.len 0ul then Some 0ul else None

let validate_entries_st (num_entries:U32.t) : stateful_validator (parse_entries num_entries) =
  fun input ->
  then_check (parse_many parse_entry (U32.v num_entries))
  (validate_many_st parse_entry validate_entry_st num_entries)
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
