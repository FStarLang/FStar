module Parsing

open Slice

open FStar.Tactics
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

type byte = U8.t
let bytes = seq byte
/// the abstract model of input is a sequence of bytes, with a limit on size so
/// offsets always fit in a UInt32.t
let bytes32 = bs:bytes{length bs < pow2 32}

/// parse a value of type t
///
/// - the parser can fail (currently reporting an uninformative [None])
/// - it returns the parsed value as well as the number of bytes read
///   (this is intended to be the number of bytes to advance the input pointer)
///
/// note that the type does not forbid lookahead; the parser can depend on
/// values beyond the returned offset
///
/// these parsers are used as specifications, and thus use unrepresentable types
/// such as byte sequences and natural numbers and are always pure
let parser (t:Type) = b:bytes32 -> Tot (option (t * n:nat{n <= length b}))

/// monadic bind for the parser monad
val and_then : #t:Type -> #t':Type ->
                p:parser t ->
                p': (t -> parser t') ->
                parser t'
let and_then #t #t' p p' b =
  match p b with
  | Some (v, l) ->
    begin
      match p' v (slice b l (length b)) with
      | Some (v', l') -> Some (v', l + l')
      | None -> None
    end
  | None -> None

/// monadic return for the parser monad
unfold let parse_ret (#t:Type) (v:t) : parser t =
  fun _ -> Some (v, 0)

/// parser that always fails
let fail_parser #t : parser t = fun b -> None

/// parser that succeeds iff at the end-of-input
let parsing_done : parser unit =
  fun b -> if length b = 0 then Some ((), 0) else None

/// projector for correctly parsed results
let parse_result (#t:Type) (#b:bytes)
  (r: option (t * n:nat{n <= length b}){Some? r}) : t =
  fst (Some?.v r)

/// repeat a parser `n` times, collecting all the results
val parse_many : #t:Type -> p:parser t -> n:nat -> parser (l:list t{List.length l == n})
let rec parse_many #t p n =
  match n with
  | 0 -> parse_ret []
  | _ -> let n':nat = n-1 in
      p `and_then`
      (fun v -> parse_many #t p n' `and_then`
      (fun l -> parse_ret #(l:list t{List.length l == n}) (v::l)))

/// A stateful parser that implements the same behavior as a pure parser. This
/// includes both the output and offset. The specification parser is an erased
/// type index; erasure helps guide extraction. The type is inlined for
/// extraction to make it clear that parsers are first-order functions taking a
/// buffer as input (as opposed to higher-order implementations that return a
/// function).
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

/// A stateful parser much like parser_st, except that error cases are
/// precluded. The precondition includes that the specification parser succeeds
/// on the input, and under this assumption a parser_st_nochk does not fail and
/// has the same behavior as the specification parser. The implementation need
/// not make error checks since those cases are impossible.
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

/// A validation is an [option U32.t], where [Some off] indicates success and
/// consumes [off] bytes. A validation checks a parse result if it returns [Some
/// off] only when the parser also succeeds and returns the same offset, with
/// any result. Note that a validation need not be complete (in particular,
/// [None] validates any parse).
unfold let validation_checks_parse #t (b: bytes)
  (v: option (off:U32.t{U32.v off <= length b}))
  (p: option (t * n:nat{n <= length b})) : Type0 =
  Some? v ==> (Some? p /\ U32.v (Some?.v v) == snd (Some?.v p))

/// A stateful validator is parametrized by a specification parser. A validator
/// does not produce a value but only checks that the data is valid. The
/// specification ensures that when a validator accepts the input the parser
/// would succeed on the same input.
inline_for_extraction
let stateful_validator #t (p: erased (parser t)) =
  input:bslice ->
  Stack (option (off:U32.t{U32.v off <= U32.v input.len}))
    (requires (fun h0 -> live h0 input))
    (ensures (fun h0 r h1 -> live h1 input /\
                          modifies_none h0 h1 /\
                          (let bs = as_seq h1 input in
                            validation_checks_parse bs r (reveal p bs))))

#reset-options "--z3rlimit 15 --max_fuel 1 --max_ifuel 1"

/// Validators can be composed monoidally, checking two parsers in sequence.
/// This only works when there is no structural dependency: the two parsers
/// always run one after the other. This validator will check any combination of
/// the results of the two parsers.
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

#reset-options

[@"substitute"]
let validate_done_st : stateful_validator (hide parsing_done) = fun input ->
  if U32.eq input.len 0ul then Some 0ul else None

let validate_fail : stateful_validator (hide fail_parser) =
  fun input -> None

#reset-options "--z3rlimit 40 --max_fuel 4 --max_ifuel 1"

let and_then_offset (#t:Type) (p:parser t) (#t':Type) (p':t -> parser t') (bs:bytes32) :
  Lemma (requires (Some? (and_then p p' bs)))
        (ensures (Some? (p bs) /\
                  Some? (and_then p p' bs) /\
                  snd (Some?.v (p bs)) <= snd (Some?.v (and_then p p' bs)))) =
  match p bs with
  | Some (v, off) ->
    match p' v (slice bs off (length bs)) with
    | Some (v', off') -> ()
    | None -> ()
  | None -> ()

val parse_many_parse_one (#t:Type) (p:parser t) (n:nat{n > 0}) (bs:bytes32) :
    Lemma (requires (Some? (parse_many p n bs)))
          (ensures (Some? (p bs) /\
                    Some? (parse_many p n bs) /\
                    snd (Some?.v (p bs)) <= snd (Some?.v (parse_many p n bs))))
let parse_many_parse_one #t p n bs =
  and_then_offset p (fun v -> parse_many #t p (n-1) `and_then`
                     (fun l -> parse_ret #(l:list t{List.length l == n}) (v::l))) bs

// TODO: finish this proof; need to think about the induction more
val validate_n_more (#t:Type) (p:parser t) (n m:nat) (buf:bslice)
    (off:nat{off <= U32.v buf.len}) (off':nat) (h:mem) :
    Lemma (requires (live h buf /\
                    off + off' <= U32.v buf.len /\
                    begin
                      let bs = as_seq h buf in
                      let bs' = slice (as_seq h buf) off (length bs) in
                      Some? (parse_many p n bs) /\
                      off == snd (Some?.v (parse_many p n bs)) /\
                      Some? (parse_many p m bs') /\
                      off' == snd (Some?.v (parse_many p m bs'))
                    end))
          (ensures (live h buf /\
                   begin
                    let bs = as_seq h buf in
                    Some? (parse_many p (n + m) bs) /\
                    off + off' == snd (Some?.v (parse_many p (n + m) bs))
                   end))
    (decreases n)
let rec validate_n_more #t p n m buf off off' h =
    match n with
    | 0 -> ()
    | _ -> let bs = as_seq h buf in
          let bs' = slice (as_seq h buf) off (length bs) in
          parse_many_parse_one p n bs;
          let off_d = snd (Some?.v (p bs)) in
          admit();
          validate_n_more p (n-1) (m+1) buf (off - off_d) (off' + off_d) h;
          ()

#reset-options "--z3rlimit 25"

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
    validate_n_more p n 1 buf (U32.v off) (U32.v off') h

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
          B.frameOf ptr_state == get_tip h1);
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

/// Validate a sequence of values from a parser (corresponding to parse_many).
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

// TODO: this definition is here out of convenience, but should probably go somewhere else
noextract
val normalize : #t:Type -> list norm_step -> t -> Tac unit
let normalize (#t:Type) (steps : list norm_step) (x:t) : Tac unit =
  let x = quote x in
  exact (norm_term (List.append steps [delta; primops]) x)

// original implementation, which behaves slightly differently
noextract
val normalize' : #t:Type -> list norm_step -> t -> Tac unit
let normalize' (#t:Type) (steps : list norm_step) (x:t) : Tac unit =
  dup ();
  exact (quote x);
  norm (FStar.List.Tot.append steps [delta; primops]);
  trefl ()
