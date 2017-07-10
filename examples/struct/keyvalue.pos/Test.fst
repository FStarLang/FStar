module Test

module U16 = FStar.UInt16
module U32 = FStar.UInt32

open FStar.Seq
module List = FStar.List.Tot
module B = FStar.Buffer

type byte = FStar.UInt8.byte
type bytes = seq byte

(*** Binary key-value store parsing ***)

(** We define a simple encoding of a key-value store with variable-length keys
    and values (both byte arrays). So far the experiments here concern parsing
    the key-value store by validating it and then locating keys and values on
    access, using pointers to the input data rather than copying values. *)

type entry: Type0 =
  { key: bytes;
    value: bytes; }

type abstract_store = seq entry

// goal: validate a sequence of bytes to establish a refinement that makes
// reading it later work

(* the binary format of the key-value store is as follows:
   - the number of entries (uint32)
   - variable-length entries consisting of:
     - the key length, in bytes (uint16)
     - the key data
     - the value length, in bytes (uint32)
       the value data

  Validating this format boils down to checking that the number of entries lines up with the sum of the key-value entry lengths, when parsed sequentially.
*)

type encoded_entry =
  | EncodedEntry:
    key_len: U16.t ->
    key: bytes{length key == U16.v key_len} ->
    val_len: U32.t ->
    value: bytes{length value == U32.v val_len} ->
    encoded_entry

type store =
  | Store :
    num_entries:U32.t ->
    entries:list encoded_entry{List.length entries = U32.v num_entries} ->
    store

(*! Spec-level parsing to values *)

// parse a value of type t
// - the parser can fail (currently reporting an uninformative [None])
// - it returns the parsed value as well as the number of bytes read
//   (this is intended to be the number of bytes to advance the input pointer)
let parser (t:Type) = b:bytes -> Tot (option (t * n:nat{n <= length b}))

// parsers form a monad; this is bind for the parser monad
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

// the monadic return for parsers
unfold let parse_ret (#t:Type) (v:t) : parser t =
  fun _ -> Some (v, 0)

let fail_parser #t : parser t = fun b -> None

assume val u16_from_be: b:bytes{length b == 2} -> U16.t

let parse_u16: parser U16.t =
  fun b -> if length b < 2 then None
        else Some (u16_from_be (slice b 0 2), 2)

assume val u32_from_be: b:bytes{length b == 4} -> U32.t

let parse_u32: parser U32.t =
  fun b -> if length b < 4 then None
        else Some (u32_from_be (slice b 0 4), 4)

type u16_array =
  | U16Array : len16:U16.t -> a16:bytes{length a16 == U16.v len16} -> u16_array

val parse_u16_array: parser u16_array
let parse_u16_array =
  parse_u16 `and_then`
  (fun array_len b' ->
    if length b' < U16.v array_len then None
    else let data = slice b' 0 (U16.v array_len) in
    Some (U16Array array_len data, U16.v array_len))

type u32_array =
  | U32Array : len32:U32.t -> a32:bytes{length a32 == U32.v len32} -> u32_array

val parse_u32_array: parser u32_array
let parse_u32_array =
  parse_u32 `and_then`
  (fun array_len b' ->
    if length b' < U32.v array_len then None
    else let data = slice b' 0 (U32.v array_len) in
    Some (U32Array array_len data, U32.v array_len))

val parse_entry : parser encoded_entry
let parse_entry =
  parse_u16_array `and_then`
  (fun key -> parse_u32_array `and_then`
  (fun value ->
  parse_ret (EncodedEntry key.len16 key.a16 value.len32 value.a32)))

let parsing_done : parser unit =
  fun b -> if length b = 0 then Some ((), 0) else None

val parse_many' : #t:Type -> p:parser t -> n:nat -> parser (list t)
let rec parse_many' #t p n =
  match n with
  | 0 -> parse_ret []
  | _ -> p `and_then`
      (fun v -> parse_many' #t p (n-1) `and_then`
      (fun l -> parse_ret (v::l)))

let rec parse_many'_length (#t:Type) (p:parser t) (n:nat) (b:bytes) :
  Lemma (Some? (parse_many' p n b) ==> List.length (fst (Some?.v (parse_many' p n b))) == n) =
  match n with
  | 0 -> ()
  | _ -> match p b with
        | Some (v, l) -> parse_many'_length p (n-1) (slice b l (length b))
        | None -> ()

// XXX: this doesn't work
(*
val parse_many : #t:Type -> p:parser t -> n:nat -> parser (s:seq t{length s == n})
let rec parse_many #t p n =
  if n = 0 then parse_ret createEmpty
    else and_then #t #(s:seq t{length s == n}) p
      (fun v -> and_then #(s:seq t{length s == n-1}) #(s:seq t{length s == n}) (parse_many #t p (n-1))
      (fun l -> parse_ret #(s:seq t{length s == n}) (cons v l)))
*)

val parse_many : #t:Type -> p:parser t -> n:nat -> parser (s:list t{List.length s == n})
let parse_many #t p n b =
  match parse_many' p n b with
  | Some (v, l) -> parse_many'_length p n b; Some (v, l)
  | None -> None

let parse_abstract_store : parser store =
  parse_u32 `and_then`
  (fun num_entries -> parse_many parse_entry (U32.v num_entries) `and_then`
  (fun entries -> parsing_done `and_then`
  (fun _ -> parse_ret (Store num_entries entries))))

(*! Serialization *)

assume val u16_to_be: U16.t -> b:bytes{length b == 2}
assume val u32_to_be: U32.t -> b:bytes{length b == 4}

let encode_u16_array (len:U16.t) (b:bytes{length b == U16.v len}) : bytes =
  u16_to_be len `append` b

let encode_u32_array (len:U32.t) (b:bytes{length b == U32.v len}) : bytes =
  u32_to_be len `append` b

val encode_entry: encoded_entry -> bytes
let encode_entry e = encode_u16_array e.key_len e.key `append` encode_u32_array e.val_len e.value

assume val u16_be_inv: n:U16.t -> Lemma (u16_from_be (u16_to_be n) == n)
                                 [SMTPat (u16_from_be (u16_to_be n))]
assume val u32_be_inv: n:U32.t -> Lemma (u32_from_be (u32_to_be n) == n)
                                 [SMTPat (u32_from_be (u32_to_be n))]


val slice_append_suffix: #a:Type -> s1:seq a -> s2:seq a ->
  n1:nat{n1 == length s1} -> n2:nat{n2 == length (append s1 s2)} ->
  Lemma (slice (append s1 s2) n1 n2 == s2)
  [SMTPat (slice (append s1 s2) n1 n2)]
let slice_append_suffix #a s1 s2 n1 n2 =
  lemma_eq_intro (slice (append s1 s2) n1 n2) s2

val slice_append_prefix: #a:Type -> s1:seq a -> s2:seq a ->
  n1:nat{n1 == length s1} ->
  Lemma (slice (append s1 s2) 0 n1 == s1)
  [SMTPat (slice (append s1 s2) 0 n1)]
let slice_append_prefix #a s1 s2 n1 =
  lemma_eq_intro (slice (append s1 s2) 0 n1) s1

let parse_u16_array_inv (len:U16.t) (b:bytes{length b == U16.v len}) :
    Lemma (parse_u16_array (encode_u16_array len b) == Some (U16Array len b, 2 + U16.v len))
    [SMTPat (parse_u16_array (encode_u16_array len b))] =
  assert (length (encode_u16_array len b) == 2 + U16.v len);
  assert (Some? (parse_u16_array (encode_u16_array len b)));
  ()

let parse_u32_array_inv (len:U32.t) (b:bytes{length b == U32.v len}) :
    Lemma (parse_u32_array (encode_u32_array len b) == Some (U32Array len b, 4 + U32.v len))
    [SMTPat (parse_u32_array (encode_u32_array len b))] =
    assert (length (encode_u32_array len b) == 4 + U32.v len);
    assert (Some? (parse_u32_array (encode_u32_array len b)));
    ()

// TODO: we're in trouble here - we have to argue that the sequential parsing
// can be broken down into parsing appends (which is where the lack of lookahead
// is important)
let encode_entry_inverse (e:encoded_entry) :
  Lemma (parse_entry (encode_entry e) == Some (e, length (encode_entry e))) =
  // assert (Some? (parse_entry (encode_entry e)));
  admit()

val encode: store -> bytes
let encode s = u32_to_be s.num_entries `append`
               (List.fold_left (fun b e -> b `append` encode_entry e)
               createEmpty s.entries)

(*! Validating input buffer *)

(*! Stateful validation *)

open FStar.HyperStack
open FStar.HyperStack.ST

type validation (b:bytes) = option U32.t

unfold let validation_checks_parse #t (b: bytes)
  (v: validation b)
  (p: option (t * n:nat{n <= length b})) : Type0 =
  Some? v ==> (Some? p /\ U32.v (Some?.v v) == snd (Some?.v p))

// a byte buffer type indexed by size
type lbuffer (len: nat) = b:B.buffer byte{B.length b == len}

// augment a buffer with a runtime length
noeq type bslice =
  | BSlice : len:U32.t -> p:lbuffer (U32.v len) -> bslice

let live h (b: bslice) = B.live h b.p
let as_seq h (b: bslice) : Ghost (s:bytes{length s == U32.v b.len})
  (requires (live h b))
  (ensures (fun _ -> True)) = B.as_seq h b.p

let advance_slice (b:bslice) (off:U32.t{U32.v off <= U32.v b.len}) : bslice =
  BSlice (U32.sub b.len off) (B.sub b.p off (U32.sub b.len off))

let advance_slice_spec (b:bslice) (off:U32.t{U32.v off <= U32.v b.len}) h :
  Lemma (requires (live h b))
        (ensures (live h (advance_slice b off) /\
                 as_seq h (advance_slice b off) == slice (as_seq h b) (U32.v off) (length (as_seq h b))))
  = ()

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

module Cast = FStar.Int.Cast

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

let u32_add_overflows (a b:U32.t) : overflow:bool{not overflow <==> U32.v a + U32.v b < pow2 32} =
  U32.lt (U32.add_mod a b) a

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

let parse_entries (num_entries:U32.t) : parser store =
  parse_many parse_entry (U32.v num_entries) `and_then`
  (fun entries -> parsing_done `and_then`
  (fun _ -> parse_ret (Store num_entries entries)))

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

(*! API using validated but unparsed key-value buffer *)

// sufficient to expose iteration over the key-value pairs (specifically pointers to them)

// spec: fold over fully parsed store
val fold_left_store: #t:Type -> f:(t -> encoded_entry -> t) -> t -> s:store -> t
let fold_left_store #t f acc s =
    let rec aux (es: list encoded_entry) (acc:t) : t =
        match es with
        | [] -> acc
        | e::es -> aux es (f acc e) in
    aux s.entries acc

// TODO: this is just computation, right?
assume val fold_left_empty (#t:Type) (f:(t -> encoded_entry -> t)) (acc:t) (s:store) :
  Lemma (requires (s.entries == []))
        (ensures (fold_left_store f acc s == acc))

let rec fold_left_store_n (f:('a -> encoded_entry -> 'a)) (acc:'a)
  (es:list encoded_entry)
  (n:nat{n <= List.length es}) : Tot 'a (decreases n) =
  match n with
  | 0 -> acc
  | _ -> let acc' = f acc (List.hd es) in
        fold_left_store_n f acc' (List.tail es) (n-1)

val fold_left_store_n_spec (f:('a -> encoded_entry -> 'a)) (acc:'a) (s:store) :
  Ghost unit
  (requires True)
  (ensures (fun _ -> fold_left_store_n f acc s.entries (U32.v s.num_entries) == fold_left_store f acc s))
  (decreases (List.length s.entries))
let rec fold_left_store_n_spec f acc s =
  match U32.v s.num_entries with
  | 0 -> fold_left_empty f acc s
  | _ ->
    let n' = U32.sub s.num_entries (U32.uint_to_t 1) in
    fold_left_store_n_spec f (f acc (List.hd s.entries)) (Store n' (List.tail s.entries))

// this is an old experiment with doing a fold_left over a buffer of bytes (pure
// validation); we now have a complete prototype of validators in ST
val fold_left_buffer: #t:Type -> f:(t -> encoded_entry -> t) -> t -> b:bytes -> t
let fold_left_buffer #t f acc b =
    match parse_u32 b with
    | Some (num_entries, l) -> begin
       // we only parse up to n more entries from the buffer b
       let rec aux (n: nat) b acc : t =
         match n with
         | 0 -> acc
         | _ -> begin
           match parse_entry b with
           | Some (e, l) ->
             assert (n > 0);
             aux (n-1) (slice b l (length b)) (f acc e)
           | None -> acc
           end in
         aux (U32.v num_entries) (slice b l (length b)) acc
      end
    | None -> acc

let parse_result (#t:Type) (#b:bytes)
  (r: option (t * n:nat{n <= length b}){Some? r}) : t =
  fst (Some?.v r)

val parse_num_entries_valid : input:bslice -> ST (U32.t * off:U32.t{U32.v off <= U32.v input.len})
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    Some? (parse_abstract_store bs))))
  (ensures (fun h0 r h1 -> // note that live and Some? (parse_abstract_store bs)
                        // come for free due to h0 == h1, but the postcondition
                        // must typecheck without assuming the precondition, so
                        // we re-assert them to discharge obligations within
                        // this postcondition; their proofs should be trivial
                        // due to the function being read-only
                        live h1 input /\
                        h0 == h1 /\
                        begin
                          let bs = as_seq h1 input in
                          Some? (parse_abstract_store bs) /\
                          (let (s, _) = Some?.v (parse_abstract_store bs) in
                           let (rv, r_off) = r in
                           let bs' = slice bs (U32.v r_off) (length bs) in
                           rv == s.num_entries /\
                          (let parse_rest = parse_many parse_entry (U32.v rv) bs' in
                           Some? parse_rest /\
                           s.entries == parse_result parse_rest))
                        end))
let parse_num_entries_valid input =
  let (len, off) = parse_u32_st_nochk input in
  (len, off)

// NOTE: we have variants of each function (spec, stateful validator, stateful
// parser); unfortunately the types also vary since specifications use bytes
// while we only statefully parse buffers. Maybe we should make the byte type a
// parameter? This would work best with a typeclass, since we need a length
// method to encode dependencies (luckily the length of a bslice can be accessed
// without a heap).

noeq type u16_array_st =
  | U16ArraySt : len16_st:U16.t -> a16_st:bslice{U32.v a16_st.len == U16.v len16_st} -> u16_array_st

val truncate_slice : b:bslice -> len:U32.t{U32.v len <= U32.v b.len} -> ST bslice
  (requires (fun h0 -> live h0 b))
  (ensures (fun h0 r h1 -> live h1 b /\
                        live h1 r /\
                        h0 == h1 /\
                        as_seq h1 r == slice (as_seq h1 b) 0 (U32.v len)))
let truncate_slice b len = BSlice len (B.sub b.p (U32.uint_to_t 0) len)

let as_u16_array h (a:u16_array_st) : Ghost u16_array
  (requires (live h a.a16_st))
  (ensures (fun _ -> True)) =
  U16Array a.len16_st (as_seq h a.a16_st)

// TODO: this isn't a parser_st_nochk because its output isn't exactly the same
// as the parser; the relationship requires converting the return value to bytes
let parse_u16_array_nochk : input:bslice -> ST (u16_array_st * off:U32.t{U32.v off <= U32.v input.len})
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    Some? (parse_u16_array bs))))
  (ensures (fun h0 r h1 ->
              live h1 input /\
              h0 == h1 /\
              (let bs = B.as_seq h1 input.p in
                Some? (parse_u16_array bs) /\
                (let (v, n) = Some?.v (parse_u16_array bs) in
                  let (rv, off) = r in
                  // BUG: ommitting this live assertion causes failure in the
                  // precondition to as_u16_array, but the error reported is
                  // simply "ill-kinded type" on as_u16_array
                  live h1 rv.a16_st /\
                  as_u16_array h1 rv == v /\
                  n == U32.v off)))) = fun input ->
  let (len, off) = parse_u16_st_nochk input in
  let input = advance_slice input off in
  let a = U16ArraySt len (truncate_slice input (Cast.uint16_to_uint32 len)) in
  (a, U32.add off (Cast.uint16_to_uint32 len))

noeq type u32_array_st =
  | U32ArraySt : len32_st:U32.t -> a32_st:bslice{U32.v a32_st.len == U32.v len32_st} -> u32_array_st

let as_u32_array h (a:u32_array_st) : Ghost u32_array
  (requires (live h a.a32_st))
  (ensures (fun _ -> True)) =
  U32Array a.len32_st (as_seq h a.a32_st)

let parse_u32_array_nochk : input:bslice -> ST (u32_array_st * off:U32.t)
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    Some? (parse_u32_array bs))))
  (ensures (fun h0 r h1 ->
              live h1 input /\
              h0 == h1 /\
              (let bs = B.as_seq h1 input.p in
                Some? (parse_u32_array bs) /\
                (let (v, n) = Some?.v (parse_u32_array bs) in
                  let (rv, off) = r in
                  live h1 rv.a32_st /\
                  as_u32_array h1 rv == v /\
                  n == U32.v off)))) = fun input ->
  let (len, off) = parse_u32_st_nochk input in
  let input = advance_slice input off in
  let a = U32ArraySt len (truncate_slice input len) in
  (a, U32.add off len)

// an entry with buffers instead of bytes
noeq type entry_st =
  | EntrySt: key_st:u16_array_st ->
             val_st:u32_array_st ->
             entry_st

// TODO: clearly encoded_entry should have a u16_array and a u32_array

// TODO: all of these things that embed buffers need a live method on top
// (really begs for a typeclass..)

let entry_live h (e:entry_st) =
    live h e.key_st.a16_st /\
    live h e.val_st.a32_st

let as_entry h (e:entry_st) : Ghost encoded_entry
  (requires (entry_live h e))
  (ensures (fun _ -> True)) =
  let key = as_u16_array h e.key_st in
  let value = as_u32_array h e.val_st in
  EncodedEntry key.len16 key.a16
               value.len32 value.a32

#reset-options "--z3rlimit 20"

let parse_entry_st_nochk : input:bslice -> ST (entry_st * off:U32.t{U32.v off <= U32.v input.len})
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    Some? (parse_entry bs))))
  (ensures (fun h0 r h1 ->
                live h1 input /\
                h0 == h1 /\
                (let bs = B.as_seq h1 input.p in
                Some? (parse_entry bs) /\
                (let (v, n) = Some?.v (parse_entry bs) in
                  let (rv, off) = r in
                  entry_live h1 rv /\
                  as_entry h1 rv == v /\
                  n == U32.v off)))) = fun input ->
  let (key, off) = parse_u16_array_nochk input in
  let input = advance_slice input off in
  let (value, off') = parse_u32_array_nochk input in
  (EntrySt key value, U32.add off off')

let parse_many_next (#t:Type) (p:parser t) (n:nat{n>0}) (bs:bytes) :
  Lemma (requires (Some? (parse_many p n bs)))
        (ensures (Some? (parse_many p n bs) /\
                  (let (vs, _) = Some?.v (parse_many p n bs) in
                   let (v, off) = Some?.v (p bs) in
                   let rest_parse = parse_many p (n-1) (slice bs off (length bs)) in
                   v == List.hd vs /\
                   Some? rest_parse /\
                   (let (vs', off') = Some?.v rest_parse in
                    vs' == List.tail vs)))) =
  ()

val parse_one_entry : n:nat{n>0} -> input:bslice -> ST (entry_st * off:U32.t{U32.v off <= U32.v input.len})
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                     Some? (parse_many parse_entry n bs))))
  (ensures (fun h0 r h1 -> live h1 input /\
                        h0 == h1 /\
                        begin
                          let bs = as_seq h1 input in
                          Some? (parse_many parse_entry n bs) /\
                          begin
                            let (vs, _) = Some?.v (parse_many parse_entry n bs) in
                            let (rv, r_off) = r in
                            entry_live h1 rv /\
                            // as_entry h1 rv == parse_result (parse_entry bs) /\
                            as_entry h1 rv == List.hd vs /\
                            begin
                              let bs' = slice bs (U32.v r_off) (length bs) in
                              let parse_rest = parse_many parse_entry (n-1) bs' in
                              Some? parse_rest /\
                                (let (vs', off') = Some?.v parse_rest in
                                 vs' == List.tail vs)
                            end
                          end
                        end))
let parse_one_entry n input =
  (let h = get() in
   let bs = as_seq h input in
   parse_many_next parse_entry n bs);
  parse_entry_st_nochk input

#reset-options

val fold_left_buffer_n_st: #t:Type -> f_spec:(t -> encoded_entry -> t) ->
  f:(acc:t -> e:entry_st -> ST t
    (requires (fun h0 -> entry_live h0 e))
    (ensures (fun h0 r h1 -> entry_live h1 e /\
                          h0 == h1 /\
                          r == f_spec acc (as_entry h1 e)))) ->
  acc:t -> input:bslice -> n:nat -> ST t
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    Some? (parse_many parse_entry n bs))))
  (ensures (fun h0 r h1 -> live h1 input /\
                        h0 == h1 /\
                        (let bs = as_seq h1 input in
                        Some? (parse_many parse_entry n bs) /\
                        r == fold_left_store_n f_spec acc (parse_result (parse_many parse_entry n bs)) n)))
let rec fold_left_buffer_n_st #t f_spec f acc input n =
    match n with
    | 0 -> acc
    | _ -> begin
      let (e, off) = parse_one_entry n input in
      let input = advance_slice input off in
      let n':nat = n-1 in
      let acc' = f acc e in
      let h = get() in
      assert (let bs = as_seq h input in
              Some? (parse_many parse_entry n' bs));
      let r = fold_left_buffer_n_st f_spec f acc' input n' in
      r
    end

val fold_left_buffer_st: #t:Type -> f_spec:(t -> encoded_entry -> t) ->
  f:(acc:t -> e:entry_st -> ST t
    (requires (fun h0 -> entry_live h0 e))
    (ensures (fun h0 r h1 -> entry_live h1 e /\
                          h0 == h1 /\
                          r == f_spec acc (as_entry h1 e)))) ->
  acc:t -> input:bslice -> ST t
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    Some? (parse_abstract_store bs))))
  (ensures (fun h0 r h1 -> live h1 input /\
                        h0 == h1 /\
                        (let bs = as_seq h1 input in
                        Some? (parse_abstract_store bs) /\
                        r == fold_left_store f_spec acc (parse_result (parse_abstract_store bs)))))
let fold_left_buffer_st #t f_spec f acc input =
  let (num_entries, off) = parse_num_entries_valid input in
  (let h = get() in
   let bs = as_seq h input in
   let (s, _) = Some?.v (parse_abstract_store bs) in
   fold_left_store_n_spec f_spec acc s;
   assert (num_entries == s.num_entries));
  let input = advance_slice input off in
  fold_left_buffer_n_st f_spec f acc input (U32.v num_entries)

(*! Pure validation *)

let validator = parser unit
// let parse_validator #t (p:parser t) = b:bytes -> (ok:bool{ok <==> Some? (p b)} * n:nat{n <= length b})

unfold let seq (#t:Type) (#t':Type) (p:parser t) (p': parser t') : parser t' =
  fun b -> match p b with
        | Some (_, l) -> begin
                match p' (slice b l (length b)) with
                | Some (v, l') -> Some (v, l + l')
                | None -> None
          end
        | None -> None

unfold let invalid (#b:bytes): option (unit * n:nat{n <= length b}) = None
unfold let valid (#b:bytes) (n:nat{n <= length b}) : option (unit * n:nat{n <= length b}) = Some ((), n)

let skip_bytes (n:nat) : validator =
  fun b -> if length b < n then invalid
        else valid n

// this is analogous to the stateful version, validation_check_parse, but pure
// validators are a special case of parsers and don't return quite the same
// thing
unfold let parser_validation_checks_parse #t (b: bytes)
  (v: option (unit * n:nat{n <= length b}))
  (p: option (t * n:nat{n <= length b})) : Type0 =
  Some? v ==> (Some? p /\ snd (Some?.v v) == snd (Some?.v p))

unfold let validator_checks_on (v:validator) #t (p: parser t) (b:bytes) = parser_validation_checks_parse b (v b) (p b)

// NOTE: this proof about the whole validator works better than a function with
// built-in correctness proof (despite the universal quantifier)
(** a correctness condition for a validator, stating that it correctly reports
    when a parser will succeed (the implication only needs to be validated ==>
    will parse, but this has worked so far) *)
unfold let validator_checks (v:validator) #t (p: parser t) = forall b. validator_checks_on v p b

// this definitions assists type inference by forcing t'=unit; it also makes the
// code read a bit better
unfold let then_validate (#t:Type) (p:parser t) (v:t -> validator) : validator =
    and_then p v

val validate_u16_array: v:validator{validator_checks v parse_u16_array}
let validate_u16_array =
  parse_u16 `then_validate`
  (fun array_len -> skip_bytes (U16.v array_len))

val validate_u32_array: v:validator{validator_checks v parse_u32_array}
let validate_u32_array =
  parse_u32 `then_validate`
  (fun array_len -> skip_bytes (U32.v array_len))

let validate_entry: v:validator{validator_checks v parse_entry} =
  validate_u16_array `seq`
  validate_u32_array

unfold let validate_accept : validator =
  fun b -> valid 0
unfold let validate_reject : validator =
  fun b -> invalid

val validate_many':
  n:nat ->
  v:validator ->
  v':validator
let rec validate_many' n v =
  match n with
  | 0 -> validate_accept
  | _ -> v `seq` validate_many' (n-1) v

let validate_seq (#t:Type) (#t':Type)
  (p: parser t) (p': parser t')
  (v: validator{validator_checks v p})
  (v': validator{validator_checks v' p'}) :
  Lemma (validator_checks (v `seq` v') (p `seq` p')) = ()

#set-options "--max_fuel 0 --z3rlimit 30"

let validate_liftA2 (#t:Type) (#t':Type) (#t'':Type)
  (p: parser t) (p': parser t') (f: t -> t' -> t'')
  (v: validator{validator_checks v p})
  (v': validator{validator_checks v' p'}) :
  Lemma (validator_checks (v `seq` v') (p `and_then` (fun (x:t) -> p' `and_then` (fun (y:t') -> parse_ret (f x y))))) =
  assert (forall x. validator_checks v' (p' `and_then` (fun y -> parse_ret (f x y))));
  assert (forall b. match v b with
               | Some (_, l) -> Some? (p b) /\ snd (Some?.v (p b)) == l
               | None -> true);
  ()

#reset-options "--z3rlimit 50"

let rec validate_many'_ok (n:nat) (#t:Type) (p: parser t) (v:validator{validator_checks v p}) :
  Lemma (validator_checks (validate_many' n v) (parse_many' p n)) =
  match n with
  | 0 -> ()
  | _ -> validate_many'_ok (n-1) p v;
        let p' = parse_many' p (n-1) in
        let v': v:validator{validator_checks v p'} = validate_many' (n-1) v in
        validate_liftA2 p p' (fun v l -> v::l) v v';
        ()

#reset-options

val validate_many:
  #t:Type -> p:parser t ->
  n:nat ->
  v:validator{validator_checks v p} ->
  v':validator{validator_checks v' (parse_many p n)}
let validate_many #t p n v = validate_many'_ok n p v; validate_many' n v

let validate_done : v:validator{validator_checks v parsing_done} =
  fun b -> if length b = 0 then valid 0
        else invalid

// TODO: tie together pieces to prove this overall correctness result
val validate: v:validator{validator_checks v parse_abstract_store}
let validate =
  admit();
  parse_u32 `then_validate`
  (fun num_entries -> validate_many parse_entry (U32.v num_entries) validate_entry `seq`
                   validate_done)

(*! Skipping bounds checks due to validation *)

// Another aspect to verify is that the bounds checks can be skipped. This
// can be done even in pure F*, but is more obvious in effectful F* where we
// prove safety of pointer arithmetic.

// note that there are no bounds checks here; they are instead asserted and
// proven through the validation
let parse_valid_u16_array (b:bytes{Some? (validate_u16_array b)}) : a:u16_array{parse_result (parse_u16_array b) == a} =
  // these asserts are for illustration only; in this simple example Z3 proves the
  // right bounds automatically from the refinements on [slice].
  assert (length b >= 2);
  let len = u16_from_be (slice b 0 2) in
  assert (length (slice b 2 (length b)) >= U16.v len);
  let data = slice b 2 (2+U16.v len) in
  U16Array len data

let parse_valid_u32_array (b:bytes{Some? (validate_u32_array b)}) : a:u32_array{parse_result (parse_u32_array b) == a} =
  let len = u32_from_be (slice b 0 4) in
  let data = slice b 4 (4+U32.v len) in
  U32Array len data

assume val parse_valid_entry (b:bytes{Some? (validate_entry b)}) : e:encoded_entry{parse_result (parse_entry b) == e}
  // TODO: unfortunately these validated parsers don't return how much data they
  // consumed like normal parsers, so chaining them will require separately
  // computing these lengths (based on the length of the array returned))

  // TODO: the underlying reason is that a validated parser is a special case of
  // a parser, but with a refinement on both the result type _and_ the input
  // b:bytes, which can't even possibly be expressed using the [parser] type.

(*! Parsing a cache *)

// TODO: currently have:
// parser: produce a struct fully representing the input buffer
// validator: check if the input is well-formed, outputting true/false
// a validator is a [parser ()] with a correctness condition relating to a real parser

// want an intermediate: a parser that produces some value (a cache) with an API
// and a proof that the parser + API is the same as the ghost parser (which
// produces a complete struct) and a ghost API (which might just be field/array
// accesses)

unfold let optbind (#t:Type) (#t':Type) (x:option t) (f:t -> option t') : option t' =
  match x with
  | Some v -> f v
  | None -> None

let parse_value_offset (b:bytes) : option (n:nat{n <= length b}) =
 parse_u16_array b `optbind`
 (fun (_, l) ->
    // NOTE: we don't need to slice out the value array, only validate its
    // length (so that b is parseable as an entry); the slice of the remaining
    // input should become part of the parser incrementing a current position
    // pointer into the input buffer
    validate_u32_array (slice b l (length b)) `optbind`
    (fun _ -> Some l))

let parse_value_offset_ok (b:bytes) :
  Lemma (parse_value_offset b `optbind`
    (fun n -> parse_u32_array (slice b n (length b)) `optbind`
    (fun (a, _) -> Some (a.a32 <: bytes))) ==
      parse_entry b `optbind`
      (fun (e, _) -> Some e.value)) = ()
