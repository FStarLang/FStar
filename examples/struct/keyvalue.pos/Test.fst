module Test

module U16 = FStar.UInt16
module U32 = FStar.UInt32

open FStar.Seq
module List = FStar.List.Tot

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
let parse_ret (#t:Type) (v:t) : parser t =
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

val parse_u16_array: parser (a:(U16.t * bytes){length (snd a) == U16.v (fst a)})
let parse_u16_array =
  and_then #(U16.t) #(a:(U16.t * bytes){length (snd a) == U16.v (fst a)}) parse_u16
  (fun array_len b' ->
    if length b' < U16.v array_len then None
    else let data = slice b' 0 (U16.v array_len) in
          Some ((array_len, data), U16.v array_len))

val parse_u32_array: parser (a:(U32.t * bytes){length (snd a) == U32.v (fst a)})
let parse_u32_array =
  and_then #(U32.t) #(a:(U32.t * bytes){length (snd a) == U32.v (fst a)}) parse_u32
  (fun array_len b' ->
    if length b' < U32.v array_len then None
    else let data = slice b' 0 (U32.v array_len) in
        Some ((array_len, data), U32.v array_len))

val parse_entry : parser encoded_entry
let parse_entry = parse_u16_array `and_then`
  (fun key_and_len -> parse_u32_array `and_then`
  (fun val_and_len ->
  let (key_len, key) = key_and_len in
  let (val_len, value) = val_and_len in
  parse_ret (EncodedEntry key_len key val_len value)
  ))

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
    Lemma (parse_u16_array (encode_u16_array len b) == Some ((len, b), 2 + U16.v len))
    [SMTPat (parse_u16_array (encode_u16_array len b))] =
  assert (length (encode_u16_array len b) == 2 + U16.v len);
  assert (Some? (parse_u16_array (encode_u16_array len b)));
  ()

let parse_u32_array_inv (len:U32.t) (b:bytes{length b == U32.v len}) :
    Lemma (parse_u32_array (encode_u32_array len b) == Some ((len, b), 4 + U32.v len))
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

let invalid (#b:bytes): option (unit * n:nat{n <= length b}) = None
let valid (#b:bytes) (n:nat{n <= length b}) : option (unit * n:nat{n <= length b}) = Some ((), n)

let skip_bytes (n:nat) : validator =
  fun b -> if length b < n then invalid
        else valid n

// NOTE: this proof about the whole validator works better than a function with
// built-in correctness proof (despite the universal quantifier)
(** a correctness condition for a validator, stating that it correctly reports
   when a parser will succeed (the implication only needs to be validated ==>
   will parse, but this has worked so far) *)
unfold let validator_checks (v:validator) #t (p: parser t) = forall b. Some? (v b) ==> (Some? (p b) /\ snd (Some?.v (v b)) == snd (Some?.v (p b)))

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

let validate_accept : validator =
  fun b -> valid 0
let validate_reject : validator =
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
  ()

let rec validate_many'_ok (n:nat) (#t:Type) (p: parser t) (v:validator{validator_checks v p}) :
  Lemma (requires True)
        (ensures (validator_checks (validate_many' n v) (parse_many' p n))) =
  match n with
  | 0 -> ()
  | _ -> validate_many'_ok (n-1) p v;
        let p' = parse_many' p (n-1) in
        validate_liftA2 p p' (fun v l -> v::l) v (validate_many' (n-1) v <: (v:validator{validator_checks v p'}));
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
                   validate_done `seq`
                   validate_accept)

(*! API using validated but unparsed key-value buffer *)

// sufficient to expose iteration over the key-value pairs (specifically pointers to them)
// TODO: write this in stateful F*; not clear what a useful pure model would be

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
    (fun ((_, a), _) -> Some (a <: bytes))) ==
      parse_entry b `optbind`
      (fun (e, _) -> Some e.value)) = ()
