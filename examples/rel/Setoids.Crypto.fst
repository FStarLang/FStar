module Setoids.Crypto
module L = Setoids
open FStar.Integers
open FStar.Map

let byte = uint_8

/// an infinite tape of byte values indexed by nat
///
/// There are many possible ways to model random sampling
/// from an infinite tape.
///
/// Here, we use a style from POPL '04
///   -- we're only going to sample from position 0
///   -- and we'll advance the tape as we sample from it
///
///      It has a downside of consuming the prefix of the tape
///      making it unavailable for reasoning.
///
///      Maybe we'll revise it
let tape = nat -> Tot byte

let truncate (t:tape) (n:nat) : tape =
  fun m -> t (m + n)

/// The type of effectful computations with 3 effects
///    1. random sampling
///    2. reading and writing state
///    3. raising exceptions
let eff (st:Type) (a:Type) =
  tape & st ->  //input tape and initial state
  Tot (option a &  //normal return (Some _) or exception (None)
       st &        //final state
       nat)          //amount of tape consumed

/// Note: F* provides syntactic sugar for monadic computations, as
/// follows
///
/// 1. bind e1 (fun x -> e2)
///
///    can be written instead as
///
///    x <-- e1;
///    e2
///
/// 2. bind e1 (fun _ -> e2)
///
///   can be written instead as
///
///     e1 ;;
///     e2


/// returning a result into a computation
let return #st #a (x:a) : eff st a =
  fun (t, s) -> Some x, s, 0

/// sequential composition of `eff` computations
let bind #st #a #b
         (f:eff st a)
         (g: a -> eff st b)
  : eff st b
  = fun (t, s) ->
       match f (t, s) with
       | None, s', n ->
         // if f raises an exception, propagate it, while preserving
         // the state (s') and #slots consumed on the tape (n)
         None, s', n

       | Some v, s', n ->
         //otherwise, truncate the prefix of the tape that was already
         //used (n) and call `g` with the result of `f`, the truncated
         //tape and the state produced by `f` (s')
         g v (truncate t n, s')

/// reading the entire state
let get #st : eff st st
  = fun (t, s) -> Some s, s, 0

/// writing the entire state
let set #st (s:st) : eff st unit
  = fun (t, _) -> Some (), s, 0

/// sampling from the head of the tape
let sample #st : eff st byte
  = fun (t, s) -> Some (t 0), s, 1

/// raising an exception
let raise #st #a : eff st a
  = fun (t, s) -> None, s, 0

/// state separation
let lift_left #st1 #st2 #a (f:eff st1 a)
  : eff (st1 & st2) a
  = fun (t, (s1, s2)) ->
      match f (t, s1) with
      | None, s1', n -> None, (s1', s2), n
      | Some x, s1', n -> Some x, (s1', s2), n

let lift_right #st1 #st2 #a (f:eff st2 a)
  : eff (st1 & st2) a
  = fun (t, (s1, s2)) ->
      match f (t, s2) with
      | None, s2', n -> None, (s1, s2'), n
      | Some x, s2', n -> Some x, (s1, s2'), n

////////////////////////////////////////////////////////////////////////////////
//KEY package
////////////////////////////////////////////////////////////////////////////////

let lbytes (n:nat) = Seq.lseq byte n
let bytes = Seq.seq byte
let handle = bytes&bytes
let key (n:nat) = lbytes n
let key_state (n:nat) = (Map.t handle bool & Map.t handle (key n))

let key_gen (h:handle) : eff (key_state 1) handle =
    s <-- get ;
    let (h_map,k_map) = s in
    match Map.contains h_map h,Map.contains k_map h with
    | false,false ->
      k <-- sample ;
      let s':key_state 1 = (Map.upd h_map h true, Map.upd k_map h (Seq.create 1 k <: Seq.lseq byte 1)) in
      //set s' ;
      return h
    | _,_ ->
      raise

let key_set (h:handle) (k_in:Seq.lseq byte 1) : eff (key_state 1) handle =
    s <-- get ;
    let (h_map,k_map) = s in
    match Map.contains h_map h,Map.contains k_map h with
    | false,false ->
      let s':key_state 1 = (Map.upd h_map h true, Map.upd k_map h k_in) in
      //set s' ;
      return h
    | _,_ ->
      raise

let key_cset (h:handle) (k_in:Seq.lseq byte 1) : eff (key_state 1) handle =
    s <-- get ;
    let (h_map,k_map) = s in
    match Map.contains h_map h,Map.contains k_map h with
    | false,false ->
      let s':key_state 1 = (Map.upd h_map h false, Map.upd k_map h k_in) in
      //set s' ;
      return h
    | _,_ ->
      raise

let key_get (h:handle) : eff (key_state 1) (key 1) =
    s <-- get ;
    let (h_map,k_map) = s in
    match Map.contains h_map h,Map.contains k_map h with
    | true,true ->
      let k = Map.sel k_map h in
      return k
    | _,_ ->
      raise

let key_hon (h:handle) : eff (key_state 1) bool =
    s <-- get ;
    let (h_map,k_map) = s in
    match Map.contains h_map h,Map.contains k_map h with
    | true,true ->
      let honest = Map.sel h_map h in
      return honest
    | _,_ ->
      raise

////////////////////////////////////////////////////////////////////////////////
//AE package
////////////////////////////////////////////////////////////////////////////////
noeq type ae_scheme (n:nat) =
  | AES:
  enc: (p:bytes -> k:key n -> nonce:bytes -> c:bytes) ->
  dec: (c:bytes -> k:key n -> nonce:bytes -> option (p:bytes)) ->
  ae_scheme n

/// Map from nonces to a maps from ciphertext to plaintexts
let ae_state #n (aes:ae_scheme n) =
  Map.t bytes (Map.t bytes bytes)

let ae_key_state #n aes = ae_state #n aes & key_state n

let enc_0 (#n:nat) (aes:ae_scheme n) (plain:bytes) (nonce:bytes) (h:handle) : (eff (ae_key_state aes) bytes) =
  state <-- get ;
  let ae_st = fst state in
  let key_st = snd state in
  match Map.contains ae_st nonce with
  | true ->
    raise
  | false ->
    k <-- get key_st h;
    let c = aes.enc plain k nonce in
    return c

let enc_1 (#n:nat) (aes:ae_scheme n) (plain:bytes) (nonce:bytes) : (eff (ae_key_state aes) bytes) =
  state <-- get ;
  let ae_st = fst state in
  let key_st = snd state in
  match Map.contains ae_st nonce with
  | true ->
    raise
  | false ->
    let c = Map.upd ae_st nonce (Map.sel ae_st plain) in
    return c

// ////////////////////////////////////////////////////////////////////////////////
// //ODH package
// ////////////////////////////////////////////////////////////////////////////////

// let share (n:nat) = lbytes n
// let exponent (n:nat) = lbytes n
// assume val exponentiate : #n:nat -> x:share n -> y:exponent n -> share
// let odh

// let odh_0  : (eff (ae_key_state aes) bytes) =
//   state <-- get ;
//   let ae_st = fst state in
//   let key_st = snd state in
//   match Map.contains ae_st nonce with
//   | true ->
//     raise
//   | false ->
//     let c = Map.upd ae_st nonce (Map.sel ae_st plain) in
//     return c
