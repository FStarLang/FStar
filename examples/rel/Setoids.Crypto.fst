module Setoids.Crypto
module L = Setoids
open FStar.Integers
open FStar.Map
open Setoids

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
//let eff (st:Type) (a:Type) =
//  tape & st ->  //input tape and initial state
//  Tot (option a &  //normal return (Some _) or exception (None)
//       st &        //final state
//       nat)          //amount of tape consumed

let option_rel (#a:Type) (arel:rel a) =
  fun x y ->
    match x with
    | None -> b2t (None? y)
    | Some some_x -> Some? y /\ Some?.v y == some_x

let eff (#s:Type) (#a:Type) (srel:rel s) (arel:rel a) =
  srel ^--> ((option_rel #a arel) ** srel)

//let option_arrow_rel (#a:Type) (#b:Type) (arel:rel a) (brel:rel b) (f g : (a -> b)) : prop =
//    forall x0 x1. x0 `arel` x1 ==>
//             f x0 `brel` g x1

let eff_rel #s #a
    (srel: erel s)
    (arel: erel a)
    : erel (eff srel arel)
  = arrow_rel srel ((option_rel #a arel) ** srel)

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
//let return #st #a (x:a) : eff st a =
//  fun (t, s) -> Some x, s, 0

let return #s #a (#srel:erel s) (#arel:erel a) (x:a)
  : eff srel arel
  = fun s0 -> Some x, s0

/// sequential composition of `eff` computations
//let bind #st #a #b
//         (f:eff st a)
//         (g: a -> eff st b)
//  : eff st b
//  = fun (t, s) ->
//       match f (t, s) with
//       | None, s', n ->
//         // if f raises an exception, propagate it, while preserving
//         // the state (s') and #slots consumed on the tape (n)
//         None, s', n
//
//       | Some v, s', n ->
//         //otherwise, truncate the prefix of the tape that was already
//         //used (n) and call `g` with the result of `f`, the truncated
//         //tape and the state produced by `f` (s')
//         g v (truncate t n, s')
let bind #s #a (#srel:erel s) (#arel:erel a) #b (#brel:erel b)
         ($f:eff srel arel)
         (g:arel ^--> eff_rel srel brel)
   : eff srel brel =
   fun s0 ->
     let x, s1 = f s0 in
     match x with
     | Some x ->
       g x s1
     | None -> None, s1

#set-options "--max_ifuel 5"

(* Old effect *)
/// reading the entire state
//let get #st : eff st st
//  = fun (t, s) -> Some s, s, 0


(* Here, F* runs out of steam *)
//let get #s (#srel:erel s) : eff srel srel =
//  fun s0 -> (Some s0), s0

(* Old effect *)
/// writing the entire state
//let set #st (s:st) : eff st unit
//  = fun (t, _) -> Some (), s, 0

let put #s (#srel:erel s) : (srel ^--> eff_rel srel (lo unit)) =
  fun s _ -> Some (), s

(* Old effect, leaving out the tape for now. *)
/// sampling from the head of the tape
//let sample #st : eff st byte
//  = fun (t, s) -> Some (t 0), s, 1


(* Old effect *)
/// raising an exception
//let raise #st #a : eff st a
//  = fun s -> (None, s)

(* Here, F* runs out of steam *)
//let raise #s (#srel:erel s) #a (#arel:erel a) : eff srel arel
//  = fun s -> (None, s)

/// state separation
let lift_left #s1 (#s1rel:erel s1) #s2 (#s2rel:erel s2) #a (#arel:erel a) (f:eff s1rel arel)
  : eff (s1rel ** s2rel) arel
  = fun (s1, s2) ->
      match f s1 with
      | None, s1' -> None, (s1', s2)
      | Some x, s1' -> Some x, (s1', s2)

let lift_right #s1 (#s1rel:erel s1) #s2 (#s2rel:erel s2) #a (#arel:erel a) (f:eff s2rel arel)
  : eff (s1rel ** s2rel) arel
  = fun (s1, s2) ->
      match f s2 with
      | None, s2' -> None, (s1, s2')
      | Some x, s2' -> Some x, (s1, s2')

////////////////////////////////////////////////////////////////////////////////
//KEY package
////////////////////////////////////////////////////////////////////////////////

let lbytes (n:nat) = Seq.lseq byte n
let bytes = Seq.seq byte
let handle = bytes&bytes
let key (n:nat) = lbytes n
let key_state (n:nat) = (Map.t handle bool & Map.t handle (key n))

let key_state_rel (n:nat) = hi (key_state n)

let key_eff (n:nat) = option_st (key_state_rel n)

//let key_gen (h:handle) : eff (key_state 1) handle =
//    s <-- get ;
//    let (h_map,k_map) = s in
//    match Map.contains h_map h,Map.contains k_map h with
//    | false,false ->
//      k <-- sample ;
//      let s':key_state 1 = (Map.upd h_map h true, Map.upd k_map h (Seq.create 1 k <: Seq.lseq byte 1)) in
//      set s' ;;
//      return h
//    | _,_ ->
//      raise
//
//let key_set (h:handle) (k_in:Seq.lseq byte 1) : eff (key_state 1) handle =
//    s <-- get ;
//    let (h_map,k_map) = s in
//    match Map.contains h_map h,Map.contains k_map h with
//    | false,false ->
//      let s':key_state 1 = (Map.upd h_map h true, Map.upd k_map h k_in) in
//      set s' ;;
//      return h
//    | _,_ ->
//      raise
//
//let key_cset (h:handle) (k_in:Seq.lseq byte 1) : eff (key_state 1) handle =
//    s <-- get ;
//    let (h_map,k_map) = s in
//    match Map.contains h_map h,Map.contains k_map h with
//    | false,false ->
//      let s':key_state 1 = (Map.upd h_map h false, Map.upd k_map h k_in) in
//      set s' ;;
//      return h
//    | _,_ ->
//      raise
//
//let key_get_t = handle -> eff (key_state 1) (key 1)
//let key_get (h:handle) : eff (key_state 1) (key 1) =
//    s <-- get ;
//    let (h_map,k_map) = s in
//    match Map.contains h_map h,Map.contains k_map h with
//    | true,true ->
//      let k = Map.sel k_map h in
//      return k
//    | _,_ ->
//      raise

let key_hon_t = lo handle ^--> (key_state_rel 1) (lo bool) //eeff (hi (key_state 1)) (lo bool)
let key_hon : key_hon_t =
    s <-- get ;
    let (h_map,k_map) = s in
    match Map.contains h_map h,Map.contains k_map h with
    | true,true ->
      let honest = Map.sel h_map h in
      return honest
    | _,_ ->
      raise

type key_labels =
    //| GET
    | HON

let key_field_types: key_labels -> Type =
    function  //GET -> key_get_t
            | HON -> key_hon_t



/// A couple of `st` types
let t_one = lo int ^--> st_rel state_rel (lo int)
let t_two = lo int ^--> st_rel state_rel (lo bool)

let field_rels : (k:key -> erel (field_types k)) =
  function
    | ONE -> arrow (lo int) (st_rel state_rel (lo int))
    | TWO -> arrow (lo int) (st_rel state_rel (lo bool))

#set-options "--z3rlimit 100"
let field_rels : (k:key_labels -> erel (key_field_types k)) =
  function
    //| GET -> arrow (lo handle) (st_rel state_rel (lo key))
    | HON -> arrow (lo handle) (eff (key_state 1) (lo bool))

//let key_module

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
