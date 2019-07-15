module Setoids.Crypto
module L = Setoids
open FStar.Bytes
open FStar.Map
open Setoids

module DMap = FStar.DependentMap

//let byte = uint_8

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

let default_tape_rel = lo tape

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
  fun (x:option a) (y:option a) ->
    match x,y with
    | None,None -> True // <: prop
    | Some some_x, Some some_y -> (arel some_y some_x) // <: prop
    | _, _ -> False // <: prop

let triple_rel (#a:Type) (#b:Type) (#c:Type) (arel:rel a) (brel:rel b) (crel:rel c) (p0 p1:(a & b & c)) : prop =
  let (x0, y0, z0) = p0 in
  let (x1, y1, z1) = p1 in
  x0 `arel` x1 /\
  y0 `brel` y1 /\
  z0 `crel` z1

let eff' (#s:Type) (#a:Type) (srel:rel s) (arel:rel a) (trel:rel tape)=
  (trel ** srel) ^--> (triple_rel (option_rel arel) srel trel)

#set-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 2"
let eff'_rel #s #a
    (srel: erel s)
    (arel: erel a)
    (trel: erel tape)
    : erel (eff' srel arel trel)
  = arrow_rel (trel ** srel) (triple_rel (option_rel #a arel) srel trel)

let eff #s #a srel arel = eff' #s #a srel arel default_tape_rel

let eff_rel #s #a
    (srel: erel s)
    (arel: erel a)
    : erel (eff' srel arel default_tape_rel)
  = eff'_rel #s #a srel arel default_tape_rel

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
let return (#s:Type) (#a:Type) (#srel:erel s) (#arel:erel a) (x:a)
  : eff #s #a srel arel
  = fun ((t:tape), (s0:s)) -> Some x, s0, t

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
//#set-options "--z3rlimit 350 --max_fuel 1 --max_ifuel 3"
#set-options "--z3rlimit 150 --max_fuel 1 --max_ifuel 2"
let bind #s #a (#srel:erel s) (#arel:erel a) #b (#brel:erel b)
         ($f:eff #s #a srel arel)
         (g:arel ^--> eff_rel #s #b srel brel)
   : eff #s #b srel brel =
   fun (t, s0) ->
     let x, s1, t = f (t, s0) in
     match x with
     | Some x ->
       g x (t,s1)
     | None -> None, s1, t

/// reading the entire state
let get #s (#srel:erel s) : eff srel srel =
  fun (t, s0) -> Some s0, s0 ,t

/// writing the entire state
let put #s (#srel:erel s) : (srel ^--> eff_rel srel (lo unit)) =
  fun s (t,_) -> Some (), s, t

(* Old effect, leaving out the tape for now. *)
/// sampling from the head of the tape
//let sample #st : eff st byte
//  = fun (t, s) -> Some (t 0), s, 1


(* Old effect *)
/// raising an exception
let raise #s (#srel:erel s) #a (#arel:erel a) : eff srel arel
  = fun (t, s) -> (None, s, t)

#set-options "--z3rlimit 350 --max_fuel 3 --max_ifuel 4"
/// state separation
let lift_left #s1 (#s1rel:erel s1) #s2 (#s2rel:erel s2) #a (#arel:erel a) (f:(default_tape_rel ** s1rel) ^--> (triple_rel (option_rel arel) s1rel default_tape_rel))
  : ((default_tape_rel ** (s1rel **s2rel)) ^--> (triple_rel (option_rel arel) (s1rel ** s2rel) default_tape_rel))
  = fun (t, (s1, s2)) ->
      match f (t, s1) with
      | None, s1', t ->
        None, (s1', s2), t

      | Some x, s1', t ->
        Some x, (s1', s2), t

let lift_right #s1 (#s1rel:erel s1) #s2 (#s2rel:erel s2) #a (#arel:erel a) (f:eff s2rel arel)
  : eff (s1rel ** s2rel) arel
  = fun (t, (s1, s2)) ->
      match f (t, s2) with
      | None, s2', t -> None, (s1, s2'), t
      | Some x, s2', t -> Some x, (s1, s2'), t

module DM = FStar.DependentMap

////////////////////////////////////////////////////////////////////////////////
//KEY package
////////////////////////////////////////////////////////////////////////////////

let lbytes (n:nat) = Seq.lseq byte n
let bytes = Seq.seq byte
let handle = bytes&bytes
let key (n:nat) = lbytes n
let key_state (n:nat) = (Map.t handle (option bool) & Map.t handle (option (key n)))

let key_state_rel (n:nat) = lo (key_state n)

let key_eff (n:nat) = eff (key_state_rel n)

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

let key_set_t (n:nat) = (lo handle) ** (lo (Seq.lseq byte n)) ^--> eff_rel (key_state_rel n) (lo handle)
let key_set n : key_set_t n =
    fun (h, k_in) ->
    s <-- get ;
    let (h_map,k_map) = s in
    match Map.sel h_map h,Map.sel k_map h with
    | None,None ->
      let s':key_state n = (Map.upd h_map h (Some true), Map.upd k_map h (Some k_in)) in
      put s' ;;
      return h
    | _,_ ->
      raise

let key_cset_t (n:nat) = (lo handle) ** (lo (Seq.lseq byte n)) ^--> eff_rel (key_state_rel n) (lo handle)
let key_cset n : key_cset_t n =
    fun (h, k_in) ->
    s <-- get ;
    let (h_map,k_map) = s in
    match Map.sel h_map h,Map.sel k_map h with
    | None, None ->
      let s':key_state n = (Map.upd h_map h (Some false), Map.upd k_map h (Some k_in)) in
      put s' ;;
      return h
    | _,_ ->
      raise

let key_get_t (n:nat) = (lo handle) ^--> eff_rel (key_state_rel n) (lo (key n))
let key_get n : key_get_t n =
    fun h ->
    s <-- get ;
    let (h_map,k_map) = s in
    match Map.sel h_map h,Map.sel k_map h with
    | Some hon, Some k ->
      return k
    | _,_ ->
      raise

let transform n (h:handle) = key_get n h


let key_hon_t (n:nat) = (lo handle) ^--> eff_rel (key_state_rel n) (lo bool)
let key_hon n : key_hon_t n =
    fun h ->
    s <-- get ;
    let (h_map,k_map) = s in
    match Map.sel h_map h,Map.sel k_map h with
    | Some hon, Some k ->
      return hon
    | _,_ ->
      raise

type key_labels =
    | GET
    | HON
    | SET
    | CSET

let key_field_types n : key_labels -> Type =
    function  GET -> key_get_t n
            | HON -> key_hon_t n
            | SET -> key_set_t n
            | CSET -> key_cset_t n

let key_field_rels n : (k:key_labels -> erel (key_field_types n k)) =
  function
      GET -> arrow (lo handle) (eff_rel (key_state_rel n) (lo (key n)))
    | HON -> arrow (lo handle) (eff_rel (key_state_rel n) (lo bool))
    | SET -> arrow (lo handle**lo (lbytes n)) (eff_rel (key_state_rel n) (lo handle))
    | CSET -> arrow (lo handle**lo (lbytes n)) (eff_rel (key_state_rel n) (lo handle))

let sig_key (n:nat) = {
  labels = key_labels;
  ops = key_field_types n;
  rels = key_field_rels n
  }

let key_module (n:nat) : module_t (sig_key n) =
  DM.create #_ #(sig_key n).ops
    (function GET -> key_get n
            | HON -> key_hon n
            | SET -> key_set n
            | CSET -> key_cset n)

let key_functor n = as_fun (key_module n)

////////////////////////////////////////////////////////////////////////////////
//AE package
////////////////////////////////////////////////////////////////////////////////
noeq type ae_scheme (n:nat) =
  | AES:
  max_plaintext_length: u32 ->
  ciphertext_length: (plaintext_length:u32{plaintext_length `lte` max_plaintext_length} -> u32) ->
  enc: (p:bytes -> k:key n -> nonce:bytes -> c:bytes) ->
  dec: (c:bytes -> k:key n -> nonce:bytes -> option (p:bytes)) ->
  ae_scheme n

/// Map from nonces to a maps from ciphertext to plaintexts
let ae_log #n (aes:ae_scheme n) =
  DM.t bytes (fun n -> option (DM.t bytes (fun i -> option bytes)))

let ae_log_rel (#n:nat) (aes:ae_scheme n) = lo (ae_log aes)

/// Is there a nicer way to have a function with mulitple inputs than using nested tuples?
/// How to use the 'secure information flow' relations again with AE^0 vs AE^1?
/// AE^0 also depends on the state of the key package.
/// Is there a way to improve verification performance and/or error messages?
/// Every AE function takes as additional parameter the module it is composed with.
/// AE Functor: Function from underlay module to AE signature

let enc_inputs (#a:Type) (#b:Type) (#c:Type) (arel:rel a) (brel:rel b) (crel: rel c) (p0 p1:(a & b & c)) : prop =
  let (w0, x0, y0) = p0 in
  let (w1, x1, y1) = p1 in
  w0 `arel` w1 /\
  x0 `brel` x1 /\
  y0 `crel` y1 ///\
  //z0 `drel` z1

#set-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 3"
/// This would be a nice, generic approach, but it's probably a little to complex
//let multi_rel' (tl:list Type) (rm:DMap.t (n:nat{n < List.Tot.length tl}) (fun i -> rel (List.Tot.index tl i))) (vm0 vm1:DMap.t (n:nat{n < List.Tot.length tl}) (fun i -> List.Tot.index tl i)) =
//  let logical_and t1 t2 = t1 /\ t2
//  let iterate_maps (i:nat{i < List.Tot.length tl}) =
//    let x0 = DMap.sel vm0 i in
//    let x1 = DMap.sel vm1 i in
//    let rel = DMap.sel rm i in
//    x0 `rel` x1
//  in
//  //let indices = mapi #Type (fun i _ -> i) tl in
//  let prop_list = List.Tot.mapi #Type (fun i _ -> iterate_maps i) tl in
//  admit()

/// TODO: Find a way to improve this such that it can take more arguments and call the function directly.
let get_oracle #sig (m:module_t sig) (o:sig.labels) : sig.ops o = DM.sel m o

#set-options "--z3rlimit 350 --max_fuel 2 --max_ifuel 3"
let enc_0_t (n:nat) (aes:ae_scheme n) = enc_inputs (lo bytes) (lo bytes) (lo handle) ^--> eff_rel (ae_log_rel #n aes ** lo (key_state n)) (lo bytes)
let enc_1_t (n:nat) (aes:ae_scheme n) = enc_inputs (lo bytes) (lo bytes) (lo handle) ^--> eff_rel (ae_log_rel #n aes ** hi (key_state n)) (lo bytes)

let enc_0 (n:nat) (aes:ae_scheme n) (key_module:module_t (sig_key n)) : (enc_0_t n aes) = // (#n:nat) (key_module:module_t (sig_key n)) (aes:ae_scheme n) (inputs:enc_inputs (lo bytes) (lo bytes) (lo handle)) : (eff (lo (ae_state #n aes)) (lo bytes)) =
  fun ((p:bytes),(nonce:bytes),(h:handle)) ->
  ae_st <-- get ;
  let ae_st,k_st = ae_st in
  match DM.sel ae_st nonce with
  | Some option_map ->
    raise
  | None ->
    let k_get : key_get_t n = get_oracle key_module GET in
    k <-- lift_right #(ae_log #n aes) #(ae_log_rel #n aes) #(key_state n) #(key_state_rel n) #(key n) #(lo (key n)) (k_get h);
    let c = aes.enc p k nonce in
    return c

let enc_1 (n:nat) (aes:ae_scheme n) (key_module:module_t (sig_key n)) : (enc_0_t n aes) = // (#n:nat) (key_module:module_t (sig_key n)) (aes:ae_scheme n) (inputs:enc_inputs (lo bytes) (lo bytes) (lo handle)) : (eff (lo (ae_state #n aes)) (lo bytes)) =
  fun ((p:bytes),(nonce:bytes),(h:handle)) ->
  ae_st <-- get ;
  let ae_st,k_st = ae_st in
  match DM.sel ae_st nonce with
  | Some option_map ->
    raise
  | None ->
    let k_get : key_get_t n = get_oracle key_module GET in
    k <-- lift_right #(ae_log #n aes) #(ae_log_rel #n aes) #(key_state n) #(key_state_rel n) #(key n) #(lo (key n)) (k_get h);
    let c = aes.enc p k nonce in
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
