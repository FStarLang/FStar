module Setoids.Crypto
module L = Setoids
open FStar.Bytes
open FStar.UInt32
open FStar.Map
open Setoids

module DM = FStar.DependentMap

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
let tape = u32 -> Tot byte
let index = u32

let default_tape_rel = lo tape
let default_index_rel = lo index

//#set-options "--z3rlimit 150 --max_fuel 1 --max_ifuel 2 --query_stats"
#set-options "--z3rlimit 150 --query_stats"
let truncate (t:tape) (n:u32) : tape =
  fun m ->
    t (add_underspec m n)

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

let quatruple_rel (#a:Type) (#b:Type) (#c:Type) (#d:Type) (arel:rel a) (brel:rel b) (crel:rel c) (drel:rel d) (p0 p1:(a & b & c & d)) : prop =
  let (w0, x0, y0, z0) = p0 in
  let (w1, x1, y1, z1) = p1 in
  w0 `arel` w1 /\
  x0 `brel` x1 /\
  y0 `crel` y1 /\
  z0 `drel` z1

let eff' (#s:Type) (#a:Type) (srel:rel s) (arel:rel a) (trel:rel tape) (irel:rel index) =
  (trel ** srel) ^--> (triple_rel (option_rel arel) srel irel)

#set-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 2"
let eff'_rel #s #a
    (srel: erel s)
    (arel: erel a)
    (trel: erel tape)
    (irel: erel index)
    : erel (eff' srel arel trel irel)
  = arrow_rel (trel ** srel) (triple_rel (option_rel #a arel) srel irel)

let eff #s #a srel arel = eff' #s #a srel arel default_tape_rel default_index_rel

let eff_rel #s #a
    (srel: erel s)
    (arel: erel a)
    : erel (eff' srel arel default_tape_rel default_index_rel)
  = eff'_rel #s #a srel arel default_tape_rel default_index_rel

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
  = fun ((t:tape), (s0:s)) -> Some x, s0, 0ul

/// sequential composition of `eff` computations
#set-options "--z3rlimit 150 --max_fuel 1 --max_ifuel 2"
let bind #s #a (#srel:erel s) (#arel:erel a) #b (#brel:erel b)
         ($f:eff #s #a srel arel)
         (g:arel ^--> eff_rel #s #b srel brel)
   : eff #s #b srel brel =
   fun (t, s0) ->
     match f (t, s0) with
     | Some x, s1, n ->
       g x (truncate t n, s1)
     | None, s1, n ->
       None, s1, n

#set-options "--z3rlimit 150 --max_fuel 1 --max_ifuel 2 --query_stats"
/// reading the entire state
let get #s (#srel:erel s) : eff srel srel =
  fun (t, s0) -> Some s0, s0, 0ul

/// writing the entire state
let put #s (#srel:erel s) : (srel ^--> eff_rel srel (lo unit)) =
  fun s (t,_) -> Some (), s, 0ul

/// sampling from the head of the tape
let sample #st : eff st (lo byte)
  = fun (t, s) -> Some (t 0ul), s, 1ul

private
let rec sample_inner (t:u32 -> byte) (c:u32) : Tot (lbytes32 c) (decreases (v c)) =
  match c with
  | 0ul -> empty_bytes
  | c' ->
    let b = t (sub c 1ul) in
    let rest = sample_inner t (sub c 1ul) in
    append rest (create 1ul b)

let sample_multiple #s #srel (length:u32) :eff #s srel (lo (lbytes32 length)) =
  fun (t, s) ->
  let b_string = sample_inner t length in
  Some b_string, s, length

/// raising an exception
let raise #s (#srel:erel s) #a (#arel:erel a) : eff srel arel
  = fun (t, s) -> (None, s, 0ul)

#reset-options
#set-options "--z3rlimit 350 --query_stats --max_fuel 4 --max_ifuel 5"
let lift_left (#s1:Type) (#s1rel:erel s1{lo s1 == s1rel}) #s2 (#s2rel:erel s2) #a (#arel:erel a) (f:eff s1rel arel)
  : ((default_tape_rel ** (s1rel ** s2rel)) ^--> (triple_rel (option_rel arel) (s1rel ** s2rel) (lo index)))
  = fun (t, (s1, s2)) ->
      match f (t ,s1) with
      | None, s1', n ->
        None, (s1', s2), n

      | Some x, s1', n ->
        Some x, (s1', s2), n

let lift_right #s1 (#s1rel:erel s1) #s2 (#s2rel:erel s2{s2rel == lo s2}) #a (#arel:erel a) (f:eff s2rel arel)
  : eff (s1rel ** s2rel) arel
  = fun (t, (s1, s2)) ->
      match f (t, s2) with
      | None, s2', t -> None, (s1, s2'), t
      | Some x, s2', t -> Some x, (s1, s2'), t

let get_oracle #sig (m:module_t sig) (o:sig.labels) : sig.ops o = DM.sel m o

/// Problems until now:
/// - can't prove lift_left and lift_right without requiring one of the state
///   relations to be 'lo'.
/// - can't prove that ae0_functor is actually a functor. I suspect this is
///   somehow because the 'lo' effect on the key module state.
/// - if two parallely composed packages have the same underlay, they should not
///   require two instance of this signature, which is what functor_prod gives you.
///   - a question on the implementation of sig_prod. What if the signatures are
///     the same? Then does the call always go to the first one?
/// state separation
