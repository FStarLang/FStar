module FStar.Monotonic.DependentMap
(** A library for mutable partial, dependent maps,
    that grow monotonically,
    while subject to an invariant on the entire map *)
open FStar.HyperStack.ST
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MR = FStar.Monotonic.RRef
module DM = FStar.DependentMap

/// `map a b`: Represent the partial map as a list of pairs of points
let map a b = list (x:a & b x)

/// `repr r`: Converts the list of pairs into a DM.t
let rec repr (#a:eqtype) (#b:a -> Type) (r:map a b)
    : GTot (partial_dependent_map a b)
    = match r with
      | [] -> empty_partial_dependent_map
      | (|x, y|)::tl -> DM.upd (repr tl) x (Some y)

/// Three basic operations on map: empty, sel upd
let empty #a #b = []

let rec sel #a #b r x =
    match r with
    | [] -> None
    | (|x', y|)::tl ->
      if x = x' then Some y else sel tl x

let upd #a #b r x v = (|x, v|)::r

////////////////////////////////////////////////////////////////////////////////

/// `grows'` and `grows`: a preorder of invariant-respeting maps
///    - Needs to be introduced in 2 steps because of an F* limitation
let grows' (#a:eqtype) (#b:a -> Type) (#inv:(partial_dependent_map a b -> Type))
           (m1:imap a b inv) (m2:imap a b inv) =
    forall x.{:pattern (Some? (sel m1 x))}
           Some? (sel m1 x) ==>
              Some? (sel m2 x) /\
              Some?.v (sel m1 x) == Some?.v (sel m2 x)
let grows #a #b #inv = grows' #a #b #inv

////////////////////////////////////////////////////////////////////////////////

//The main stateful interface is minimal and straigtforward
let alloc #a #b #inv #r _ = MR.m_alloc r []

let extend #a #b #inv #r t x y =
    let open MR in
    m_recall t;
    let cur = m_read t in
    m_write t (upd cur x y);
    witness t (contains t x y)

let lookup #a #b #inv #r t x =
    let open MR in
    let m = m_read t in
    let y = sel m x in
    match y with
    | None -> y
    | Some b ->
      witness t (contains t x b);
      y
