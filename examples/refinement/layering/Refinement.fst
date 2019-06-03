module Refinement
(* The goal of this experiment is to define a simple,
   abstract memory model on top of HyperStack.

   I just pick the state to be a pair of nats, for now.
   But, we should generalize this.
*)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
/// pre_roots:
///   A pair of pointers that will store our abstract state in the hyperstack
///   and the initial HS.mem in which our abstract computation begins
noeq
type pre_roots = {
  p1:B.pointer nat;
  p2:B.pointer nat;
  h:(h:HS.mem{ B.disjoint p1 p2 /\
               B.live h p1 /\
               B.live h p2 }  )
}

/// `roots` hides `pre_roots` from clients
abstract type roots = pre_roots

/// `inv`: An abstract invariant on roots
abstract
let inv (r:roots) (h:HS.mem) =
  B.live h r.p1 /\
  B.live h r.p2


/// `pre_h_extension`:
///    Relating a memory to the roots
///    Intuitively, a `h` is a successor memory of the initial one
let pre_h_extension (r:pre_roots) (h:HS.mem) =
  //h1 == put r h0 (get r h1) //equivalent
  inv r h /\
  HST.equal_domains r.h h /\
  B.modifies (B.loc_union (B.loc_buffer r.p1)
                          (B.loc_buffer r.p2))
             r.h
             h

/// `h_extension`: Abstracting pre_h_extension from clients
abstract
let h_extension (r:roots) (h:HS.mem) = pre_h_extension r h

/// `imem r`: A memory satisfying the invariant
let imem (r:roots) = h:HS.mem{h_extension r h}

/// `get`: viewing an memory as an abstract state (a pair)
abstract
let get (r:roots) (h:imem r) : GTot (nat * nat) =
  B.get h r.p1 0,
  B.get h r.p2 0

/// `put`: updating the memory with an abstract state
abstract
let put (r:roots) (h:imem r) (p:nat * nat) : GTot (imem r) =
  let h1 = B.g_upd r.p1 0 (fst p) h in
  B.g_upd_seq_as_seq r.p1 (Seq.upd (B.as_seq h r.p1) 0 (fst p)) h;
  let h2 = B.g_upd r.p2 0 (snd p) h1 in
  B.g_upd_seq_as_seq r.p2 (Seq.upd (B.as_seq h1 r.p2) 0 (snd p)) h1;
  h2

/// get/put are a lens ... should be easy to prove, but I'm lazy
let get_put (r:roots) (h:imem r)
  : Lemma (put r h (get r h) == h)
          [SMTPat (put r h (get r h))]
  = admit()

let put_get (r:roots) (h:imem r) (p:(nat * nat))
  : Lemma (get r (put r h p) == p)
          [SMTPat (get r (put r h p))]
  = admit()

let put_put (r:roots) (h:imem r) (p:(nat * nat))
  : Lemma (put r (put r h p) p == put r h p)
  = admit()


/// `mk_roots`: To get going, we can build a `roots`
abstract
let mk_roots (p1 p2:B.pointer nat)
             (h:HS.mem)
  : Pure roots
     (requires
       B.disjoint p1 p2 /\
       B.live h p1 /\
       B.live h p2)
     (ensures fun r ->
       h_extension r h)
  = {p1 = p1; p2 = p2; h = h}

/// `pre_roots_of_roots`: And an abstract desrtructor
abstract
let pre_roots_of_roots (r:roots)
  : Tot pre_roots
  = r

/// With a proof that mk_roots / pre_roots_of_roots are inverses
let invert_mk_roots
      (p1 p2:B.pointer nat)
      (h:HS.mem{B.disjoint p1 p2 /\
                B.live h p1 /\
                B.live h p2})
   : Lemma
      (ensures (
        let p = pre_roots_of_roots (mk_roots p1 p2 h) in
        p.p1 == p1 /\
        p.p2 == p2 /\
        p.h == h))
      [SMTPat (pre_roots_of_roots (mk_roots p1 p2 h))]
   = ()

/// `elim`: Eliminate the main abstract invariant back to HyperStack notions
let elim (r:roots) (h:imem r)
  : Lemma
    (requires
       h_extension r h)
    (ensures (
      let p = pre_roots_of_roots r in
      let p1, p2 = get r h in
      pre_h_extension p h /\
      B.get h p.p1 0 == p1 /\
      B.get h p.p2 0 == p2))
  = ()


/// The main computation type provided by this module
///   `RST a r pre post`
///    An abstract computation on pairs layered on top of HyperStack.STATE
effect RST (a:Type) (r:roots) (pre: (nat * nat) -> prop) (post: (nat * nat) -> a -> (nat * nat) -> prop) =
       STATE a
            (fun (k:a -> HS.mem -> Type)
               (h0:HS.mem) ->
               h_extension r h0 /\               //expect the initial memory to be in the invariat
               pre (get r h0) /\
               (forall x h1.
                 h_extension r h1 /\             //final memory is also in the invariant
                 post (get r h0)                //and the user-provided post on pairs
                      x
                      (get r h1) ==>
                k x h1))                        //prove the continuation under this hypothesis


/// `read_fst`: abstract accessor for the first component
let read_fst (r:roots)
  : RST nat r
    (requires fun _ -> True)
    (ensures fun s0 x s1 ->
      s0 == s1 /\
      x == fst s0)
  = B.index r.p1 0ul

/// `read_snd`: abstract accessor for the second component
let read_snd (r:roots)
  : RST nat r
    (requires fun _ -> True)
    (ensures fun s0 x s1 ->
      s0 == s1 /\
      x == snd s0)
  = B.index r.p2 0ul

/// `set_fst`: abstract mutator for the first component
let set_fst (r:roots) (v:nat)
  : RST unit r
    (requires fun _ -> True)
    (ensures fun s0 x s1 ->
      s1 == (v, snd s0))
  = B.upd r.p1 0ul v

/// `set_fst`: abstract mutator for the second component
let set_snd (r:roots) (v:nat)
  : RST unit r
    (requires fun _ -> True)
    (ensures fun s0 x s1 ->
      s1 == (fst s0, v))
  = B.upd r.p2 0ul v
