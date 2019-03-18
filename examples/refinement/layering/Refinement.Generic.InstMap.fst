module Refinement.Generic.InstMap
open Refinement.Generic

module DM = FStar.DependentMap
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

//// A view of an HS.mem and a root set as a dependent map. 
//// Abapted from  InstPair.fst view.

noeq
type pre_roots = {
  p1:B.pointer nat;
  p2:B.pointer bool;
  h:(h:HS.mem{ B.disjoint p1 p2 /\
               B.live h p1 /\
               B.live h p2 }  )
}

abstract let roots = pre_roots

let pre_inv (h:HS.mem) (r:pre_roots) : prop =
    B.live h r.p1 /\
    B.live h r.p2 /\
    HST.equal_domains r.h h /\
    B.modifies (B.loc_union (B.loc_buffer r.p1)
                            (B.loc_buffer r.p2))
               r.h
               h

abstract
let inv : inv_t roots = pre_inv

type mapt = DM.t (i:nat{i < 2}) (function 0 -> nat | 1 -> bool)

/// `get`: viewing an memory as an abstract state (a pair)
abstract
let get (r:roots) (h:imem inv r) : GTot mapt =
  // Getting the values before constructing the map feels wrong, but trying to 
  // 
  // Any way around this? Thunking the i's also doesn't seem to work
  let i1 =  B.get h r.p1 0 in
  let i2 = B.get h r.p2 0 in
  DM.create #(i:nat{i < 2}) #(function 0 -> nat | 1 -> bool) (function 0 -> i1 | 1 -> i2)

/// `put`: updating the memory with an abstract state
abstract
let put (r:roots) (h:imem inv r) (m: mapt) : GTot (imem inv r) =
  let i1 = DM.sel m 0 in 
  let i2 = DM.sel m 1 in     
  let h1 = B.g_upd r.p1 0 i1 h in
  B.g_upd_seq_as_seq r.p1 (Seq.upd (B.as_seq h r.p1) 0 i1) h;
  let h2 = B.g_upd r.p2 0 i2 h1 in
  B.g_upd_seq_as_seq r.p2 (Seq.upd (B.as_seq h1 r.p2) 0 i2) h1;
  h2

abstract
let pl : pre_lens inv mapt = {
  get = get;
  put = put
}

(* First lens law, almost *)
let get_put_mapt (r:roots) (h:imem inv r) : Lemma (pl.put r h (pl.get r h) == h) =
  let i1 =  B.get h r.p1 0 in
  let i2 = B.get h r.p2 0 in
  DM.sel_create #(i:nat{i < 2}) #(function 0 -> nat | 1 -> bool) (function 0 -> i1 | 1 -> i2) 0; 
  DM.sel_create #(i:nat{i < 2}) #(function 0 -> nat | 1 -> bool) (function 0 -> i1 | 1 -> i2) 1;

  let m = DM.create #(i:nat{i < 2}) #(function 0 -> nat | 1 -> bool) (function 0 -> i1 | 1 -> i2) in
  assert (DM.sel m 0 = i1);
  assert (DM.sel m 1 = i2);
  let h1 = B.g_upd r.p1 0 i1 h in
  assume (Seq.upd (B.as_seq h r.p1) 0 i1 = B.as_seq h r.p1);
  B.lemma_g_upd_with_same_seq r.p1 h;
  assert (h1 == h);
  let h2 = B.g_upd r.p2 0 i2 h in
  assume (Seq.upd (B.as_seq h r.p2) 0 i2 = B.as_seq h r.p2);
  B.lemma_g_upd_with_same_seq r.p2 h;
  assert (h2 == h);
  ()

 
let _ : squash (get_put pl /\
                put_get pl /\
                put_put pl) =
 assume (get_put pl /\
         put_get pl /\
         put_put pl) //admitting for now

abstract
let l :  lens inv mapt = pl

/// `read_fst`: abstract accessor for the first component
let read_fst (r:rlens l)
  : RST nat r
    (requires fun _ -> True)
    (ensures fun s0 x s1 ->
      s0 == s1 /\
      x == DM.sel s0 0)
  = l_get_l_put_lens l;
    B.index r.p1 0ul

/// `read_snd`: abstract accessor for the second component
let read_snd (r:rlens l)
  : RST bool r
    (requires fun _ -> True)
    (ensures fun s0 x s1 ->
      s0 == s1 /\
      x == DM.sel s0 1)
  = l_get_l_put_lens l;
    B.index r.p2 0ul

/// `set_fst`: abstract mutator for the first component
let set_fst (r:rlens l) (v:nat)
  : RST unit r
    (requires fun _ -> True)
    (ensures fun s0 x s1 ->
      DM.sel s1 0 = v /\ DM.sel s1 1 == DM.sel s0 1)
  = l_get_l_put_lens l;
    B.upd r.p1 0ul v

/// `set_fst`: abstract mutator for the second component
let set_snd (r:rlens l) (v:bool)
  : RST unit r
    (requires fun _ -> True)
    (ensures fun s0 x s1 ->
       DM.sel s1 1 = v /\ DM.sel s1 0 == DM.sel s0 0)
  = l_get_l_put_lens l;
    B.upd r.p2 0ul v

abstract
let mk_roots (p1:B.pointer nat) (p2:B.pointer bool)
             (h:HS.mem)
  : Pure (rlens l)
     (requires
       B.disjoint p1 p2 /\
       B.live h p1 /\
       B.live h p2)
     (ensures fun r ->
       inv h r)
  = {p1 = p1; p2 = p2; h = h}


/// `pre_roots_of_roots`: And an abstract desrtructor
abstract
let pre_roots_of_roots (r:rlens l)
  : Tot pre_roots
  = r

/// With a proof that mk_roots / pre_roots_of_roots are inverses
let invert_mk_roots
      (p1:B.pointer nat) (p2:B.pointer bool)
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
let elim (r:rlens l) (h:imem inv r)
  : Lemma
    (ensures (
      let pr = pre_roots_of_roots r in
      pre_inv h pr /\
      (let m = l_get l r h in
       B.get h pr.p1 0 == DM.sel m 0 /\
       B.get h pr.p2 0 == DM.sel m 1)))
  = l_get_l_put_lens l


 
