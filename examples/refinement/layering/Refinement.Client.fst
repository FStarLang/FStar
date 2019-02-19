module Refinement.Client
open Refinement
(* This client of Refinement demonstrates how
   abstract computation can be writted in the RST effect
   without any details of LowStar needed in VCs *)
#reset-options "--using_facts_from '* -FStar.HyperStack -LowStar'"

(* Here's a simple swap *)
let swap r
  : RST unit r
    (requires fun _ -> True)
    (ensures (fun (v0, v1) _ (v0', v1') ->
       v0 == v1' /\
       v1 == v0'))
  = let v0 = read_fst r in
    let v1 = read_snd r in
    set_fst r v1;
    set_snd r v0

(* Iterating many (100) times works pretty easily *)
let n_swap r
  : RST unit r
    (requires (fun _ -> True))
    (ensures (fun p0 _ p1 ->
      p0 == p1))
  = swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r; //20

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r; //40

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r; //60

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r; //80

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r;

    swap r;
    swap r //100

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 30"

(* And here's how to call into an abstract computation
   from Low* *)
module B = LowStar.Buffer
open FStar.HyperStack.ST
module HS = FStar.HyperStack
let go (p1 p2: B.pointer nat)
  : Stack unit
    (requires (fun h ->
      B.disjoint p1 p2 /\
      B.live h p1 /\
      B.live h p2))
    (ensures (fun h0 _ h1 ->
       B.get h0 p1 0 == B.get h1 p1 0 /\
       B.get h0 p2 0 == B.get h1 p2 0 /\
       B.modifies
         (B.loc_union
           (B.loc_buffer p1)
           (B.loc_buffer p2))
         h0 h1))
  = let h0 = get () in
    let r = mk_roots p1 p2 h0 in     //make an initial roots
    n_swap r;                        //call into RST
    let h1 = get () in
    elim r h0;                       //call the eliminators
    elim r h1

(* Meanwhile, doing n swaps directly in Low* doesn't scales poorly *)
open LowStar.BufferOps
let l_swap (p1 p2:B.pointer nat)
  : Stack unit
    (requires fun h ->
      B.disjoint p1 p2 /\
      B.live h p1 /\
      B.live h p2)
    (ensures (fun h0 _ h1 ->
       B.get h0 p1 0 == B.get h1 p2 0 /\
       B.get h0 p2 0 == B.get h1 p1 0 /\
       B.modifies
         (B.loc_union
           (B.loc_buffer p1)
           (B.loc_buffer p2))
         h0 h1))
  = let v1 = !* p1 in
    let v2 = !* p2 in
    p1 *= v2;
    p2 *= v1

//#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit_factor 10 --z3cliopt 'smt.qi.eager_threshold=100'"
let n_lswap (p1 p2:B.pointer nat)
  : Stack unit
    (requires (fun h ->
      B.disjoint p1 p2 /\
      B.live h p1 /\
      B.live h p2))
    (ensures (fun h0 _ h1 ->
       B.get h0 p1 0 == B.get h1 p1 0 /\
       B.get h0 p2 0 == B.get h1 p2 0 /\
       B.modifies
         (B.loc_union
           (B.loc_buffer p1)
           (B.loc_buffer p2))
         h0 h1))
  = l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2; //20

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2; //40

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2; //60

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2; //80

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2;

    l_swap p1 p2;
    l_swap p1 p2 //100
