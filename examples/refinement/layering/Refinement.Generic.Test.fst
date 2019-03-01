module Refinement.Generic.Test
module P = Refinement.Generic.PointerLens
module Tup2 = Refinement.Generic.Tuple2
open Refinement.Generic.Effect
module B = LowStar.Buffer
open Refinement.Generic.Lens

(* Here's a simple swap *)
val swap (#a:_) (ps:Tup2.ptr_pair a a)
  : RST unit (Tup2.mk_pair ps)
    (requires fun _ -> True)
    (ensures (fun (v0, v1) _ (v0', v1') ->
       v0 == v1' /\
       v1 == v0'))
#set-options "--max_fuel 0 --max_ifuel 0 --log_queries --query_stats"
let swap (#a:_) ps =
  let v1 = Tup2.get_fst ps in
  let v2 = Tup2.get_snd ps in
  Tup2.set_fst ps v2;
  Tup2.set_snd ps v1

val n_swap (#a:_) (ps:Tup2.ptr_pair a a)
  : RST unit (Tup2.mk_pair ps)
    (requires fun _ -> True)
    (ensures (fun (v0, v1) _ (v0', v1') ->
       v0 == v0' /\
       v1 == v1'))
#reset-options "--using_facts_from 'FStar.Pervasives.Native' --max_fuel 0 --max_ifuel 0"
let n_swap #a ps =
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps; //40

    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps; //80

    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps; //120

    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps; //160

    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps; //180

    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps  //200

(* Here's a more generic, but also more cumbersome swap
   not specialized to pointers *)
let swap_gen (#a #b #c: _)
             (#l1:hs_lens a c) (r1:reader_t l1) (w1:writer_t l1)
             (#l2:hs_lens b c) (r2:reader_t l2) (w2:writer_t l2{Tup2.composable l1 l2})
  : RST unit (Tup2.mk l1 l2)
    (requires fun _ -> True)
    (ensures (fun (v0, v1) _ (v0', v1') ->
       v0 == v1' /\
       v1 == v0'))
  = let v0 = Tup2.read_fst l1 l2 r1 in
    let v1 = Tup2.read_snd l1 l2 r2 in
    Tup2.write_fst l1 l2 w1 v1;
    Tup2.write_snd l1 l2 w2 v0

val n_swap_gen (#a #b #c: _)
               (#l1:hs_lens a c) (r1:reader_t l1) (w1:writer_t l1)
               (#l2:hs_lens b c) (r2:reader_t l2) (w2:writer_t l2{Tup2.composable l1 l2})
  : RST unit (Tup2.mk l1 l2)
    (requires fun _ -> True)
    (ensures (fun (v0, v1) _ (v0', v1') ->
       v0 == v0' /\
       v1 == v1'))
let n_swap_gen (#a #b #c: _) #l1 r1 w1 #l2 r2 w2 =
  swap_gen r1 w1 r2 w2;
  swap_gen r1 w1 r2 w2

#reset-options
open FStar.HyperStack.ST
let call (p1 p2: B.pointer 'a)
  : Stack unit
    (requires fun h ->
      B.disjoint p1 p2 /\
      B.live h p1 /\
      B.live h p2)
    (ensures fun h0 _ h1 ->
      B.live h1 p1 /\
      B.live h1 p2 /\
      B.modifies (B.loc_union (B.loc_buffer p1)
                              (B.loc_buffer p2))
                 h0 h1 /\
      B.get h0 p1 0 == B.get h1 p1 0 /\
      B.get h0 p2 0 == B.get h1 p2 0
  )
  = let h0 = get () in
    let lp1 = P.mk p1 h0 in
    let lp2 = P.mk p2 h0 in
    reveal_mods();
    Tup2.tup_inv (P.lens_of_ptr lp1) (P.lens_of_ptr lp2) h0;

    n_swap (Tup2.PtrPair lp1 lp2);

    let h1 = get () in
    Tup2.tup_inv (P.lens_of_ptr lp1) (P.lens_of_ptr lp2) h1;
    P.elim_ptr_inv lp1 h0;
    P.elim_ptr_inv lp2 h0;
    P.elim_ptr_inv lp1 h1;
    P.elim_ptr_inv lp2 h1
