(*
   Copyright 2008-2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module LowStar.Lens.Buffer
open LowStar.Lens
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.Integers

let mk #a #p #q (b:B.mbuffer a p q) (f:flavor b) (snap:HS.mem{B.live snap b})
  : Tot (l:buffer_lens b f{(lens_of l).snapshot == snap})
  = let blens : buffer_hs_lens b f =
        FStar.Classical.forall_intro_2 (B.g_upd_seq_as_seq b);
        let invariant (x:B.mbuffer a p q) (h:HS.mem) =
          B.live h x
        in
        let fp = Ghost.hide (B.loc_buffer b) in
        let get : get_t (imem (invariant b)) (view_type_of f) =
          fun h -> 
            match f with
            | Buffer -> B.as_seq h b
            | Pointer -> B.get h b 0
        in
        let put : put_t (imem (invariant b)) (view_type_of f) =
          fun v h ->
            match f with
            | Buffer -> B.g_upd_seq b v h
            | Pointer -> B.g_upd b 0 v h
        in
        let l : imem_lens (invariant b) (view_type_of f) fp = {
          get = get;
          put = put;
          lens_laws = ()
        }
        in
        {
          footprint = fp;
          invariant = invariant;
          x = b;
          snapshot = snap;
          l = l
        }
    in
    let reader : with_state blens (reader_t f id_lens) =
      fun s i ->
        reveal_inv();
        B.index b i
    in
    let writer : with_state blens (writer_t f id_lens) =
      fun s i v ->
        reveal_inv();
        B.upd b i v
    in
    Mk blens reader writer

let elim_inv #a #p #q 
             (#b:B.mbuffer a p q)
             (#f:flavor b)
             (bl:buffer_lens b f)
  : Lemma (reveal_inv();
          (forall (h:HS.mem).{:pattern (lens_of bl).invariant (lens_of bl).x h}
           let l = lens_of bl in
           (exists h'.{:pattern mk b f h'} B.live h' b /\ bl == mk b f h') /\
             (lens_of bl).invariant (lens_of bl).x h ==>
             B.live h b /\
             view (snap l h) h == 
               (match f with
                | Pointer -> B.get h b 0
                | Buffer -> B.as_seq h b)))
  = reveal_inv ()
