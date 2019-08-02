(*
   Copyright 2008-2018 Microsoft Research

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
module Loops

open FStar.List.Tot
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST
#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

let v (r:ref int) (res: (unit * heap)) : GTot int = sel (snd res) r

let rec sum_up (r:ref int) (from:int) (to:int{from <= to})
    : ST unit (requires (fun h -> h `contains_a_well_typed` r))
              (ensures (fun _ _ h' -> h' `contains_a_well_typed` r))
              (decreases (to - from))
    = if to <> from
      then (r := !r + from;
            sum_up r (from + 1) to)

let rec sum_up_eq (r:ref int) (from:int) (to:int{from <= to})
              (h0:heap{h0 `contains_a_well_typed` r})
              (h1:heap{h1 `contains_a_well_typed` r})
    : Lemma (requires (sel h0 r == sel h1 r))
            (ensures (v r (reify (sum_up r from to) h0) =
                      v r (reify (sum_up r from to) h1)))
            (decreases (to - from))
    = if from = to
      then ()
      else sum_up_eq r (from + 1) to (upd h0 r (sel h0 r + from)) (upd h1 r (sel h1 r + from))

(* TODO : tweak me down if possible *)
#set-options "--z3rlimit 128 --max_fuel 8 --max_ifuel 8"

let rec sum_up_commute (r:ref int)
                       (from:int)
                       (to:int{from <= to})
                       (offset:int)
                       (h:heap{h `contains_a_well_typed` r})
      : Lemma (requires True)
              (ensures (v r (reify (sum_up r from to) h)
                      + offset
                      = v r (reify (sum_up r from to) (upd h r (sel h r + offset)))))
              (decreases (to - from))
      = if from = to
        then ()
        else begin
            let h1 = upd h r (sel h r + from) in
            let h2 = upd h1 r (sel h1 r + offset) in
            let h3 = upd h1 r (sel h r + from + offset) in
            let h4 = upd h r (sel h r + offset) in
            let h5 = upd h4 r (sel h4 r + from) in
            sum_up_commute r (from + 1) to offset h1; //IH 2
            assert (v r (reify (sum_up r from to) h) + offset
                  = v r (reify (sum_up r (from + 1) to) h1) + offset); //unfolding
            assert (v r (reify (sum_up r (from + 1) to) h1) + offset
                  = v r (reify (sum_up r (from + 1) to) h2)); //IH
            assert (v r (reify (sum_up r (from + 1) to) (upd h1 r (sel h1 r + offset)))
                  = v r (reify (sum_up r (from + 1) to) h3)); //sel/upd rewrite
            sum_up_eq r (from + 1) to h3 h5;
            assert (v r (reify (sum_up r from to) h) + offset
                  = v r (reify (sum_up r from to) h4))
        end

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

let rec sum_dn (r:ref int) (from:int) (to:int{from <= to})
    : ST unit (requires (fun h -> h `contains_a_well_typed` r))
              (ensures (fun _ _ h' -> h' `contains_a_well_typed` r))
              (decreases (to - from))
    = if to <> from
      then (r := !r + (to - 1);
            sum_dn r from (to - 1))

let rec sum_dn_eq (r:ref int) (from:int) (to:int{from <= to})
                  (h0:heap{h0 `contains_a_well_typed` r})
                  (h1:heap{h1 `contains_a_well_typed` r})
    : Lemma (requires (sel h0 r == sel h1 r))
            (ensures (v r (reify (sum_dn r from to) h0) =
                      v r (reify (sum_dn r from to) h1)))
            (decreases (to - from))
    = if from = to
      then ()
      else let t = to - 1 in
           sum_dn_eq r from t (upd h0 r (sel h0 r + t))
                              (upd h1 r (sel h1 r + t))

let rec sum_dn_commute (r:ref int)
                       (from:int)
                       (to:int{from <= to})
                       (offset:int)
                       (h:heap{h `contains_a_well_typed` r})
      : Lemma (requires True)
              (ensures (v r (reify (sum_dn r from to) h)
                      + offset
                      = v r (reify (sum_dn r from to) (upd h r (sel h r + offset)))))
              (decreases (to - from))
      = if from = to
        then ()
        else begin
            let t = to - 1 in
            let h1 = upd h r (sel h r + t) in
            let h2 = upd h1 r (sel h1 r + offset) in
            let h3 = upd h1 r (sel h r + t + offset) in
            let h4 = upd h r (sel h r + offset) in
            let h5 = upd h4 r (sel h4 r + t) in
            sum_dn_commute r from (to - 1) offset h1; //IH 2
            assert (v r (reify (sum_dn r from to) h) + offset
                  = v r (reify (sum_dn r from t) h1) + offset); //unfolding
            assert (v r (reify (sum_dn r from t) h1) + offset
                  = v r (reify (sum_dn r from t) h2)); //IH
            assert (v r (reify (sum_dn r from t) (upd h1 r (sel h1 r + offset)))
                  = v r (reify (sum_dn r from t) h3)); //sel/upd rewrite
            sum_dn_eq r from t h3 h5;
            assert (v r (reify (sum_dn r from to) h) + offset
                  = v r (reify (sum_dn r from to) h4))
        end


val sum_up_dn_aux (r:ref int)
                      (lo:int)
                      (mid:int{lo <= mid})
                      (to:int{mid <= to})
                      (h:heap{h `contains_a_well_typed` r})
   : Lemma (requires True)
           (ensures
               ( v r (reify (sum_up r lo to) h) =
                 v r (reify (sum_up r mid to) h) +
                 v r (reify (sum_dn r lo mid) h) -
                 sel h r))
           (decreases (mid - lo))

let rec sum_up_dn_aux r lo mid hi h =
    if lo = mid then ()
    else (sum_up_dn_aux r lo (mid - 1) hi h;
          sum_up_commute r mid hi (mid - 1) h;
          sum_dn_commute r lo (mid - 1) (mid - 1) h)

let equiv_sum_up_dn (r:ref int)
                    (from:int)
                    (to:int{from <= to})
                    (h:heap{h `contains_a_well_typed` r})
   : Lemma (v r (reify (sum_up r from to) h) =
            v r (reify (sum_dn r from to) h))
   = sum_up_dn_aux r from to to h

