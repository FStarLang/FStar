(*
   Copyright 2020 Microsoft Research

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

module Steel.Channel.FramingDuplex
module S = Steel.Channel.FramingSimplex
module Atomic = Steel.FramingEffect.Atomic

let change_slprop (p q:slprop)
                  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelT unit p (fun _ -> q)
  = Atomic.change_slprop p q proof

noeq
type chan_t (p:prot) = {
  send : S.chan p;
  recv : S.chan (dual p);
}

noeq
type chan (p:prot) = {
  chan_chan : chan_t p
}


let endpoint (#p:prot) (c:chan p) (next_action:prot) =
  S.sender c.chan_chan.send next_action `star`
  S.receiver c.chan_chan.recv (dual next_action)

#reset-options "--debug_level Rel  --print_universes"

let new_chan p =
  let c1 = S.new_chan p in
  let c2 = S.new_chan (dual p) in
  let c:chan p = { chan_chan = { send = c1; recv = c2 }} in
  change_slprop
    (S.sender c2 (dual p) `star` S.receiver c1 p)
    (endpoint c (dual p)) (fun _ -> admit());
  change_slprop
    (S.sender c1 p `star` S.receiver c2 (dual p))
    (endpoint c p) (fun _ -> admit());
  c


let send #p c #next x =
  S.send c.chan_chan.send x;
  S.recv c.chan_chan.recv x
