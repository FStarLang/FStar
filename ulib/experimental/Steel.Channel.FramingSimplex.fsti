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

module Steel.Channel.FramingSimplex
open Steel.Channel.Protocol
open Steel.FramingEffect
open Steel.Memory

/// Msg int (fun x -> Msg (y:int { y > x }) (fun _ -> Ret unit))
///
/// DoWhile (Msg int (fun x -> Msg (y:int { y > x }) (fun _ -> Ret bool)))
let prot : Type u#1 = protocol unit

val chan (p:prot) : Type0

val sender (#p:prot) (c:chan p) (next_action:prot) : slprop u#1

val receiver (#p:prot) (c:chan p) (next_action:prot) : slprop u#1

val new_chan (p:prot)
  : SteelT (chan p) emp (fun c -> sender c p `star` receiver c p)

val send (#p:prot) (c:chan p) (#next:prot{more next}) (x:msg_t next)
  : SteelT unit (sender c next) (fun _ -> sender c (step next x))

val recv (#p:prot) (#next:prot{more next}) (c:chan p)
  : SteelT (msg_t next) (receiver c next) (fun x -> receiver c (step next x))

val history (#p:prot) (c:chan p) (t:partial_trace_of p) : slprop

val history_duplicable (#p:prot) (c:chan p) (t:partial_trace_of p)
  : SteelT unit (history c t) (fun _ -> history c t `star` history c t)

val trace (#q:prot) (cc:chan q)
  : SteelT (partial_trace_of q) emp (fun tr -> history cc tr)

val extend_trace (#p:prot) (#next:prot) (c:chan p) (previous:partial_trace_of p)
  : SteelT (extension_of previous)
           (receiver c next `star` history c previous)
           (fun t -> receiver c next `star` history c t `star` pure (until t == next))
