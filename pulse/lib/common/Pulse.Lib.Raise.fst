(*
   Copyright 2025 Microsoft Research

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
module Pulse.Lib.Raise

noeq type raisable = {
  f: ([@@@strictly_positive] Type u#a -> Type u#b);
  raise_val: (#t: Type u#a -> x: t -> f t);
  downgrade_val: (#t: Type u#a -> x: f t -> t);
  down_raise: (#t: Type u#a -> x: t -> squash (downgrade_val (raise_val x) == x));
  raise_down: (#t: Type u#a -> x: f t -> squash (raise_val (downgrade_val x) == x));
}

let raisable_inst = {
  f = Universe.raise_t;
  raise_val = Universe.raise_val;
  downgrade_val = Universe.downgrade_val;
  down_raise = Universe.downgrade_val_raise_val;
  raise_down = Universe.raise_val_downgrade_val;
}

let raise_t #inst t = inst.f t
let raise_val #t #inst x = inst.raise_val x
let downgrade_val #t #inst x = inst.downgrade_val x
let downgrade_val_raise_val #_ #inst x = inst.down_raise x
let raise_val_downgrade_val #_ #inst x = inst.raise_down x
