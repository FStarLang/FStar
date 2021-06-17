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
module Steel.Primitive.ForkJoin

open Steel.Memory
open Steel.Effect

/// Building a model of fork/join concurrency as a verified library on top of the Steel framework.
/// This will ultimately be extracted to primitive implementations of fork/join and mutexes in
/// both OCaml and C.

/// The abstract type of a thread. The thread is indexed by a vprop [p], and must provide
/// this vprop when terminating
val thread (p:vprop) : Type u#0

/// Forking threads. [f] corresponds to the forked function,
/// while [g] is the continuation, which knows that the forked thread will
/// ultimately return vprop [q].
val fork (#p #q #r #s:vprop)
         (f: (unit -> SteelT unit p (fun _ -> q)))
         (g: (thread q -> unit -> SteelT unit r (fun _ -> s)))
  : SteelT unit (p `star` r) (fun _ -> s)

/// Joining a thread [t], adding the vprop [p] to the context that [t]
/// must ultimately return.
/// Blocks until [t] terminates
val join (#p:vprop) (t:thread p)
  : SteelT unit emp (fun _ -> p)
