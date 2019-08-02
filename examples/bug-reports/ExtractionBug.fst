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
module ExtractionBug
open FStar.HyperHeap
type gid = int

type rw = 
  | Reader
  | Writer

type state (i:gid) (rw:rw) = 
  | State :
      region:rid
    -> peer_region:rid
    -> log:  rref (if rw=Reader then peer_region else region) int
    -> state i rw


let f (#i:gid) (#r:rw) (s:state i r) = !(State.log s)

let g (#i:gid) (#r:rw) (s:state i r) =
  let (State reg peer l) = s in
  !l
