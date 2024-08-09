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
module SL.Actions

open SL.Heap
open SL.Effect

let lift_div_st (a:Type) (wp:pure_wp a) (p:post a) (m:memory) = wp (fun a -> p a m)
sub_effect DIV ~> STATE = lift_div_st


let read_wp (#a:Type) (r:ref a) : st_wp a =
    (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post x m0)

assume val ( ! ) (#a:Type) (r:ref a) : ST a (read_wp r) [ii r]


let write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
  (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post () (r |> v))

assume val ( := ) (#a:Type) (r:ref a) (v:a) :ST unit (write_wp r v) [ii r]


let alloc_wp (#a:Type) (v:a) : st_wp (ref a) =
  (fun post m0 -> forall (r:ref a). m0 == emp  /\ post r (r |> v))

assume val alloc (#a:Type) (v:a) : ST (ref a) (alloc_wp v) []


let free_wp (#a:Type) (r:ref a) : st_wp unit =
  (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post () emp)

assume val free (#a:Type) (r:ref a) : ST unit (free_wp r) [ii r]
