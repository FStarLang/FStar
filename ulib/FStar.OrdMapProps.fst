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
module FStar.OrdMapProps
 
open FStar.OrdMap

val fold: #k:eqtype -> #v:Type -> #a:Type -> #f:cmp k -> (k -> v -> a -> Tot a)
          -> m:ordmap k v f -> a -> Tot a (decreases (size m))
let rec fold #k #v #t #f g m a =
  if size m = 0 then a
  else
    let Some (k, v) = choose m in
    fold g (remove k m) (g k v a)
