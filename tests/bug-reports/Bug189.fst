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
module Bug189

type heap = unit -> Tot unit

type pred = heap -> Tot unit

type deduce : unit -> Type =
| Blah : deduce ()

val feq : #a:Type -> a -> Tot unit
let feq x = ()

type hoare_c (q:pred) = (h':heap -> deduce (q h'))

val skip_spec : u:unit -> Tot (hoare_c feq)
let skip_spec u = fun h1 -> magic()
