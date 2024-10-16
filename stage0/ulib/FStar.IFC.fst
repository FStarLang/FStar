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
module FStar.IFC

let protected #sl l b = b

let reveal #sl #l #b x = x
let hide #sl #l #b x = x
let reveal_hide #l #t #b x = ()
let hide_reveal #sl #l #b x = ()

let map #a #b #sl #l x f = f x
let join #sl #l1 #l2 #a x = x
