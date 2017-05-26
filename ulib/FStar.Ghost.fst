(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

(* See FStar.Ghost.fsti *)
module FStar.Ghost
let erased a = a
let reveal #a x = x
let hide #a x = x
let hide_reveal #a x = ()
let reveal_hide #a x = ()
let elift1 #a #b f ga = f ga
let elift2 #a #b #c f ga gc = f ga gc
let elift3 #a #b #c #d f ga gc gd = f ga gc gd
let elift1_p #a #b #p f ga = f ga
let elift2_p #a #c #p #b f ga gc = f ga gc
