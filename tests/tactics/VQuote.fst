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
module VQuote

let var = 2
type myrec = { a:int ; b:bool }

let _ = assert (`%var     == "VQuote.var")
let _ = assert (`%Some?.v == "FStar.Pervasives.Native.__proj__Some__item__v")
let _ = assert (`%Some?   == "FStar.Pervasives.Native.uu___is_Some")
let _ = assert (`%Some    == "FStar.Pervasives.Native.Some")
let _ = assert (`%int     == "Prims.int")
let _ = assert (`%(Mkmyrec?.a) == "VQuote.__proj__Mkmyrec__item__a")
let _ = assert (`%(Mkmyrec?.b) == "VQuote.__proj__Mkmyrec__item__b")
