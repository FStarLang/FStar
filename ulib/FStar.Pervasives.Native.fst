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
module FStar.Pervasives.Native
open Prims
open FStar.Pervasives.Native.Tuple2

type option (a:Type) =
  | None : option a
  | Some : v:a -> option a

let fst (x:tuple2 'a 'b) :'a = Mktuple2?._1 x
let snd (x:tuple2 'a 'b) :'b = Mktuple2?._2 x
