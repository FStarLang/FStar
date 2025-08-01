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
module FStarC.Option

open FStarC.Effect

val map (f : 'a -> 'b) (o : option 'a)
  : option 'b

val must : option 'a -> 'a (* clearly partial *)

val dflt : 'a -> option 'a -> Tot 'a

val find: ('a -> bool) -> list 'a -> option 'a

val bind : option 'a -> ('a -> option 'b) -> option 'b

val catch : option 'a -> (unit -> option 'a) -> option 'a

val iter : ('a -> unit) -> option 'a -> unit
