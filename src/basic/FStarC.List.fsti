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
module FStarC.List
open FStarC.Effect
open Prims

val isEmpty : (list 'a) -> Tot bool
val singleton : 'a -> list 'a
val hd : (list 'a) -> 'a
val length : (list 'a) -> Tot nat
val nth : (list 'a) -> int -> 'a
val rev_acc : (list 'a) -> (list 'a) -> Tot (list 'a)
val rev : (list 'a) -> Tot (list 'a)
val append : (list 'a) -> (list 'a) -> Tot (list 'a)
val ( @ ) :  (list 'a) -> (list 'a) -> Tot (list 'a)
val flatten : (list (list 'a)) -> Tot (list 'a)
val iter : ('a -> unit) -> (list 'a) -> unit
val iter2 : ('a -> 'b -> unit) -> (list 'a) -> list 'b -> unit
val iteri : (int -> 'a -> unit) -> (list 'a) -> unit
val map : ('a -> 'b) -> (list 'a) -> (list 'b)
val mapi_init : (int -> 'a -> 'b) -> (list 'a) -> int -> (list 'b)
val mapi : (int -> 'a -> 'b) -> (list 'a) -> (list 'b)
val concatMap : ('a -> (list 'b)) -> (list 'a) -> (list 'b)
val map2 : ('a -> 'b -> 'c) -> (list 'a) -> (list 'b) -> (list 'c)
val map3 : ('a -> 'b -> 'c -> 'd) -> (list 'a) -> (list 'b) -> (list 'c) -> (list 'd)
val fold_left : ('a -> 'b -> 'a) -> 'a -> (list 'b) -> 'a
val fold_left2 : ('s -> 'a -> 'b -> 's) -> 's -> (list 'a) -> (list 'b) -> 's
val fold_right : ('a -> 'b -> 'b) -> (list 'a) -> 'b -> 'b
val fold_right2 : ('a -> 'b -> 'c -> 'c) -> list 'a -> list 'b -> 'c -> 'c
val rev_map_onto : ('a -> 'b) -> (list 'a) -> (list 'b) -> (list 'b)
val init : (list 'a) -> list 'a
val last : (list 'a) -> 'a
val last_opt : list 'a -> option 'a
val existsb : f:('a -> bool) -> (list 'a) -> bool
val existsML : f:('a -> bool) -> (list 'a) -> bool
val find : f:('a -> bool) -> (list 'a) -> (option 'a)
val filter : ('a -> bool) -> (list 'a) -> (list 'a)
val for_all : ('a -> bool) -> (list 'a) -> bool
val forall2 : ('a -> 'b -> bool) -> (list 'a) -> (list 'b) -> bool
val collect : ('a -> (list 'b)) -> (list 'a) -> (list 'b)
val tryFind : ('a -> bool) -> (list 'a) -> (option 'a)
val tryPick : ('a -> (option 'b)) -> (list 'a) -> (option 'b)
val choose : ('a -> (option 'b)) -> (list 'a) -> (list 'b)
val partition : ('a -> bool) -> (list 'a) -> ((list 'a) & (list 'a))
val splitAt : int -> list 'a -> list 'a & list 'a
val split : (list ('a & 'b)) -> Tot ((list 'a) & (list 'b))
val unzip3 : list ('a & 'b & 'c) -> Tot ((list 'a) & (list 'b) & (list 'c))
val zip : (list 'a) -> (list 'b) -> (list ('a & 'b))
val zip3 : (list 'a) -> (list 'b) -> (list 'c) -> (list ('a & 'b & 'c))
val sortWith : ('a -> 'a -> int) -> (list 'a) -> (list 'a)
val bool_of_compare : ('a -> 'a -> Tot int) -> 'a -> 'a -> Tot bool
val tail : (list '_1225) -> (list '_1225)
val tl : list '_1230 -> list '_1230
val rev_append : (list '_5110) -> (list '_5110) -> Tot (list '_5110)
val concat : (list (list '_6116)) -> Tot (list '_6116)
val unzip : (list ('_36948 & '_36947)) -> Tot ((list '_36948) & (list '_36947))
val filter_map: ('a -> option 'b) -> list 'a -> list 'b
val count: #a:eqtype -> a -> (list a) -> Tot nat
val mem: #a:eqtype -> a -> (list a) -> Tot bool
val assoc: #a:eqtype -> #b:Type -> a -> (list (a & b)) -> Tot (option b)
val contains: #a:eqtype -> a -> (list a) -> Tot bool
val unique: #a:eqtype -> list a -> list a
val index: #a:eqtype -> (a -> bool) -> list a -> int
val span: #a:eqtype -> (a -> bool) -> list a -> Tot ((list a) & (list a))
val deduplicate (f: 'a -> 'a -> bool) (s: list 'a) : list 'a
val fold_left_map (f: 'a -> 'b -> 'a & 'c) (s: 'a) (l: list 'b) : 'a & list 'c
