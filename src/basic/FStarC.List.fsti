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
val iter : ('a -> ML unit) -> (list 'a) -> ML unit
val iter2 : ('a -> 'b -> ML unit) -> (list 'a) -> list 'b -> ML unit
val iteri : (int -> 'a -> ML unit) -> (list 'a) -> ML unit
val map : ('a -> ML 'b) -> (list 'a) -> ML (list 'b)
val mapi_init : (int -> 'a -> ML 'b) -> (list 'a) -> int -> ML (list 'b)
val mapi : (int -> 'a -> ML 'b) -> (list 'a) -> ML (list 'b)
val concatMap : ('a -> ML (list 'b)) -> (list 'a) -> ML (list 'b)
val map2 : ('a -> 'b -> ML 'c) -> (list 'a) -> (list 'b) -> ML (list 'c)
val map3 : ('a -> 'b -> 'c -> ML 'd) -> (list 'a) -> (list 'b) -> (list 'c) -> ML (list 'd)
val fold_left : ('a -> 'b -> ML 'a) -> 'a -> (list 'b) -> ML 'a
val fold_left2 : ('s -> 'a -> 'b -> ML 's) -> 's -> (list 'a) -> (list 'b) -> ML 's
val fold_right : ('a -> 'b -> ML 'b) -> (list 'a) -> 'b -> ML 'b
val fold_right2 : ('a -> 'b -> 'c -> ML 'c) -> list 'a -> list 'b -> 'c -> ML 'c
val rev_map_onto : ('a -> ML 'b) -> (list 'a) -> (list 'b) -> ML (list 'b)
val init : (list 'a) -> list 'a
val last : (list 'a) -> 'a
val last_opt : list 'a -> option 'a
val existsb : f:('a -> ML bool) -> (list 'a) -> ML bool
val existsML : f:('a -> ML bool) -> (list 'a) -> ML bool
val find : f:('a -> ML bool) -> (list 'a) -> ML (option 'a)
val filter : ('a -> ML bool) -> (list 'a) -> ML (list 'a)
val for_all : ('a -> ML bool) -> (list 'a) -> ML bool
val forall2 : ('a -> 'b -> ML bool) -> (list 'a) -> (list 'b) -> ML bool
val collect : ('a -> ML (list 'b)) -> (list 'a) -> ML (list 'b)
val tryFind : ('a -> ML bool) -> (list 'a) -> ML (option 'a)
val tryPick : ('a -> ML (option 'b)) -> (list 'a) -> ML (option 'b)
val choose : ('a -> ML (option 'b)) -> (list 'a) -> ML (list 'b)
val partition : ('a -> ML bool) -> (list 'a) -> ML ((list 'a) & (list 'a))
val splitAt : int -> list 'a -> list 'a & list 'a
val split : (list ('a & 'b)) -> Tot ((list 'a) & (list 'b))
val unzip3 : list ('a & 'b & 'c) -> Tot ((list 'a) & (list 'b) & (list 'c))
val zip : (list 'a) -> (list 'b) -> (list ('a & 'b))
val zip3 : (list 'a) -> (list 'b) -> (list 'c) -> (list ('a & 'b & 'c))
val sortWith : ('a -> 'a -> ML int) -> (list 'a) -> ML (list 'a)
val tail : (list '_1225) -> (list '_1225)
val tl : list '_1230 -> list '_1230
val rev_append : (list '_5110) -> (list '_5110) -> Tot (list '_5110)
val concat : (list (list '_6116)) -> Tot (list '_6116)
val unzip : (list ('_36948 & '_36947)) -> Tot ((list '_36948) & (list '_36947))
val filter_map: ('a -> ML (option 'b)) -> list 'a -> ML (list 'b)
val count: #a:eqtype -> a -> (list a) -> Tot nat
val mem: #a:eqtype -> a -> (list a) -> Tot bool
val assoc: #a:eqtype -> #b:Type -> a -> (list (a & b)) -> Tot (option b)
val contains: #a:eqtype -> a -> (list a) -> Tot bool
val unique: #a:eqtype -> list a -> list a
val index: #a:eqtype -> (a -> bool) -> list a -> int
val span: #a:eqtype -> (a -> bool) -> list a -> Tot ((list a) & (list a))
val deduplicate (f: 'a -> 'a -> ML bool) (s: list 'a) : ML (list 'a)
val fold_left_map (f: 'a -> 'b -> ML ('a & 'c)) (s: 'a) (l: list 'b) : ML ('a & list 'c)
