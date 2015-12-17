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
module FStar.List
open Prims

val isEmpty : (list<'a>) -> Tot<bool>
val hd : (list<'a>) -> 'a
val length : (list<'a>) -> Tot<nat>
val nth : (list<'a>) -> int -> 'a
val count<'a when 'a : equality> : 'a -> (list<'a>) -> Tot<nat>
val rev_acc : (list<'a>) -> (list<'a>) -> Tot<(list<'a>)>
val rev : (list<'a>) -> Tot<(list<'a>)>
val append : (list<'a>) -> (list<'a>) -> Tot<(list<'a>)>
val flatten : (list<(list<'a>)>) -> Tot<(list<'a>)>
val iter : ('a -> unit) -> (list<'a>) -> unit
val iteri : (int -> 'a -> unit) -> (list<'a>) -> unit
val map : ('a -> 'b) -> (list<'a>) -> (list<'b>)
val mapi_init : (int -> 'a -> 'b) -> (list<'a>) -> int -> (list<'b>)
val mapi : (int -> 'a -> 'b) -> (list<'a>) -> (list<'b>)
val concatMap : ('a -> (list<'b>)) -> (list<'a>) -> (list<'b>)
val map2 : ('a -> 'b -> 'c) -> (list<'a>) -> (list<'b>) -> (list<'c>)
val map3 : ('a -> 'b -> 'c -> 'd) -> (list<'a>) -> (list<'b>) -> (list<'c>) -> (list<'d>)
val fold_left : ('a -> 'b -> 'a) -> 'a -> (list<'b>) -> 'a
val fold_left2 : ('s -> 'a -> 'b -> 's) -> 's -> (list<'a>) -> (list<'b>) -> 's
val fold_right : ('a -> 'b -> 'b) -> (list<'a>) -> 'b -> 'b
val mem<'a when 'a : equality>  : 'a -> (list<'a>) -> Tot<bool>
val existsb : f:('a -> Tot<bool>) -> (list<'a>) -> Tot<bool>
val find : f:('a -> Tot<bool>) -> (list<'a>) -> Tot<(option<'a>)>
val filter : ('a -> bool) -> (list<'a>) -> (list<'a>)
val for_all : ('a -> bool) -> (list<'a>) -> bool
val forall2 : ('a -> 'b -> bool) -> (list<'a>) -> (list<'b>) -> bool
val collect : ('a -> (list<'b>)) -> (list<'a>) -> (list<'b>)
val tryFind : ('a -> bool) -> (list<'a>) -> (option<'a>)
val tryPick : ('a -> (option<'b>)) -> (list<'a>) -> (option<'b>)
val choose : ('a -> (option<'b>)) -> (list<'a>) -> (list<'b>)
val partition : ('a -> bool) -> (list<'a>) -> ((list<'a>) * (list<'a>))
val assoc<'a, 'b when 'a : equality>  : 'a -> (list<('a * 'b)>) -> Tot<(option<'b>)>
val split : (list<('a * 'b)>) -> Tot<((list<'a>) * (list<'b>))>
val unzip3 : (list<('a * 'b * 'c)>) -> Tot<((list<'a>) * (list<'b>) * (list<'c>))>
val zip : (list<'a>) -> (list<'b>) -> (list<('a * 'b)>)
val zip3 : (list<'a>) -> (list<'b>) -> (list<'c>) -> (list<('a * 'b * 'c)>)
val sortWith : ('a -> 'a -> int) -> (list<'a>) -> (list<'a>)
val bool_of_compare : ('a -> 'a -> Tot<int>) -> 'a -> 'a -> Tot<bool>
val tail : (list<'_1225>) -> (list<'_1225>)
val tl : (list<'_1230> -> list<'_1230>)
val rev_append : (list<'_5110>) -> (list<'_5110>) -> Tot<(list<'_5110>)>
val concat : (list<(list<'_6116>)>) -> Tot<(list<'_6116>)>
val contains<'_17778 when '_17778 : equality>  : '_17778 -> (list<'_17778>) -> Tot<bool>
val unzip : (list<('_36948 * '_36947)>) -> Tot<((list<'_36948>) * (list<'_36947>))>
val unique<'a when 'a:equality> : list<'a> -> list<'a>

