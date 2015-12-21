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
val isEmpty : (list 'a) -> Tot bool
val hd : (list 'a) -> 'a
val length : (list 'a) -> Tot nat
val nth : (list 'a) -> int -> 'a
val total_nth : (list 'a) -> nat -> Tot (option 'a)
val count : 'a -> (list 'a) -> Tot nat
val rev_acc : (list 'a) -> (list 'a) -> Tot (list 'a)
val rev : (list 'a) -> Tot (list 'a)
val append : (list 'a) -> (list 'a) -> Tot (list 'a)
val flatten : (list (list 'a)) -> Tot (list 'a)
val iter : ('a -> unit) -> (list 'a) -> unit
val iteri : (int -> 'a -> unit) -> (list 'a) -> unit
val iterT : ('a -> Tot unit) -> (list 'a) -> Tot unit
val map : ('a -> 'b) -> (list 'a) -> (list 'b)
val mapT : ('a -> Tot 'b) -> (list 'a) -> Tot (list 'b)
val mapi_init : (int -> 'a -> 'b) -> (list 'a) -> int -> (list 'b)
val mapi_initT : (int -> 'a -> Tot 'b) -> (list 'a) -> int -> Tot (list 'b)
val mapi : (int -> 'a -> 'b) -> (list 'a) -> (list 'b)
val mapiT : (int -> 'a -> Tot 'b) -> (list 'a) -> Tot (list 'b)
val concatMap : ('a -> (list 'b)) -> (list 'a) -> (list 'b)
val concatMapT : ('a -> Tot (list 'b)) -> (list 'a) -> Tot (list 'b)
val map2 : ('a -> 'b -> 'c) -> (list 'a) -> (list 'b) -> (list 'c)
val map3 : ('a -> 'b -> 'c -> 'd) -> (list 'a) -> (list 'b) -> (list 'c) -> (list 'd)
val fold_left : ('a -> 'b -> 'a) -> 'a -> (list 'b) -> 'a
val fold_leftT : ('a -> 'b -> Tot 'a) -> 'a -> l:(list 'b) -> Tot 'a (decreases l)
val fold_left2 : ('s -> 'a -> 'b -> 's) -> 's -> (list 'a) -> (list 'b) -> 's
val fold_right : ('a -> 'b -> 'b) -> (list 'a) -> 'b -> 'b
val fold_rightT : ('a -> 'b -> Tot 'b) -> (list 'a) -> 'b -> Tot 'b
val mem : 'a -> (list 'a) -> Tot bool
val existsb : f:('a -> Tot bool) -> (list 'a) -> Tot bool
val find : f:('a -> Tot bool) -> (list 'a) -> Tot (option (x:'a{(f x)}))
val filter : ('a -> bool) -> (list 'a) -> (list 'a)
val filterT : f:('a -> Tot bool) -> (list 'a) -> Tot (m:(list 'a){(forall x. ((mem x m) ==> (f x)))})
val for_all : ('a -> bool) -> (list 'a) -> bool
val for_allT : ('a -> Tot bool) -> (list 'a) -> Tot bool
val forall2 : ('a -> 'b -> bool) -> (list 'a) -> (list 'b) -> bool
val collect : ('a -> (list 'b)) -> (list 'a) -> (list 'b)
val collectT : ('a -> Tot (list 'b)) -> (list 'a) -> Tot (list 'b)
val tryFind : ('a -> bool) -> (list 'a) -> (option 'a)
val tryFindT : ('a -> Tot bool) -> (list 'a) -> Tot (option 'a)
val tryPick : ('a -> (option 'b)) -> (list 'a) -> (option 'b)
val tryPickT : ('a -> Tot (option 'b)) -> (list 'a) -> Tot (option 'b)
val choose : ('a -> (option 'b)) -> (list 'a) -> (list 'b)
val chooseT : ('a -> Tot (option 'b)) -> (list 'a) -> Tot (list 'b)
val partition : ('a -> bool) -> (list 'a) -> (Tuple2 (list 'a) (list 'a))
val partitionT : f:('a -> Tot bool) -> (list 'a) -> Tot (Tuple2 (list 'a) (list 'a))
val assoc : 'a -> (list (Tuple2 'a 'b)) -> Tot (option 'b)
val split : (list (Tuple2 'a 'b)) -> Tot (Tuple2 (list 'a) (list 'b))
val unzip3 : (list (Tuple3 'a 'b 'c)) -> Tot (Tuple3 (list 'a) (list 'b) (list 'c))
val zip : (list 'a) -> (list 'b) -> (list (Tuple2 'a 'b))
val zip3 : (list 'a) -> (list 'b) -> (list 'c) -> (list (Tuple3 'a 'b 'c))
val sortWith : ('a -> 'a -> int) -> (list 'a) -> (list 'a)
val partition_length : f:('a -> Tot bool) -> l:(list 'a) -> Lemma (unit)
val bool_of_compare : ('a -> 'a -> Tot int) -> 'a -> 'a -> Tot bool
val sortWithT : ('a -> 'a -> Tot int) -> l:(list 'a) -> Tot (list 'a)


val isEmptyT : (list '_645) -> Tot bool
val tail : (list '_1225) -> (list '_1225)
val tl : (list '_1230) -> (list '_1230)
val lengthT : (list '_1585) -> Tot nat
val countT : '_4383 -> (list '_4383) -> Tot nat
val rev_append : (list '_5110) -> (list '_5110) -> Tot (list '_5110)
val revT : (list '_5131) -> Tot (list '_5131)
val appendT : (list '_5687) -> (list '_5687) -> Tot (list '_5687)
val flattenT : (list (list '_6110)) -> Tot (list '_6110)
val concat : (list (list '_6116)) -> Tot (list '_6116)
val concatT : (list (list '_6122)) -> Tot (list '_6122)
val memT : '_17768 -> (list '_17768) -> Tot bool
val contains : '_17778 -> (list '_17778) -> Tot bool
val containsT : '_17788 -> (list '_17788) -> Tot bool
val findT : f:('_19377 -> Tot bool) -> (list '_19377) -> Tot (option (x:'_19377{(f x)}))
val assocT : '_35042 -> (list (Tuple2 '_35042 '_35041)) -> Tot (option '_35041)
val splitT : (list (Tuple2 '_36940 '_36939)) -> Tot (Tuple2 (list '_36940) (list '_36939))
val unzip : (list (Tuple2 '_36948 '_36947)) -> Tot (Tuple2 (list '_36948) (list '_36947))
val unzipT : (list (Tuple2 '_36956 '_36955)) -> Tot (Tuple2 (list '_36956) (list '_36955))
val unzip3T : (list (Tuple3 '_40328 '_40327 '_40326)) -> Tot (Tuple3 (list '_40328) (list '_40327) (list '_40326))
(* This signature (just like [contains] and others) does not require that 'a be
   comparable for F#, which means that after extraction, your code may not
   compile with F#. OCaml does not have this problem, as it features a
   polymorphic comparison. *)
val unique: list 'a -> list 'a
