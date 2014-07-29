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
module List

val hd: list 'a -> 'a
val tail: list 'a -> list 'a
val mem: 'a -> list 'a -> bool 
val map: ('a -> 'b) -> list 'a -> list 'b
val fold_left: ('a -> 'b -> 'a) -> 'a -> list 'b -> 'a
val fold_right: ('a -> 'b -> 'b) -> list 'a -> 'b -> 'b
val iter: ('a -> unit) -> list 'a -> unit
val assoc: 'a -> list ('a*'b) -> option 'b
val append: list 'a -> list 'a -> list 'a
val concatMap: ('a -> list 'b) -> list 'a -> list 'b

assume val forall2: ('a -> 'b -> bool) -> list 'a -> list 'b -> bool
assume val mapi: (int -> 'a -> 'b) -> list 'a -> list 'b
assume val map2: ('a -> 'b -> 'c) -> list 'a -> list 'b -> list 'c
assume val split: list ('a * 'b) -> PURE.Tot (list 'a * list 'b)
assume val unzip: list ('a * 'b) -> PURE.Tot (list 'a * list 'b)
assume val unzip3: list ('a * 'b * 'c) -> PURE.Tot (list 'a * list 'b * list 'c)
assume val zip: list 'a -> list 'b -> PURE.Tot (list ('a * 'b))
assume val zip3: list 'a -> list 'b -> list 'c -> PURE.Tot (list ('a * 'b * 'c))
assume val map3: ('a -> 'b -> 'c -> 'd) -> list 'a -> list 'b -> list 'c -> list 'd
assume val rev: list 'a -> PURE.Tot (list 'a)
assume val collect: ('a -> list 'b) -> list 'a -> list 'b
assume val tl: list 'a -> list 'a
assume val length: list 'a -> PURE.Tot int
assume val tryFind: ('a -> bool) -> list 'a -> option 'b
assume val concat: list (list 'a) -> PURE.Tot (list 'a)
assume val sortWith: ('a -> 'a -> int) -> list 'a -> list 'a
assume val choose: ('a -> option 'b) -> list 'a -> list 'b
assume val flatten: list (list 'a) -> PURE.Tot (list 'a)
assume val filter: ('a -> bool) -> list 'a -> list 'a
assume val partition: ('a -> bool) -> list 'a -> (list 'a * list 'a)
assume val contains: 'a -> list 'a -> PURE.Tot bool
assume val fold_left2: ('s -> 'a -> 'b -> 's) -> 's -> list 'a -> list 'b -> 's

