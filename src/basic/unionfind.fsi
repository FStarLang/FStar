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
// (c) Microsoft Corporation. All rights reserved

#light "off"
module FStar.Unionfind

open FStar.Util

type puf<'a>
type p_uvar<'a>
val puf_empty: unit -> puf<'a>
val puf_fresh: puf<'a> -> 'a -> p_uvar<'a>
val puf_id: puf<'a> -> p_uvar<'a> -> int
val puf_find: puf<'a> -> p_uvar<'a> -> 'a
val puf_union: puf<'a> -> p_uvar<'a> -> p_uvar<'a> -> puf<'a>
val puf_equivalent: puf<'a> -> p_uvar<'a> -> p_uvar<'a> -> bool
val puf_change: puf<'a> -> p_uvar<'a> -> 'a -> puf<'a>
val puf_test: unit -> unit

// type uf_t<'a> = ref<puf_t<'a>>
// type p_uvar<'a> = { elem: 'a; id: int }

// val p_uvar_id : p_uvar<'a> -> int
// val p_fresh : uf_t<'a> -> 'a -> p_uvar<'a>
// val p_find : p_uvar<'a> -> 'a
// val p_change: p_uvar<'a> -> 'a -> unit
// val p_equivalent: p_uvar<'a> -> p_uvar<'a> -> bool
// val p_union : p_uvar<'a> -> p_uvar<'a> -> unit

//type cell<'a when 'a : not struct> = {mutable contents : contents<'a> }
//and contents<'a when 'a : not struct> =
//  | Data of list<'a> * int
//  | Fwd of cell<'a>
//type uvar<'a when 'a : not struct> = 'a cell
//
//val uvar_id: uvar<'a> -> int
//val fresh : 'a -> uvar<'a>
//val find : uvar<'a> -> 'a
//val change : uvar<'a> -> 'a -> unit
//val equivalent : uvar<'a> -> uvar<'a> -> bool
//val union : uvar<'a> -> uvar<'a> -> unit
//
//type tx = int //don't rely on representation
//val new_transaction: (unit -> tx)
//val rollback: tx -> unit
//val commit: tx -> unit
//val update_in_tx: ref<'a> -> 'a -> unit
