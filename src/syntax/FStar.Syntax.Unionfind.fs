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
#light "off"
module FStar.Syntax.Unionfind
open FStar.All
open FStar.Syntax.Syntax
module S = FStar.Syntax.Syntax
module PU = FStar.Unionfind
module BU = FStar.Util
module L = FStar.List

type vops_t = {
    next_major : unit -> S.version;
    next_minor : unit -> S.version
}

let vops =
    let major = BU.mk_ref 0 in
    let minor = BU.mk_ref 0 in
    let next_major () =
        minor := 0;
        {major=(BU.incr major; !major);
         minor=0}
    in
    let next_minor () =
        {major=(!major);
         minor=(BU.incr minor; !minor)}
    in
    {next_major=next_major;
     next_minor=next_minor}

(* private *)
type tgraph = PU.puf<option<S.term>>
(* private *)
type ugraph = PU.puf<option<S.universe>>

(* The type of the current unionfind graph *)
type uf = {
  term_graph: tgraph;
  univ_graph: ugraph;
  version:version;
}

let empty (v:version) = {
    term_graph = PU.puf_empty();
    univ_graph = PU.puf_empty();
    version = v
  }

(*private*)
let version_to_string v = BU.format2 "%s.%s" (BU.string_of_int v.major) (BU.string_of_int v.minor)

(* private *)
let state : ref<uf> =
  BU.mk_ref (empty (vops.next_major()))

type tx =
    | TX of uf

(* getting and setting the current unionfind graph
     -- used during backtracking in the tactics engine *)
let get () = !state
let set (u:uf) = state := u
let reset () =
    let v = vops.next_major () in
//    printfn "UF version = %s" (version_to_string v);
    set (empty v)

////////////////////////////////////////////////////////////////////////////////
//Transacational interface, used in FStar.TypeChecker.Rel
////////////////////////////////////////////////////////////////////////////////
let new_transaction () =
    let tx = TX (get ()) in
    set ({get() with version=vops.next_minor()});
    tx
let commit (tx:tx) = ()
let rollback (TX uf) = set uf
let update_in_tx (r:ref<'a>) (x:'a) = ()

////////////////////////////////////////////////////////////////////////////////
//Interface for term unification
////////////////////////////////////////////////////////////////////////////////
(* private *)
let get_term_graph () = (get()).term_graph
let get_version () = (get()).version

(* private *)
let set_term_graph tg =
  set ({get() with term_graph = tg})

(*private*)
let chk_v (u, v) =
    let expected = get_version () in
    if v.major = expected.major
    && v.minor <= expected.minor
    then u
    else failwith (BU.format2
                        "Incompatible version for unification variable: current version is %s; got version %s"
                        (version_to_string expected)
                        (version_to_string v))

let uvar_id u  = PU.puf_id (get_term_graph()) (chk_v u)
let from_id n  = PU.puf_fromid (get_term_graph()) n, get_version()
let fresh ()   = PU.puf_fresh (get_term_graph()) None, get_version()
let find u     = PU.puf_find (get_term_graph()) (chk_v u)
let change u t = set_term_graph (PU.puf_change (get_term_graph()) (chk_v u) (Some t))
let equiv u v  = PU.puf_equivalent (get_term_graph()) (chk_v u) (chk_v v)
let union  u v = set_term_graph (PU.puf_union (get_term_graph()) (chk_v u) (chk_v v))

////////////////////////////////////////////////////////////////////////////////
//Interface for universe unification
////////////////////////////////////////////////////////////////////////////////

(*private*)
let get_univ_graph () = (get()).univ_graph

(*private*)
let set_univ_graph (ug:ugraph) =
  set ({get() with univ_graph = ug})

let univ_uvar_id u  = PU.puf_id (get_univ_graph()) (chk_v u)
let univ_from_id n  = PU.puf_fromid (get_univ_graph()) n, get_version()
let univ_fresh ()   = PU.puf_fresh (get_univ_graph()) None, get_version()
let univ_find u     = PU.puf_find (get_univ_graph()) (chk_v u)
let univ_change u t = set_univ_graph (PU.puf_change (get_univ_graph()) (chk_v u) (Some t))
let univ_equiv  u v = PU.puf_equivalent (get_univ_graph()) (chk_v u) (chk_v v)
let univ_union  u v = set_univ_graph (PU.puf_union (get_univ_graph()) (chk_v u) (chk_v v))
