(*
   Copyright 2008-2014 Microsoft Research

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

module FStar.Syntax.Unionfind
open FStar.Compiler.Effect
open FStar.Errors
open FStar.Syntax.Syntax

module Range = FStar.Compiler.Range
module S     = FStar.Syntax.Syntax
module PU    = FStar.Unionfind
module BU    = FStar.Compiler.Util
module L     = FStar.Compiler.List
module O     = FStar.Options

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
type tgraph = PU.puf (option S.term & S.uvar_decoration)
(* private *)
type ugraph = PU.puf (option S.universe)

(* The type of the current unionfind graph *)
type uf = {
  term_graph: tgraph;
  univ_graph: ugraph;
  version:version;
  ro:bool;
}

let empty (v:version) = {
    term_graph = PU.puf_empty();
    univ_graph = PU.puf_empty();
    version = v;
    ro = false;
  }

(*private*)
let version_to_string v = BU.format2 "%s.%s" (BU.string_of_int v.major) (BU.string_of_int v.minor)

(* private *)
let state : ref uf =
  BU.mk_ref (empty (vops.next_major()))

type tx =
    | TX of uf

(* getting and setting the current unionfind graph
     -- used during backtracking in the tactics engine *)
let get () = !state


let set_ro () =
    let s = get () in
    state := { s with ro = true }

let set_rw () =
    let s = get () in
    state := { s with ro = false }

let with_uf_enabled (f : unit -> 'a) : 'a =
    let s = get () in
    set_rw ();
    let restore () = if s.ro then set_ro () in

    let r =
        if O.trace_error ()
        then f ()
        else try f ()
             with | e -> begin
                    restore ();
                    raise e
                  end
    in
    restore ();
    r

let fail_if_ro () =
    if (get ()).ro then
      raise_error (Fatal_BadUvar, "Internal error: UF graph was in read-only mode")
                  Range.dummyRange

let set (u:uf) =
    fail_if_ro ();
    state := u

let reset () =
    fail_if_ro ();
    let v = vops.next_major () in
//    printfn "UF version = %s" (version_to_string v);
    set ({ empty v with ro = false })

////////////////////////////////////////////////////////////////////////////////
//Transacational interface, used in FStar.TypeChecker.Rel
////////////////////////////////////////////////////////////////////////////////
let new_transaction () =
    let tx = TX (get ()) in
    set ({get() with version=vops.next_minor()});
    tx
let commit (tx:tx) = ()
let rollback (TX uf) = set uf
let update_in_tx (r:ref 'a) (x:'a) = ()

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
let chk_v_t (su:S.uvar) = 
    let u, v, rng = su in
    let uvar_to_string u = "?" ^ (PU.puf_unique_id u |> BU.string_of_int) in
    let expected = get_version () in
    if v.major = expected.major
    && v.minor <= expected.minor
    then u
    else
      raise_error (Fatal_BadUvar,
                   BU.format3 "Internal error: incompatible version for term unification variable %s: current version is %s; got version %s"
                        (uvar_to_string u)
                        (version_to_string expected)
                        (version_to_string v))
                  rng

let uvar_id u  = PU.puf_id (get_term_graph()) (chk_v_t u)
let uvar_unique_id u = PU.puf_unique_id (chk_v_t u)
let fresh decoration (rng:Range.range)  =
    fail_if_ro ();
    PU.puf_fresh (get_term_graph()) (None, decoration), get_version(), rng

let find_core u = PU.puf_find (get_term_graph()) (chk_v_t u)
let find u     = fst (find_core u)
let find_decoration u = snd (find_core u)
let change u t = let _, dec = find_core u in set_term_graph (PU.puf_change (get_term_graph()) (chk_v_t u) (Some t, dec))
let change_decoration u d =  let t, _ = find_core u in set_term_graph (PU.puf_change (get_term_graph()) (chk_v_t u) (t, d))
let equiv u v  = PU.puf_equivalent (get_term_graph()) (chk_v_t u) (chk_v_t v)
let union  u v = set_term_graph (PU.puf_union (get_term_graph()) (chk_v_t u) (chk_v_t v))

////////////////////////////////////////////////////////////////////////////////
//Interface for universe unification
////////////////////////////////////////////////////////////////////////////////

(*private*)
let get_univ_graph () = (get()).univ_graph

(*private*)
let chk_v_u (u, v, rng) =
    let uvar_to_string u = "?" ^ (PU.puf_unique_id u |> BU.string_of_int) in
    let expected = get_version () in
    if v.major = expected.major
    && v.minor <= expected.minor
    then u
    else
      raise_error (Fatal_BadUvar,
                   BU.format3 "Internal error: incompatible version for universe unification variable %s: current version is %s; got version %s"
                        (uvar_to_string u)
                        (version_to_string expected)
                        (version_to_string v))
                  rng

(*private*)
let set_univ_graph (ug:ugraph) =
  set ({get() with univ_graph = ug})

let univ_uvar_id u  = PU.puf_id (get_univ_graph()) (chk_v_u u)
let univ_fresh (rng:Range.range) =
    fail_if_ro ();
    PU.puf_fresh (get_univ_graph()) None, get_version(), rng

let univ_find u     = PU.puf_find (get_univ_graph()) (chk_v_u u)
let univ_change u t = set_univ_graph (PU.puf_change (get_univ_graph()) (chk_v_u u) (Some t))
let univ_equiv  u v = PU.puf_equivalent (get_univ_graph()) (chk_v_u u) (chk_v_u v)
let univ_union  u v = set_univ_graph (PU.puf_union (get_univ_graph()) (chk_v_u u) (chk_v_u v))
