#light "off"
module FStar.Syntax.Unionfind
open FStar.All
module S = FStar.Syntax.Syntax
module PU = FStar.Unionfind
module BU = FStar.Util
module L = FStar.List

(* private *)
type tgraph = PU.puf<option<S.term>>
(* private *)
type ugraph = PU.puf<option<S.universe>>

(* The type of the current unionfind graph *)
type uf = {
  term_graph: tgraph;
  univ_graph: ugraph
}

(* Transaction idetifiers
      -- add a wrapper to allow making it abstract in F# *)
type tx = | TX of int

(* private *)
type transactional_state = {
  current:uf;
  rest:list<(tx * uf)>;
}

(* private *)
let state : ref<transactional_state> =
  let init = {
    term_graph = PU.puf_empty();
    univ_graph = PU.puf_empty()
  } in
  let tx_st = {
    current = init;
    rest = []
  } in
  BU.mk_ref tx_st

(* getting and setting the current unionfind graph
     -- used during backtracking in the tactics engine *)
let get () = (!state).current
let set (u:uf) = state := {!state with current = u}

////////////////////////////////////////////////////////////////////////////////
//Transacational interface, used in FStar.TypeChecker.Rel
////////////////////////////////////////////////////////////////////////////////
let new_transaction =
    let tx_ctr = BU.mk_ref 0 in
    fun () ->
        let tx = BU.incr tx_ctr; TX !tx_ctr in
        state := {!state with rest = (tx, get())::(!state).rest};
        tx
let commit_or_rollback (rb:bool) tx =
    let rec aux =
       function
       | [] -> failwith "Transaction identifier is invalid"
       | (tx', uf)::rest ->
         if tx=tx'
         then begin
           if rb then set uf;
           state := {!state with rest=rest}
         end
         else aux rest
    in
    aux (!state).rest
let rollback tx = commit_or_rollback true tx
let commit tx = commit_or_rollback false tx
(* remove this once we really migrate to using puf *)
let update_in_tx (r:ref<'a>) (x:'a) = ()

////////////////////////////////////////////////////////////////////////////////
//Interface for term unification
////////////////////////////////////////////////////////////////////////////////
(* private *)
let get_term_graph () = (get()).term_graph

(* private *)
let set_term_graph (tg:tgraph) =
  let next = {get() with term_graph = tg} in
  state := {!state with current=next}

let uvar_id u  = PU.puf_id (get_term_graph()) u
let fresh ()   = PU.puf_fresh (get_term_graph()) None
let find u     = PU.puf_find (get_term_graph()) u
let change u t = set_term_graph (PU.puf_change (get_term_graph()) u (Some t))
let equiv  u v = PU.puf_equivalent (get_term_graph()) u v
let union  u v = set_term_graph (PU.puf_union (get_term_graph()) u v)

////////////////////////////////////////////////////////////////////////////////
//Interface for universe unification
////////////////////////////////////////////////////////////////////////////////

(*private*)
let get_univ_graph () = (get()).univ_graph

(*private*)
let set_univ_graph (ug:ugraph) =
  let next = {get() with univ_graph = ug} in
  state := {!state with current=next}

let univ_uvar_id u  = PU.puf_id (get_univ_graph()) u
let univ_fresh ()   = PU.puf_fresh (get_univ_graph()) None
let univ_find u     = PU.puf_find (get_univ_graph()) u
let univ_change u t = set_univ_graph (PU.puf_change (get_univ_graph()) u (Some t))
let univ_equiv  u v = PU.puf_equivalent (get_univ_graph()) u v
let univ_union  u v = set_univ_graph (PU.puf_union (get_univ_graph()) u v)
