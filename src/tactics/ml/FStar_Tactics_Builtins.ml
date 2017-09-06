open Prims
open FStar_Tactics_Types
open FStar_Tactics_Effect
module E = FStar_Tactics_Effect
module B = FStar_Tactics_Basic
module RT = FStar_Reflection_Types

let interpret_tac (t: 'a B.tac) (ps: proofstate): 'a E.__result =
  match B.run t ps with
  | B.Success (a, state) -> E.Success (a, state)
  | B.Failed (s, state) -> E.Failed (s, state)

let uninterpret_tac (t: 'a __tac) (ps: proofstate): 'a B.result =
  match t ps with
  | E.Success (a, state) -> B.Success (a, state)
  | E.Failed (s, state) -> B.Failed (s, state)

let to_tac_0 (t: 'a __tac): 'a B.tac =
  (fun (ps: proofstate) ->
    uninterpret_tac t ps) |> B.mk_tac

let from_tac_0 (t: 'a B.tac): 'a __tac =
  fun (ps: proofstate) ->
    interpret_tac t ps

let from_tac_1 (t: 'a -> 'b B.tac): 'a  -> 'b __tac =
  fun (x: 'a) ->
    fun (ps: proofstate) ->
      let m = t x in
      interpret_tac m ps

let from_tac_2 (t: 'a -> 'b -> 'c B.tac): 'a  -> 'b -> 'c __tac =
  fun (x: 'a) ->
    fun (y: 'b) ->
      fun (ps: proofstate) ->
        let m = t x y in
        interpret_tac m ps

let from_tac_3 (t: 'a -> 'b -> 'c -> 'd B.tac): 'a  -> 'b -> 'c -> 'd __tac =
  fun (x: 'a) ->
    fun (y: 'b) ->
      fun (z: 'c) ->
        fun (ps: proofstate) ->
          let m = t x y z in
          interpret_tac m ps

let __cur_env: RT.env __tac = from_tac_0 B.cur_env
let cur_env: unit -> RT.env __tac = fun () -> __cur_env

let __cur_goal: RT.term __tac = from_tac_0 B.cur_goal'
let cur_goal: unit -> RT.term __tac = fun () -> __cur_goal

let __cur_witness: RT.term __tac = from_tac_0 B.cur_witness
let cur_witness: unit -> RT.term __tac = fun () -> __cur_witness

let __embed =
  Obj.magic (fun uu____118  -> failwith "Not yet implemented:__embed")
let quote x uu____135 s = E.Success ((__embed x), s)

let __trytac (t: 'a __tac): ('a option) __tac = from_tac_1 B.trytac (to_tac_0 t)
let trytac: 'a E.tactic -> unit -> ('a option) __tac = fun t -> fun () -> __trytac (E.reify_tactic t)

let __trivial: unit __tac = from_tac_0 B.trivial
let trivial: unit -> unit __tac = fun () -> __trivial

let __norm (s: FStar_Reflection_Data.norm_step list): unit __tac = from_tac_1 B.norm s 
let norm: FStar_Reflection_Data.norm_step list -> unit -> unit __tac = fun s -> fun () -> __norm s

let __intro: RT.binder __tac = from_tac_0 B.intro
let intro: unit -> RT.binder __tac = fun () -> __intro

let __revert: unit __tac = from_tac_0 B.revert
let revert: unit -> unit __tac = fun () -> __revert

let __clear: unit __tac = from_tac_0 B.clear
let clear: unit -> unit __tac = fun () -> __clear

let __rewrite (h: RT.binder): unit __tac = from_tac_1 B.rewrite h
let rewrite: RT.binder -> unit -> unit __tac = fun b  -> fun () -> __rewrite b

let __smt: unit __tac = from_tac_0 B.smt
let smt: unit -> unit __tac = fun ()  -> __smt

let __divide (n:int) (f: 'a __tac) (g: 'b __tac): ('a * 'b) __tac = from_tac_3 B.divide n (to_tac_0 f) (to_tac_0 g)
let divide: int -> 'a E.tactic -> 'b E.tactic -> ('a * 'b) E.tactic = fun n f g -> fun () -> __divide n (E.reify_tactic f) (E.reify_tactic g)

let __seq (t1: unit __tac) (t2: unit __tac): unit __tac = from_tac_2 B.seq (to_tac_0 t1) (to_tac_0 t2)
let seq: unit E.tactic -> unit E.tactic -> unit -> unit __tac = fun f  -> fun g  -> fun () -> __seq (E.reify_tactic f) (E.reify_tactic g)

let __exact (t: RT.term): unit __tac = from_tac_1 B.exact t
let exact: RT.term E.tactic -> unit -> unit __tac =
  fun t  -> fun () -> fun ps ->
    match (t ()) ps with
    | E.Success (a, state) -> __exact a state
    | E.Failed (s, state) -> E.Failed (s, state)

let __exact_lemma (t: RT.term): unit __tac = from_tac_1 B.exact_lemma t
let exact_lemma: RT.term E.tactic -> unit -> unit __tac =
  fun t  -> fun () -> fun ps ->
    match (t ()) ps with
    | E.Success (a, state) -> __exact_lemma a state
    | E.Failed (s, state) -> E.Failed (s, state)

let __apply (t: RT.term): unit __tac = from_tac_1 B.apply t
let apply: RT.term E.tactic -> unit -> unit __tac =
  fun t  -> fun () -> fun ps ->
    match (t ()) ps with
    | E.Success (a, state) -> __apply a state
    | E.Failed (s, state) -> E.Failed (s, state)

let __apply_lemma (t: RT.term): unit __tac = from_tac_1 B.apply_lemma t
let apply_lemma: RT.term E.tactic -> unit -> unit __tac =
  fun t  -> fun () -> fun ps ->
    match (t ()) ps with
    | E.Success (a, state) -> __apply_lemma a state
    | E.Failed (s, state) -> E.Failed (s, state)

let __print (s: string): unit __tac = from_tac_1 (fun x -> B.ret (B.tacprint x)) s
let print: string -> unit -> unit __tac = fun s -> fun () -> __print s

let __dump (s: string): unit __tac = from_tac_1 B.print_proof_state s
let dump: string -> unit -> unit __tac = fun s -> fun () -> __dump s

let __dump1 (s: string): unit __tac = from_tac_1 B.print_proof_state1 s
let dump1: string -> unit -> unit __tac = fun s -> fun () -> __dump1 s

let __trefl: unit __tac = from_tac_0 B.trefl
let trefl: unit -> unit __tac = fun () -> __trefl

let __pointwise (t: unit __tac): unit __tac = from_tac_1 B.pointwise (to_tac_0 t)
let pointwise: unit E.tactic -> unit -> unit __tac = fun tau -> fun () -> __pointwise (E.reify_tactic tau)

let __later: unit __tac = from_tac_0 B.later
let later: unit -> unit __tac = fun () -> __later

let __flip: unit __tac = from_tac_0 B.flip
let flip: unit -> unit __tac = fun () -> __flip

let __qed: unit __tac = from_tac_0 B.qed
let qed: unit -> unit __tac = fun () -> __qed

let __prune (s: string): unit __tac = from_tac_1 B.prune s
let prune: string -> unit -> unit __tac = fun ns  -> fun () -> __prune ns

let __addns (s: string): unit __tac = from_tac_1 B.addns s
let addns: string -> unit -> unit __tac = fun ns  -> fun () -> __addns ns

let __cases (t: RT.term): (RT.term * RT.term) __tac = from_tac_1 B.cases t
let cases: RT.term -> unit -> (RT.term * RT.term) __tac = fun t  -> fun () -> __cases t

let __set_options (s: string) : unit __tac = from_tac_1 B.set_options s
let set_options : string -> unit -> unit __tac = fun s -> fun () -> __set_options s

let __uvar_env (e : RT.env) (o : RT.term option) : RT.term __tac = from_tac_2 B.uvar_env e o
let uvar_env : RT.env -> RT.term option -> unit -> RT.term __tac = fun e o -> fun () -> __uvar_env e o

let __unify (t1 : RT.term) (t2 : RT.term) : bool __tac = from_tac_2 B.unify t1 t2
let unify : RT.term -> RT.term -> unit -> bool __tac = fun t1 t2 -> fun () -> __unify t1 t2
