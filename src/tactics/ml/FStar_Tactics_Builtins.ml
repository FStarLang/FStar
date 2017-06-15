open Prims
open FStar_Tactics_Effect
module E = FStar_Tactics_Effect
module B = FStar_Tactics_Basic
module RT = FStar_Reflection_Types


let transform_tactic_0 (t: 'a B.tac): 'a __tac =
  fun (ps: FStar_Tactics_Types.proofstate) ->
    match B.run t ps with
    | Success (a, state) -> E.Success (a, state)
    | Failed (s, state) -> E.Failed (s, state)

let transform_tactic_1 (t: 'a -> 'b B.tac): 'a  -> 'b __tac =
  fun (x: 'a) ->
    fun (ps: FStar_Tactics_Types.proofstate) ->
      let m = t x in
      match B.run m ps with
      | Success (a, state) -> E.Success (a, state)
      | Failed (s, state) -> E.Failed (s, state)

let transform_tactic_2 (t: 'a -> 'b -> 'c B.tac): 'a  -> 'b -> 'c __tac =
  fun (x: 'a) ->
    fun (y: 'b) ->
      fun (ps: FStar_Tactics_Types.proofstate) ->
        let m = t x y in
        match B.run m ps with
        | Success (a, state) -> E.Success (a, state)
        | Failed (s, state) -> E.Failed (s, state)


let __cur_env: FStar_Reflection_Types.env FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____8  -> failwith "Not yet implemented:__cur_env")
let cur_env:
  Prims.unit -> FStar_Reflection_Types.env FStar_Tactics_Effect.__tac =
  fun uu____33  -> __cur_env
let __cur_goal: RT.term __tac = transform_tactic_0 B.cur_goal'
let cur_goal:
  Prims.unit -> FStar_Reflection_Types.term FStar_Tactics_Effect.__tac =
  fun uu____68  -> __cur_goal
let __cur_witness: FStar_Reflection_Types.term FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____78  -> failwith "Not yet implemented:__cur_witness")
let cur_witness:
  Prims.unit -> FStar_Reflection_Types.term FStar_Tactics_Effect.__tac =
  fun uu____103  -> __cur_witness
let __embed =
  Obj.magic (fun uu____118  -> failwith "Not yet implemented:__embed")
let quote x uu____135 s = FStar_Tactics_Effect.Success ((__embed x), s)
let __trytac =
  Obj.magic (fun uu____162  -> failwith "Not yet implemented:__trytac")
let trytac t uu____209 = __trytac (FStar_Tactics_Effect.reify_tactic t)
let __trivial: Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____230  -> failwith "Not yet implemented:__trivial")
let trivial: Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun uu____249  -> __trivial
let __norm:
  FStar_Reflection_Syntax.norm_step Prims.list ->
    Prims.unit FStar_Tactics_Effect.__tac
  = Obj.magic (fun uu____263  -> failwith "Not yet implemented:__norm")
let norm:
  FStar_Reflection_Syntax.norm_step Prims.list ->
    Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac
  = fun steps  -> fun uu____278  -> __norm steps
let __intro: FStar_Reflection_Types.binder FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____288  -> failwith "Not yet implemented:__intro")
let intro:
  Prims.unit -> FStar_Reflection_Types.binder FStar_Tactics_Effect.__tac =
  fun uu____307  -> __intro
let __revert: Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____317  -> failwith "Not yet implemented:__revert")
let revert: Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun uu____336  -> __revert
let __clear: Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____346  -> failwith "Not yet implemented:__clear")
let clear: Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun uu____365  -> __clear
let __rewrite:
  FStar_Reflection_Types.binder -> Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____378  -> failwith "Not yet implemented:__rewrite")
let rewrite:
  FStar_Reflection_Types.binder ->
    Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac
  = fun b  -> fun uu____390  -> __rewrite b
let __smt: unit __tac = transform_tactic_0 B.smt
let smt: Prims.unit -> Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun uu____413  -> fun uu____415  -> __smt
let __focus:
  Prims.unit FStar_Tactics_Effect.__tac ->
    Prims.unit FStar_Tactics_Effect.__tac
  = Obj.magic (fun uu____433  -> failwith "Not yet implemented:__focus")
let focus:
  Prims.unit FStar_Tactics_Effect.tactic ->
    Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac
  = fun f  -> fun uu____456  -> __focus (FStar_Tactics_Effect.reify_tactic f)
let __seq:
  Prims.unit FStar_Tactics_Effect.__tac ->
    Prims.unit FStar_Tactics_Effect.__tac ->
      Prims.unit FStar_Tactics_Effect.__tac
  =
  Obj.magic
    (fun uu____492  -> fun uu____493  -> failwith "Not yet implemented:__seq")
let seq:
  Prims.unit FStar_Tactics_Effect.tactic ->
    Prims.unit FStar_Tactics_Effect.tactic ->
      Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac
  =
  fun f  ->
    fun g  ->
      fun uu____530  ->
        __seq (FStar_Tactics_Effect.reify_tactic f)
          (FStar_Tactics_Effect.reify_tactic g)
let __exact:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____561  -> failwith "Not yet implemented:__exact")
let exact:
  FStar_Reflection_Types.term FStar_Tactics_Effect.tactic ->
    Prims.unit ->
      FStar_Tactics_Types.proofstate ->
        Prims.unit FStar_Tactics_Effect.__result
  =
  fun t  ->
    fun uu____582  ->
      fun p  ->
        match (t ()) p with
        | FStar_Tactics_Effect.Success (a,q) -> __exact a q
        | FStar_Tactics_Effect.Failed (msg,q) ->
            FStar_Tactics_Effect.Failed (msg, q)
let __exact_lemma:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____629  -> failwith "Not yet implemented:__exact_lemma")
let exact_lemma:
  FStar_Reflection_Types.term FStar_Tactics_Effect.tactic ->
    Prims.unit ->
      FStar_Tactics_Types.proofstate ->
        Prims.unit FStar_Tactics_Effect.__result
  =
  fun t  ->
    fun uu____650  ->
      fun p  ->
        match (t ()) p with
        | FStar_Tactics_Effect.Success (a,q) -> __exact_lemma a q
        | FStar_Tactics_Effect.Failed (msg,q) ->
            FStar_Tactics_Effect.Failed (msg, q)
let __apply:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____697  -> failwith "Not yet implemented:__apply")
let apply:
  FStar_Reflection_Types.term FStar_Tactics_Effect.tactic ->
    Prims.unit ->
      FStar_Tactics_Types.proofstate ->
        Prims.unit FStar_Tactics_Effect.__result
  =
  fun t  ->
    fun uu____718  ->
      fun p  ->
        match (t ()) p with
        | FStar_Tactics_Effect.Success (a,q) -> __apply a q
        | FStar_Tactics_Effect.Failed (msg,q) ->
            FStar_Tactics_Effect.Failed (msg, q)
let __apply_lemma:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____765  -> failwith "Not yet implemented:__apply_lemma")
let apply_lemma:
  FStar_Reflection_Types.term FStar_Tactics_Effect.tactic ->
    Prims.unit ->
      FStar_Tactics_Types.proofstate ->
        Prims.unit FStar_Tactics_Effect.__result
  =
  fun t  ->
    fun uu____786  ->
      fun p  ->
        match (t ()) p with
        | FStar_Tactics_Effect.Success (a,q) -> __apply_lemma a q
        | FStar_Tactics_Effect.Failed (msg,q) ->
            FStar_Tactics_Effect.Failed (msg, q)
let __print: Prims.string -> Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____833  -> failwith "Not yet implemented:__print")
let print:
  Prims.string -> Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun msg  -> fun uu____845  -> __print msg
let __dump (s: string): unit __tac = transform_tactic_1 B.print_proof_state s
let dump: Prims.string -> Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac
  = fun msg  -> fun uu____870  -> __dump msg
let __dump1: Prims.string -> Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____883  -> failwith "Not yet implemented:__dump1")
let dump1:
  Prims.string -> Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun msg  -> fun uu____895  -> __dump1 msg
let __trefl: Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____905  -> failwith "Not yet implemented:__trefl")
let trefl: Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun uu____924  -> __trefl
let __pointwise:
  Prims.unit FStar_Tactics_Effect.__tac ->
    Prims.unit FStar_Tactics_Effect.__tac
  = Obj.magic (fun uu____942  -> failwith "Not yet implemented:__pointwise")
let pointwise:
  Prims.unit FStar_Tactics_Effect.tactic ->
    Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac
  =
  fun tau  ->
    fun uu____965  -> __pointwise (FStar_Tactics_Effect.reify_tactic tau)
let __later: Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____985  -> failwith "Not yet implemented:__later")
let later: Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun uu____1004  -> __later
let __flip: Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____1014  -> failwith "Not yet implemented:__flip")
let flip: Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun uu____1033  -> __flip
let __qed: Prims.unit FStar_Tactics_Effect.__tac =
  Obj.magic (fun uu____1043  -> failwith "Not yet implemented:__qed")
let qed: Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun uu____1062  -> __qed
let __prune (s: string): unit __tac = transform_tactic_1 B.prune s
let prune:
  Prims.string -> Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun ns  -> fun uu____1087  -> __prune ns
let __addns (s: string): unit __tac = transform_tactic_1 B.addns s
let addns:
  Prims.string -> Prims.unit -> Prims.unit FStar_Tactics_Effect.__tac =
  fun ns  -> fun uu____1112  -> __addns ns
let __cases:
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term* FStar_Reflection_Types.term)
      FStar_Tactics_Effect.__tac
  = Obj.magic (fun uu____1127  -> failwith "Not yet implemented:__cases")
let cases:
  FStar_Reflection_Types.term ->
    Prims.unit ->
      (FStar_Reflection_Types.term* FStar_Reflection_Types.term)
        FStar_Tactics_Effect.__tac
  = fun t  -> fun uu____1145  -> __cases t