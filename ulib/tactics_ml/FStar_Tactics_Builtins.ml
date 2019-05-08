open Prims
open FStar_Pervasives_Native
open FStar_Pervasives
open FStar_Tactics_Result
open FStar_Tactics_Types
open FStar_Tactics_Effect
module N = FStar_TypeChecker_Normalize
module E = FStar_Tactics_Effect
module B = FStar_Tactics_Basic
module RT = FStar_Reflection_Types
module RD = FStar_Reflection_Data
module EMB = FStar_Syntax_Embeddings

let interpret_tac (t: 'a B.tac) (ps: proofstate): 'a __result =
  B.run t ps

let uninterpret_tac (t: 'a __tac) (ps: proofstate): 'a __result =
  t ps

let tr_repr_steps =
    let tr1 = function
              | Simpl         -> EMB.Simpl
              | Weak          -> EMB.Weak
              | HNF           -> EMB.HNF
              | Primops       -> EMB.Primops
              | Delta         -> EMB.Delta
              | Zeta          -> EMB.Zeta
              | Iota          -> EMB.Iota
              | NBE           -> EMB.NBE
              | Reify         -> EMB.Reify
              | UnfoldOnly  ss -> EMB.UnfoldOnly ss
              | UnfoldFully ss -> EMB.UnfoldFully ss
              | UnfoldAttr  ss -> EMB.UnfoldAttr  ss
    in List.map tr1

let to_tac_0 (t: 'a __tac): 'a B.tac =
  (fun (ps: proofstate) ->
    uninterpret_tac t ps) |> B.mk_tac

let to_tac_1 (t: 'b -> 'a __tac): 'b -> 'a B.tac = fun x ->
  (fun (ps: proofstate) ->
    uninterpret_tac (t x) ps) |> B.mk_tac

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

(* Pointing to the internal primitives *)
let get                     = from_tac_1 (fun () -> B.get) (* silly.. *)
let set_goals               = from_tac_1 B.set_goals
let set_smt_goals           = from_tac_1 B.set_smt_goals
let top_env                 = from_tac_1 B.top_env
let fresh                   = from_tac_1 B.fresh
let refine_intro            = from_tac_1 B.refine_intro
let tc                      = from_tac_1 B.tc
let tcc                     = from_tac_1 B.tcc
let unshelve                = from_tac_1 B.unshelve
let unquote                 = fun t -> failwith "Sorry, unquote does not work in compiled tactics"
let trivial                 = from_tac_1 B.trivial
let norm                    = fun s ->   from_tac_1 B.norm (tr_repr_steps s) (* TODO: somehow avoid translating steps? *)
let norm_term_env           = fun e s -> from_tac_3 B.norm_term_env e (tr_repr_steps s)
let norm_binder_type        = fun s ->   from_tac_2 B.norm_binder_type (tr_repr_steps s)
let intro                   = from_tac_1 B.intro
let intro_rec               = from_tac_1 B.intro_rec
let rename_to               = from_tac_2 B.rename_to
let revert                  = from_tac_1 B.revert
let binder_retype           = from_tac_1 B.binder_retype
let clear_top               = from_tac_1 B.clear_top
let clear                   = from_tac_1 B.clear
let rewrite                 = from_tac_1 B.rewrite
let t_exact                 = from_tac_3 B.t_exact
let t_apply                 = from_tac_2 B.t_apply
let apply_lemma             = from_tac_1 B.apply_lemma
let print                   = from_tac_1 B.print
let debugging               = from_tac_1 B.debugging
let dump                    = from_tac_1 B.print_proof_state
let trefl                   = from_tac_1 B.trefl
let dup                     = from_tac_1 B.dup
let prune                   = from_tac_1 B.prune
let addns                   = from_tac_1 B.addns
let t_destruct              = from_tac_1 B.t_destruct
let set_options             = from_tac_1 B.set_options
let uvar_env                = from_tac_2 B.uvar_env
let unify_env               = from_tac_3 B.unify_env
let launch_process          = from_tac_3 B.launch_process
let fresh_bv_named          = from_tac_2 B.fresh_bv_named
let change                  = from_tac_1 B.change
let get_guard_policy        = from_tac_1 B.get_guard_policy
let set_guard_policy        = from_tac_1 B.set_guard_policy
let lax_on                  = from_tac_1 B.lax_on
let tadmit_t                = from_tac_1 B.tadmit_t
let join                    = from_tac_1 B.join
let inspect                 = from_tac_1 B.inspect
let pack                    = from_tac_1 B.pack

(* sigh *)
let fix_either (s : ('a, 'b) FStar_Util.either) : ('a, 'b) FStar_Pervasives.either =
    match s with
    | FStar_Util.Inl a -> FStar_Pervasives.Inl a
    | FStar_Util.Inr b -> FStar_Pervasives.Inr b

(* SIGH *)
let fmap f r =
    match r with
    | Success (a, ps) -> Success (f a, ps)
    | Failed (msg, ps) -> Failed (msg, ps)

(* Those that need some translations. Maybe we can do this somewhere else
 * or automatically, but keep it for now *)
let catch (t: unit -> 'a __tac): ((exn, 'a) FStar_Pervasives.either) __tac =
        fun ps -> fmap fix_either (from_tac_1 B.catch (to_tac_0 (t ())) ps)
let recover (t: unit -> 'a __tac): ((exn, 'a) FStar_Pervasives.either) __tac =
        fun ps -> fmap fix_either (from_tac_1 B.recover (to_tac_0 (t ())) ps)

let t_pointwise (d : direction) (t: unit -> unit __tac): unit __tac = from_tac_2 B.pointwise d (to_tac_0 (t ()))

let topdown_rewrite (t1 : RT.term -> (bool * int) __tac) (t2 : unit -> unit __tac) : unit __tac =
        from_tac_2 B.topdown_rewrite (to_tac_1 t1) (to_tac_0 (t2 ()))
