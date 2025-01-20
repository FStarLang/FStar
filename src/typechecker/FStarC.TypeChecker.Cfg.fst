module FStarC.TypeChecker.Cfg

open FStar open FStarC
open FStar.Char
open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.String
open FStarC.Const
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.TypeChecker.Env

open FStarC.Class.Show

module S   = FStarC.Syntax.Syntax
module SS  = FStarC.Syntax.Subst
module BU  = FStarC.Util
module FC  = FStarC.Const
module PC  = FStarC.Parser.Const
module U   = FStarC.Syntax.Util
module I   = FStarC.Ident
module EMB = FStarC.Syntax.Embeddings
module Z   = FStarC.BigInt
module NBE = FStarC.TypeChecker.NBETerm

friend FStar.Pervasives (* to expose norm_step *)

let steps_to_string f =
  let format_opt (f:'a -> string) (o:option 'a) =
    match o with
    | None -> "None"
    | Some x -> "Some ("^ f x ^ ")"
  in
  let b = BU.string_of_bool in
  BU.format
  "{\n\
    beta = %s;\n\
    iota = %s;\n\
    zeta = %s;\n\
    zeta_full = %s;\n\
    weak = %s;\n\
    hnf  = %s;\n\
    primops = %s;\n\
    do_not_unfold_pure_lets = %s;\n\
    unfold_until = %s;\n\
    unfold_only = %s;\n\
    unfold_once = %s;\n\
    unfold_fully = %s;\n\
    unfold_attr = %s;\n\
    unfold_qual = %s;\n\
    unfold_namespace = %s;\n\
    dont_unfold_attr = %s;\n\
    pure_subterms_within_computations = %s;\n\
    simplify = %s;\n\
    erase_universes = %s;\n\
    allow_unbound_universes = %s;\n\
    reify_ = %s;\n\
    compress_uvars = %s;\n\
    no_full_norm = %s;\n\
    check_no_uvars = %s;\n\
    unmeta = %s;\n\
    unascribe = %s;\n\
    in_full_norm_request = %s;\n\
    weakly_reduce_scrutinee = %s;\n\
    for_extraction = %s;\n\
    unrefine = %s;\n\
    default_univs_to_zero = %s;\n\
    tactics = %s;\n\
  }"
  [ f.beta |> show;
    f.iota |> show;
    f.zeta |> show;
    f.zeta_full |> show;
    f.weak |> show;
    f.hnf  |> show;
    f.primops |> show;
    f.do_not_unfold_pure_lets |> show;
    f.unfold_until |> show;
    f.unfold_only |> show;
    f.unfold_once |> show;
    f.unfold_fully |> show;
    f.unfold_attr |> show;
    f.unfold_qual |> show;
    f.unfold_namespace |> show;
    f.dont_unfold_attr |> show;
    f.pure_subterms_within_computations |> show;
    f.simplify |> show;
    f.erase_universes |> show;
    f.allow_unbound_universes |> show;
    f.reify_ |> show;
    f.compress_uvars |> show;
    f.no_full_norm |> show;
    f.check_no_uvars |> show;
    f.unmeta |> show;
    f.unascribe |> show;
    f.in_full_norm_request |> show;
    f.weakly_reduce_scrutinee |> show;
    f.for_extraction |> show;
    f.unrefine |> show;
    f.default_univs_to_zero |> show;
    f.tactics |> show;
   ]

instance deq_fsteps : deq fsteps = {
  (=?) = (fun f1 f2 ->
            f1.beta =? f2.beta &&
            f1.iota =? f2.iota &&
            f1.zeta =? f2.zeta &&
            f1.zeta_full =? f2.zeta_full &&
            f1.weak =? f2.weak &&
            f1.hnf =? f2.hnf &&
            f1.primops =? f2.primops &&
            f1.do_not_unfold_pure_lets =? f2.do_not_unfold_pure_lets &&
            f1.unfold_until =? f2.unfold_until &&
            f1.unfold_only =? f2.unfold_only &&
            f1.unfold_fully =? f2.unfold_fully &&
            f1.unfold_attr =? f2.unfold_attr &&
            f1.unfold_qual =? f2.unfold_qual &&
            f1.unfold_namespace =? f2.unfold_namespace &&
            f1.dont_unfold_attr =? f2.dont_unfold_attr &&
            f1.pure_subterms_within_computations =? f2.pure_subterms_within_computations &&
            f1.simplify =? f2.simplify &&
            f1.erase_universes =? f2.erase_universes &&
            f1.allow_unbound_universes =? f2.allow_unbound_universes &&
            f1.reify_ =? f2.reify_ &&
            f1.compress_uvars =? f2.compress_uvars &&
            f1.no_full_norm =? f2.no_full_norm &&
            f1.check_no_uvars =? f2.check_no_uvars &&
            f1.unmeta =? f2.unmeta &&
            f1.unascribe =? f2.unascribe &&
            f1.in_full_norm_request =? f2.in_full_norm_request &&
            f1.weakly_reduce_scrutinee =? f2.weakly_reduce_scrutinee &&
            f1.nbe_step =? f2.nbe_step &&
            f1.for_extraction =? f2.for_extraction &&
            f1.unrefine =? f2.unrefine &&
            f1.default_univs_to_zero =? f2.default_univs_to_zero &&
            f1.tactics =? f2.tactics
            );
}

let default_steps : fsteps = {
    beta = true;
    iota = true;
    zeta = true;
    zeta_full = false;
    weak = false;
    hnf  = false;
    primops = false;
    do_not_unfold_pure_lets = false;
    unfold_until = None;
    unfold_only = None;
    unfold_once = None;
    unfold_fully = None;
    unfold_attr = None;
    unfold_qual = None;
    unfold_namespace = None;
    dont_unfold_attr = None;
    pure_subterms_within_computations = false;
    simplify = false;
    erase_universes = false;
    allow_unbound_universes = false;
    reify_ = false;
    compress_uvars = false;
    no_full_norm = false;
    check_no_uvars = false;
    unmeta = false;
    unascribe = false;
    in_full_norm_request = false;
    weakly_reduce_scrutinee = true;
    nbe_step = false;
    for_extraction = false;
    unrefine = false;
    default_univs_to_zero = false;
    tactics = false;
}

let fstep_add_one s fs =
    match s with
    | Beta -> { fs with beta = true }
    | Iota -> { fs with iota = true }
    | Zeta -> { fs with zeta = true }
    | ZetaFull -> { fs with zeta_full = true }
    | Exclude Beta -> { fs with beta = false }
    | Exclude Iota -> { fs with iota = false }
    | Exclude Zeta -> { fs with zeta = false }
    | Exclude _ -> failwith "Bad exclude"
    | Weak -> { fs with weak = true }
    | HNF -> { fs with hnf = true }
    | Primops -> { fs with primops = true }
    | Eager_unfolding -> fs // eager_unfolding is not a step
    | Inlining -> fs // not a step // ZP : Adding qualification because of name clash
    | DoNotUnfoldPureLets ->  { fs with do_not_unfold_pure_lets = true }
    | UnfoldUntil d -> { fs with unfold_until = Some d }
    | UnfoldOnly  lids -> { fs with unfold_only  = Some lids }
    | UnfoldOnce  lids -> { fs with unfold_once  = Some lids }
    | UnfoldFully lids -> { fs with unfold_fully = Some lids }
    | UnfoldAttr  lids -> { fs with unfold_attr  = Some lids }
    | UnfoldQual  strs ->
      let fs = { fs with unfold_qual  = Some strs } in
      if List.contains "pure_subterms_within_computations" strs
      then {fs with pure_subterms_within_computations = true}
      else fs
    | UnfoldNamespace strs ->
     { fs with unfold_namespace =
         Some (List.map (fun s -> (Ident.path_of_text s, true)) strs, false) }
    | DontUnfoldAttr lids -> { fs with dont_unfold_attr = Some lids }
    | PureSubtermsWithinComputations ->  { fs with pure_subterms_within_computations = true }
    | Simplify ->  { fs with simplify = true }
    | EraseUniverses ->  { fs with erase_universes = true }
    | AllowUnboundUniverses ->  { fs with allow_unbound_universes = true }
    | Reify ->  { fs with reify_ = true }
    | CompressUvars ->  { fs with compress_uvars = true }
    | NoFullNorm ->  { fs with no_full_norm = true }
    | CheckNoUvars ->  { fs with check_no_uvars = true }
    | Unmeta ->  { fs with unmeta = true }
    | Unascribe ->  { fs with unascribe = true }
    | NBE -> {fs with nbe_step = true }
    | ForExtraction -> {fs with for_extraction = true }
    | Unrefine -> {fs with unrefine = true }
    | NormDebug -> fs // handled above, affects only dbg flags
    | DefaultUnivsToZero -> {fs with default_univs_to_zero = true}
    | Tactics -> { fs with tactics = true }

let to_fsteps (s : list step) : fsteps =
    List.fold_right fstep_add_one s default_steps

let no_debug_switches = {
    gen              = false;
    top              = false;
    cfg              = false;
    primop           = false;
    unfolding        = false;
    b380             = false;
    wpe              = false;
    norm_delayed     = false;
    print_normalized = false;
    debug_nbe        = false;
    erase_erasable_args = false;
}

(* Primitive step sets. They are represented as a persistent string map *)
type prim_step_set = BU.psmap primitive_step

let empty_prim_steps () : prim_step_set =
    BU.psmap_empty ()

let add_step (s : primitive_step) (ss : prim_step_set) =
    BU.psmap_add ss (I.string_of_lid s.name) s

let merge_steps (s1 : prim_step_set) (s2 : prim_step_set) : prim_step_set =
    BU.psmap_merge s1 s2

let add_steps (m : prim_step_set) (l : list primitive_step) : prim_step_set =
    List.fold_right add_step l m

let prim_from_list (l : list primitive_step) : prim_step_set =
    add_steps (empty_prim_steps ()) l
(* / Primitive step sets *)

(* Turn the lists into psmap sets, for efficiency of lookup *)
let built_in_primitive_steps = prim_from_list built_in_primitive_steps_list
let env_dependent_ops env = prim_from_list (env_dependent_ops env)
let simplification_steps env = prim_from_list (simplification_ops_list env)

instance showable_cfg : showable cfg = {
  show = (fun cfg ->
             String.concat "\n"
                 ["{";
                 BU.format1 "  steps = %s;" (steps_to_string cfg.steps);
                 BU.format1 "  delta_level = %s;" (show cfg.delta_level);
                 "}" ]);
}

let cfg_env cfg = cfg.tcenv

let find_prim_step cfg fv =
    BU.psmap_try_find cfg.primitive_steps (I.string_of_lid fv.fv_name.v)

let is_prim_step cfg fv =
    BU.is_some (BU.psmap_try_find cfg.primitive_steps (I.string_of_lid fv.fv_name.v))

let log cfg f =
    if cfg.debug.gen then f () else ()

let log_top cfg f =
    if cfg.debug.top then f () else ()

let log_cfg cfg f =
    if cfg.debug.cfg then f () else ()

let log_primops cfg f =
    if cfg.debug.primop then f () else ()

let dbg_unfolding = Debug.get_toggle "Unfolding"
let log_unfolding cfg f =
  if !dbg_unfolding then f () else ()

let log_nbe cfg f =
    if cfg.debug.debug_nbe then f ()

(* Profiling the time each different primitive step consumes *)
let primop_time_map : BU.smap int = BU.smap_create 50

let primop_time_reset () =
    BU.smap_clear primop_time_map

let primop_time_count (nm : string) (ns : int) : unit =
    match BU.smap_try_find primop_time_map nm with
    | None     -> BU.smap_add primop_time_map nm ns
    | Some ns0 -> BU.smap_add primop_time_map nm (ns0 + ns)

let fixto n s =
    if String.length s < n
    then (make (n - String.length s) ' ') ^ s
    else s

let primop_time_report () : string =
    let pairs = BU.smap_fold primop_time_map (fun nm ns rest -> (nm, ns)::rest) [] in
    let pairs = BU.sort_with (fun (_, t1) (_, t2) -> t1 - t2) pairs in
    List.fold_right (fun (nm, ns) rest -> (BU.format2 "%sms --- %s\n" (fixto 10 (BU.string_of_int (ns / 1000000))) nm) ^ rest) pairs ""

let extendable_primops_dirty : ref bool = BU.mk_ref true

type register_prim_step_t = primitive_step -> unit
type retrieve_prim_step_t = unit -> prim_step_set
let mk_extendable_primop_set ()
  : register_prim_step_t
  & retrieve_prim_step_t =
  let steps = BU.mk_ref (empty_prim_steps ()) in
  let register (p:primitive_step) =
      extendable_primops_dirty := true;
      steps := add_step p !steps
  in
  let retrieve () = !steps
  in
  register, retrieve

let plugins = mk_extendable_primop_set ()
let extra_steps = mk_extendable_primop_set ()

let register_plugin (p:primitive_step) = fst plugins p
let retrieve_plugins () =
    if Options.no_plugins ()
    then empty_prim_steps ()
    else snd plugins ()

let register_extra_step  p  = fst extra_steps p
let retrieve_extra_steps () = snd extra_steps ()

let list_plugins () : list primitive_step =
    FStarC.Common.psmap_values (retrieve_plugins ())

let list_extra_steps () : list primitive_step =
    FStarC.Common.psmap_values (retrieve_extra_steps ())

let cached_steps : unit -> prim_step_set =
    let memo : ref prim_step_set = BU.mk_ref (empty_prim_steps ()) in
    fun () ->
      if !extendable_primops_dirty
      then
        let steps =
          merge_steps built_in_primitive_steps
            (merge_steps (retrieve_plugins ())
                (retrieve_extra_steps ()))
        in
        memo := steps;
        extendable_primops_dirty := false;
        steps
      else
      !memo

let add_nbe s = // ZP : Turns nbe flag on, to be used as the default norm strategy
    if Options.use_nbe ()
    then { s with nbe_step = true }
    else s

let dbg_Norm = Debug.get_toggle "Norm"
let dbg_NormTop = Debug.get_toggle "NormTop"
let dbg_NormCfg = Debug.get_toggle "NormCfg"
let dbg_Primops = Debug.get_toggle "Primops"
let dbg_Unfolding = Debug.get_toggle "Unfolding"
let dbg_380 = Debug.get_toggle "380"
let dbg_WPE = Debug.get_toggle "WPE"
let dbg_NormDelayed = Debug.get_toggle "NormDelayed"
let dbg_print_normalized = Debug.get_toggle "print_normalized_terms"
let dbg_NBE = Debug.get_toggle "NBE"
let dbg_UNSOUND_EraseErasableArgs = Debug.get_toggle "UNSOUND_EraseErasableArgs"

let config' psteps s e =
    let d = s |> List.collect (function
        | UnfoldUntil k -> [Env.Unfold k]
        | Eager_unfolding -> [Env.Eager_unfolding_only]
        | UnfoldQual l when List.contains "unfold" l ->
          [Env.Eager_unfolding_only]
        | Inlining -> [Env.InliningDelta]
        | UnfoldQual l when List.contains "inline_for_extraction" l ->
          [Env.InliningDelta]
        | _ -> []) |> List.unique in
    let d = match d with
        | [] -> [Env.NoDelta]
        | _ -> d in
    let steps = to_fsteps s |> add_nbe in
    let psteps = add_steps (merge_steps (env_dependent_ops e) (cached_steps ())) psteps in
    let dbg_flag = List.contains NormDebug s in
    {
      tcenv = e;
      debug = {
        gen = !dbg_Norm || dbg_flag;
        top = !dbg_NormTop || dbg_flag;
        cfg = !dbg_NormCfg;
        primop = !dbg_Primops;
        unfolding = !dbg_Unfolding;
        b380 = !dbg_380;
        wpe = !dbg_WPE;
        norm_delayed = !dbg_NormDelayed;
        print_normalized = !dbg_print_normalized;
        debug_nbe = !dbg_NBE;
        erase_erasable_args = (
         if !dbg_UNSOUND_EraseErasableArgs then
           Errors.log_issue e Errors.Warning_WarnOnUse
             "The 'UNSOUND_EraseErasableArgs' setting is for debugging only; it is not sound";
         !dbg_UNSOUND_EraseErasableArgs);
      };
      steps = steps;
      delta_level = d;
      primitive_steps = psteps;
      strong = false;
      memoize_lazy = true;
      normalize_pure_lets = (not steps.pure_subterms_within_computations) || Options.normalize_pure_terms_for_extraction();
      reifying = false;
      compat_memo_ignore_cfg = Options.Ext.get "compat:normalizer_memo_ignore_cfg" <> "";
   }

let config s e = config' [] s e

let should_reduce_local_let cfg lb =
  if cfg.steps.do_not_unfold_pure_lets
  then false //we're not allowed to do any local delta steps
  else if cfg.steps.pure_subterms_within_computations &&
          U.has_attribute lb.lbattrs PC.inline_let_attr
  then true //1. we're extracting, and it's marked @inline_let
  else
    let n = Env.norm_eff_name cfg.tcenv lb.lbeff in
    if U.is_pure_effect n &&
       (cfg.normalize_pure_lets
        || U.has_attribute lb.lbattrs PC.inline_let_attr)
    then true //Or, 2. it's pure and we either not extracting, or it's marked @inline_let
    else U.is_ghost_effect n && //Or, 3. it's ghost and we're not extracting
         not (cfg.steps.pure_subterms_within_computations)

let translate_norm_step = function
    | Pervasives.Zeta ->    [Zeta]
    | Pervasives.ZetaFull -> [ZetaFull]
    | Pervasives.Iota ->    [Iota]
    | Pervasives.Delta ->   [UnfoldUntil delta_constant]
    | Pervasives.Simpl ->   [Simplify]
    | Pervasives.Weak ->    [Weak]
    | Pervasives.HNF  ->    [HNF]
    | Pervasives.Primops -> [Primops]
    | Pervasives.Reify ->   [Reify]
    | Pervasives.NormDebug -> [NormDebug]
    | Pervasives.UnfoldOnly names ->
        [UnfoldUntil delta_constant; UnfoldOnly (List.map I.lid_of_str names)]
    | Pervasives.UnfoldOnce names ->
        [UnfoldUntil delta_constant; UnfoldOnce (List.map I.lid_of_str names)]
    | Pervasives.UnfoldFully names ->
        [UnfoldUntil delta_constant; UnfoldFully (List.map I.lid_of_str names)]
    | Pervasives.UnfoldAttr names ->
        [UnfoldUntil delta_constant; UnfoldAttr (List.map I.lid_of_str names)]
    | Pervasives.UnfoldQual names ->
        [UnfoldUntil delta_constant; UnfoldQual names]
    | Pervasives.UnfoldNamespace names ->
        [UnfoldUntil delta_constant; UnfoldNamespace names]
    | Pervasives.Unascribe -> [Unascribe]
    | Pervasives.NBE -> [NBE]
    | Pervasives.Unmeta -> [Unmeta]

let translate_norm_steps s =
    let s = List.concatMap translate_norm_step s in
    let add_exclude s z = if BU.for_some ((=?) z) s then s else Exclude z :: s in
    let s = Beta::s in
    let s = add_exclude s Zeta in
    let s = add_exclude s Iota in
    s
