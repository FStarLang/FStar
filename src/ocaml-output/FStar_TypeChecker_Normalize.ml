open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
  | Exclude of step 
  | Weak 
  | HNF 
  | Primops 
  | Eager_unfolding 
  | Inlining 
  | NoDeltaSteps 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | PureSubtermsWithinComputations 
  | Simplify 
  | EraseUniverses 
  | AllowUnboundUniverses 
  | Reify 
  | CompressUvars 
  | NoFullNorm 
  | CheckNoUvars 
  | Unmeta 
  | Unascribe [@@deriving show]
let (uu___is_Beta : step -> Prims.bool) =
  fun projectee -> match projectee with | Beta -> true | uu____22 -> false
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____26 -> false
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____30 -> false
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee -> match projectee with | Exclude _0 -> _0
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____46 -> false
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____50 -> false
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee -> match projectee with | Primops -> true | uu____54 -> false
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding -> true | uu____58 -> false
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Inlining -> true | uu____62 -> false
let (uu___is_NoDeltaSteps : step -> Prims.bool) =
  fun projectee ->
    match projectee with | NoDeltaSteps -> true | uu____66 -> false
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldUntil _0 -> true | uu____71 -> false
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee -> match projectee with | UnfoldUntil _0 -> _0
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____85 -> false
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____103 -> false
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldTac -> true | uu____114 -> false
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | PureSubtermsWithinComputations -> true
    | uu____118 -> false
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Simplify -> true | uu____122 -> false
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | EraseUniverses -> true | uu____126 -> false
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | AllowUnboundUniverses -> true | uu____130 -> false
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu____134 -> false
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CompressUvars -> true | uu____138 -> false
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee ->
    match projectee with | NoFullNorm -> true | uu____142 -> false
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CheckNoUvars -> true | uu____146 -> false
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Unmeta -> true | uu____150 -> false
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Unascribe -> true | uu____154 -> false
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____162 'Auu____163 .
    ('Auu____162 -> 'Auu____163) ->
      'Auu____163 ->
        'Auu____162 FStar_Pervasives_Native.option -> 'Auu____163
  =
  fun f ->
    fun d ->
      fun uu___77_180 ->
        match uu___77_180 with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None -> d
type fsteps =
  {
  beta: Prims.bool ;
  iota: Prims.bool ;
  zeta: Prims.bool ;
  weak: Prims.bool ;
  hnf: Prims.bool ;
  primops: Prims.bool ;
  no_delta_steps: Prims.bool ;
  unfold_until:
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option ;
  unfold_only: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_attr:
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option ;
  unfold_tac: Prims.bool ;
  pure_subterms_within_computations: Prims.bool ;
  simplify: Prims.bool ;
  erase_universes: Prims.bool ;
  allow_unbound_universes: Prims.bool ;
  reify_: Prims.bool ;
  compress_uvars: Prims.bool ;
  no_full_norm: Prims.bool ;
  check_no_uvars: Prims.bool ;
  unmeta: Prims.bool ;
  unascribe: Prims.bool }[@@deriving show]
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__beta
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__iota
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__zeta
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__weak
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__hnf
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__primops
let (__proj__Mkfsteps__item__no_delta_steps : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__no_delta_steps
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_until
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_only
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_attr
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_tac
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} ->
        __fname__pure_subterms_within_computations
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__simplify
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__erase_universes
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__allow_unbound_universes
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__reify_
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__compress_uvars
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__no_full_norm
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__check_no_uvars
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unmeta
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unascribe
let (default_steps : fsteps) =
  {
    beta = true;
    iota = true;
    zeta = true;
    weak = false;
    hnf = false;
    primops = false;
    no_delta_steps = false;
    unfold_until = FStar_Pervasives_Native.None;
    unfold_only = FStar_Pervasives_Native.None;
    unfold_attr = FStar_Pervasives_Native.None;
    unfold_tac = false;
    pure_subterms_within_computations = false;
    simplify = false;
    erase_universes = false;
    allow_unbound_universes = false;
    reify_ = false;
    compress_uvars = false;
    no_full_norm = false;
    check_no_uvars = false;
    unmeta = false;
    unascribe = false
  }
let (fstep_add_one : step -> fsteps -> fsteps) =
  fun s ->
    fun fs ->
      let add_opt x uu___78_1038 =
        match uu___78_1038 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs) in
      match s with
      | Beta ->
          let uu___96_1058 = fs in
          {
            beta = true;
            iota = (uu___96_1058.iota);
            zeta = (uu___96_1058.zeta);
            weak = (uu___96_1058.weak);
            hnf = (uu___96_1058.hnf);
            primops = (uu___96_1058.primops);
            no_delta_steps = (uu___96_1058.no_delta_steps);
            unfold_until = (uu___96_1058.unfold_until);
            unfold_only = (uu___96_1058.unfold_only);
            unfold_attr = (uu___96_1058.unfold_attr);
            unfold_tac = (uu___96_1058.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1058.pure_subterms_within_computations);
            simplify = (uu___96_1058.simplify);
            erase_universes = (uu___96_1058.erase_universes);
            allow_unbound_universes = (uu___96_1058.allow_unbound_universes);
            reify_ = (uu___96_1058.reify_);
            compress_uvars = (uu___96_1058.compress_uvars);
            no_full_norm = (uu___96_1058.no_full_norm);
            check_no_uvars = (uu___96_1058.check_no_uvars);
            unmeta = (uu___96_1058.unmeta);
            unascribe = (uu___96_1058.unascribe)
          }
      | Iota ->
          let uu___97_1059 = fs in
          {
            beta = (uu___97_1059.beta);
            iota = true;
            zeta = (uu___97_1059.zeta);
            weak = (uu___97_1059.weak);
            hnf = (uu___97_1059.hnf);
            primops = (uu___97_1059.primops);
            no_delta_steps = (uu___97_1059.no_delta_steps);
            unfold_until = (uu___97_1059.unfold_until);
            unfold_only = (uu___97_1059.unfold_only);
            unfold_attr = (uu___97_1059.unfold_attr);
            unfold_tac = (uu___97_1059.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1059.pure_subterms_within_computations);
            simplify = (uu___97_1059.simplify);
            erase_universes = (uu___97_1059.erase_universes);
            allow_unbound_universes = (uu___97_1059.allow_unbound_universes);
            reify_ = (uu___97_1059.reify_);
            compress_uvars = (uu___97_1059.compress_uvars);
            no_full_norm = (uu___97_1059.no_full_norm);
            check_no_uvars = (uu___97_1059.check_no_uvars);
            unmeta = (uu___97_1059.unmeta);
            unascribe = (uu___97_1059.unascribe)
          }
      | Zeta ->
          let uu___98_1060 = fs in
          {
            beta = (uu___98_1060.beta);
            iota = (uu___98_1060.iota);
            zeta = true;
            weak = (uu___98_1060.weak);
            hnf = (uu___98_1060.hnf);
            primops = (uu___98_1060.primops);
            no_delta_steps = (uu___98_1060.no_delta_steps);
            unfold_until = (uu___98_1060.unfold_until);
            unfold_only = (uu___98_1060.unfold_only);
            unfold_attr = (uu___98_1060.unfold_attr);
            unfold_tac = (uu___98_1060.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1060.pure_subterms_within_computations);
            simplify = (uu___98_1060.simplify);
            erase_universes = (uu___98_1060.erase_universes);
            allow_unbound_universes = (uu___98_1060.allow_unbound_universes);
            reify_ = (uu___98_1060.reify_);
            compress_uvars = (uu___98_1060.compress_uvars);
            no_full_norm = (uu___98_1060.no_full_norm);
            check_no_uvars = (uu___98_1060.check_no_uvars);
            unmeta = (uu___98_1060.unmeta);
            unascribe = (uu___98_1060.unascribe)
          }
      | Exclude (Beta) ->
          let uu___99_1061 = fs in
          {
            beta = false;
            iota = (uu___99_1061.iota);
            zeta = (uu___99_1061.zeta);
            weak = (uu___99_1061.weak);
            hnf = (uu___99_1061.hnf);
            primops = (uu___99_1061.primops);
            no_delta_steps = (uu___99_1061.no_delta_steps);
            unfold_until = (uu___99_1061.unfold_until);
            unfold_only = (uu___99_1061.unfold_only);
            unfold_attr = (uu___99_1061.unfold_attr);
            unfold_tac = (uu___99_1061.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1061.pure_subterms_within_computations);
            simplify = (uu___99_1061.simplify);
            erase_universes = (uu___99_1061.erase_universes);
            allow_unbound_universes = (uu___99_1061.allow_unbound_universes);
            reify_ = (uu___99_1061.reify_);
            compress_uvars = (uu___99_1061.compress_uvars);
            no_full_norm = (uu___99_1061.no_full_norm);
            check_no_uvars = (uu___99_1061.check_no_uvars);
            unmeta = (uu___99_1061.unmeta);
            unascribe = (uu___99_1061.unascribe)
          }
      | Exclude (Iota) ->
          let uu___100_1062 = fs in
          {
            beta = (uu___100_1062.beta);
            iota = false;
            zeta = (uu___100_1062.zeta);
            weak = (uu___100_1062.weak);
            hnf = (uu___100_1062.hnf);
            primops = (uu___100_1062.primops);
            no_delta_steps = (uu___100_1062.no_delta_steps);
            unfold_until = (uu___100_1062.unfold_until);
            unfold_only = (uu___100_1062.unfold_only);
            unfold_attr = (uu___100_1062.unfold_attr);
            unfold_tac = (uu___100_1062.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1062.pure_subterms_within_computations);
            simplify = (uu___100_1062.simplify);
            erase_universes = (uu___100_1062.erase_universes);
            allow_unbound_universes = (uu___100_1062.allow_unbound_universes);
            reify_ = (uu___100_1062.reify_);
            compress_uvars = (uu___100_1062.compress_uvars);
            no_full_norm = (uu___100_1062.no_full_norm);
            check_no_uvars = (uu___100_1062.check_no_uvars);
            unmeta = (uu___100_1062.unmeta);
            unascribe = (uu___100_1062.unascribe)
          }
      | Exclude (Zeta) ->
          let uu___101_1063 = fs in
          {
            beta = (uu___101_1063.beta);
            iota = (uu___101_1063.iota);
            zeta = false;
            weak = (uu___101_1063.weak);
            hnf = (uu___101_1063.hnf);
            primops = (uu___101_1063.primops);
            no_delta_steps = (uu___101_1063.no_delta_steps);
            unfold_until = (uu___101_1063.unfold_until);
            unfold_only = (uu___101_1063.unfold_only);
            unfold_attr = (uu___101_1063.unfold_attr);
            unfold_tac = (uu___101_1063.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1063.pure_subterms_within_computations);
            simplify = (uu___101_1063.simplify);
            erase_universes = (uu___101_1063.erase_universes);
            allow_unbound_universes = (uu___101_1063.allow_unbound_universes);
            reify_ = (uu___101_1063.reify_);
            compress_uvars = (uu___101_1063.compress_uvars);
            no_full_norm = (uu___101_1063.no_full_norm);
            check_no_uvars = (uu___101_1063.check_no_uvars);
            unmeta = (uu___101_1063.unmeta);
            unascribe = (uu___101_1063.unascribe)
          }
      | Exclude uu____1064 -> failwith "Bad exclude"
      | Weak ->
          let uu___102_1065 = fs in
          {
            beta = (uu___102_1065.beta);
            iota = (uu___102_1065.iota);
            zeta = (uu___102_1065.zeta);
            weak = true;
            hnf = (uu___102_1065.hnf);
            primops = (uu___102_1065.primops);
            no_delta_steps = (uu___102_1065.no_delta_steps);
            unfold_until = (uu___102_1065.unfold_until);
            unfold_only = (uu___102_1065.unfold_only);
            unfold_attr = (uu___102_1065.unfold_attr);
            unfold_tac = (uu___102_1065.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1065.pure_subterms_within_computations);
            simplify = (uu___102_1065.simplify);
            erase_universes = (uu___102_1065.erase_universes);
            allow_unbound_universes = (uu___102_1065.allow_unbound_universes);
            reify_ = (uu___102_1065.reify_);
            compress_uvars = (uu___102_1065.compress_uvars);
            no_full_norm = (uu___102_1065.no_full_norm);
            check_no_uvars = (uu___102_1065.check_no_uvars);
            unmeta = (uu___102_1065.unmeta);
            unascribe = (uu___102_1065.unascribe)
          }
      | HNF ->
          let uu___103_1066 = fs in
          {
            beta = (uu___103_1066.beta);
            iota = (uu___103_1066.iota);
            zeta = (uu___103_1066.zeta);
            weak = (uu___103_1066.weak);
            hnf = true;
            primops = (uu___103_1066.primops);
            no_delta_steps = (uu___103_1066.no_delta_steps);
            unfold_until = (uu___103_1066.unfold_until);
            unfold_only = (uu___103_1066.unfold_only);
            unfold_attr = (uu___103_1066.unfold_attr);
            unfold_tac = (uu___103_1066.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1066.pure_subterms_within_computations);
            simplify = (uu___103_1066.simplify);
            erase_universes = (uu___103_1066.erase_universes);
            allow_unbound_universes = (uu___103_1066.allow_unbound_universes);
            reify_ = (uu___103_1066.reify_);
            compress_uvars = (uu___103_1066.compress_uvars);
            no_full_norm = (uu___103_1066.no_full_norm);
            check_no_uvars = (uu___103_1066.check_no_uvars);
            unmeta = (uu___103_1066.unmeta);
            unascribe = (uu___103_1066.unascribe)
          }
      | Primops ->
          let uu___104_1067 = fs in
          {
            beta = (uu___104_1067.beta);
            iota = (uu___104_1067.iota);
            zeta = (uu___104_1067.zeta);
            weak = (uu___104_1067.weak);
            hnf = (uu___104_1067.hnf);
            primops = true;
            no_delta_steps = (uu___104_1067.no_delta_steps);
            unfold_until = (uu___104_1067.unfold_until);
            unfold_only = (uu___104_1067.unfold_only);
            unfold_attr = (uu___104_1067.unfold_attr);
            unfold_tac = (uu___104_1067.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1067.pure_subterms_within_computations);
            simplify = (uu___104_1067.simplify);
            erase_universes = (uu___104_1067.erase_universes);
            allow_unbound_universes = (uu___104_1067.allow_unbound_universes);
            reify_ = (uu___104_1067.reify_);
            compress_uvars = (uu___104_1067.compress_uvars);
            no_full_norm = (uu___104_1067.no_full_norm);
            check_no_uvars = (uu___104_1067.check_no_uvars);
            unmeta = (uu___104_1067.unmeta);
            unascribe = (uu___104_1067.unascribe)
          }
      | Eager_unfolding -> fs
      | Inlining -> fs
      | NoDeltaSteps ->
          let uu___105_1068 = fs in
          {
            beta = (uu___105_1068.beta);
            iota = (uu___105_1068.iota);
            zeta = (uu___105_1068.zeta);
            weak = (uu___105_1068.weak);
            hnf = (uu___105_1068.hnf);
            primops = (uu___105_1068.primops);
            no_delta_steps = true;
            unfold_until = (uu___105_1068.unfold_until);
            unfold_only = (uu___105_1068.unfold_only);
            unfold_attr = (uu___105_1068.unfold_attr);
            unfold_tac = (uu___105_1068.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1068.pure_subterms_within_computations);
            simplify = (uu___105_1068.simplify);
            erase_universes = (uu___105_1068.erase_universes);
            allow_unbound_universes = (uu___105_1068.allow_unbound_universes);
            reify_ = (uu___105_1068.reify_);
            compress_uvars = (uu___105_1068.compress_uvars);
            no_full_norm = (uu___105_1068.no_full_norm);
            check_no_uvars = (uu___105_1068.check_no_uvars);
            unmeta = (uu___105_1068.unmeta);
            unascribe = (uu___105_1068.unascribe)
          }
      | UnfoldUntil d ->
          let uu___106_1070 = fs in
          {
            beta = (uu___106_1070.beta);
            iota = (uu___106_1070.iota);
            zeta = (uu___106_1070.zeta);
            weak = (uu___106_1070.weak);
            hnf = (uu___106_1070.hnf);
            primops = (uu___106_1070.primops);
            no_delta_steps = (uu___106_1070.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1070.unfold_only);
            unfold_attr = (uu___106_1070.unfold_attr);
            unfold_tac = (uu___106_1070.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1070.pure_subterms_within_computations);
            simplify = (uu___106_1070.simplify);
            erase_universes = (uu___106_1070.erase_universes);
            allow_unbound_universes = (uu___106_1070.allow_unbound_universes);
            reify_ = (uu___106_1070.reify_);
            compress_uvars = (uu___106_1070.compress_uvars);
            no_full_norm = (uu___106_1070.no_full_norm);
            check_no_uvars = (uu___106_1070.check_no_uvars);
            unmeta = (uu___106_1070.unmeta);
            unascribe = (uu___106_1070.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___107_1074 = fs in
          {
            beta = (uu___107_1074.beta);
            iota = (uu___107_1074.iota);
            zeta = (uu___107_1074.zeta);
            weak = (uu___107_1074.weak);
            hnf = (uu___107_1074.hnf);
            primops = (uu___107_1074.primops);
            no_delta_steps = (uu___107_1074.no_delta_steps);
            unfold_until = (uu___107_1074.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___107_1074.unfold_attr);
            unfold_tac = (uu___107_1074.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1074.pure_subterms_within_computations);
            simplify = (uu___107_1074.simplify);
            erase_universes = (uu___107_1074.erase_universes);
            allow_unbound_universes = (uu___107_1074.allow_unbound_universes);
            reify_ = (uu___107_1074.reify_);
            compress_uvars = (uu___107_1074.compress_uvars);
            no_full_norm = (uu___107_1074.no_full_norm);
            check_no_uvars = (uu___107_1074.check_no_uvars);
            unmeta = (uu___107_1074.unmeta);
            unascribe = (uu___107_1074.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___108_1078 = fs in
          {
            beta = (uu___108_1078.beta);
            iota = (uu___108_1078.iota);
            zeta = (uu___108_1078.zeta);
            weak = (uu___108_1078.weak);
            hnf = (uu___108_1078.hnf);
            primops = (uu___108_1078.primops);
            no_delta_steps = (uu___108_1078.no_delta_steps);
            unfold_until = (uu___108_1078.unfold_until);
            unfold_only = (uu___108_1078.unfold_only);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___108_1078.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1078.pure_subterms_within_computations);
            simplify = (uu___108_1078.simplify);
            erase_universes = (uu___108_1078.erase_universes);
            allow_unbound_universes = (uu___108_1078.allow_unbound_universes);
            reify_ = (uu___108_1078.reify_);
            compress_uvars = (uu___108_1078.compress_uvars);
            no_full_norm = (uu___108_1078.no_full_norm);
            check_no_uvars = (uu___108_1078.check_no_uvars);
            unmeta = (uu___108_1078.unmeta);
            unascribe = (uu___108_1078.unascribe)
          }
      | UnfoldTac ->
          let uu___109_1079 = fs in
          {
            beta = (uu___109_1079.beta);
            iota = (uu___109_1079.iota);
            zeta = (uu___109_1079.zeta);
            weak = (uu___109_1079.weak);
            hnf = (uu___109_1079.hnf);
            primops = (uu___109_1079.primops);
            no_delta_steps = (uu___109_1079.no_delta_steps);
            unfold_until = (uu___109_1079.unfold_until);
            unfold_only = (uu___109_1079.unfold_only);
            unfold_attr = (uu___109_1079.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___109_1079.pure_subterms_within_computations);
            simplify = (uu___109_1079.simplify);
            erase_universes = (uu___109_1079.erase_universes);
            allow_unbound_universes = (uu___109_1079.allow_unbound_universes);
            reify_ = (uu___109_1079.reify_);
            compress_uvars = (uu___109_1079.compress_uvars);
            no_full_norm = (uu___109_1079.no_full_norm);
            check_no_uvars = (uu___109_1079.check_no_uvars);
            unmeta = (uu___109_1079.unmeta);
            unascribe = (uu___109_1079.unascribe)
          }
      | PureSubtermsWithinComputations ->
          let uu___110_1080 = fs in
          {
            beta = (uu___110_1080.beta);
            iota = (uu___110_1080.iota);
            zeta = (uu___110_1080.zeta);
            weak = (uu___110_1080.weak);
            hnf = (uu___110_1080.hnf);
            primops = (uu___110_1080.primops);
            no_delta_steps = (uu___110_1080.no_delta_steps);
            unfold_until = (uu___110_1080.unfold_until);
            unfold_only = (uu___110_1080.unfold_only);
            unfold_attr = (uu___110_1080.unfold_attr);
            unfold_tac = (uu___110_1080.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___110_1080.simplify);
            erase_universes = (uu___110_1080.erase_universes);
            allow_unbound_universes = (uu___110_1080.allow_unbound_universes);
            reify_ = (uu___110_1080.reify_);
            compress_uvars = (uu___110_1080.compress_uvars);
            no_full_norm = (uu___110_1080.no_full_norm);
            check_no_uvars = (uu___110_1080.check_no_uvars);
            unmeta = (uu___110_1080.unmeta);
            unascribe = (uu___110_1080.unascribe)
          }
      | Simplify ->
          let uu___111_1081 = fs in
          {
            beta = (uu___111_1081.beta);
            iota = (uu___111_1081.iota);
            zeta = (uu___111_1081.zeta);
            weak = (uu___111_1081.weak);
            hnf = (uu___111_1081.hnf);
            primops = (uu___111_1081.primops);
            no_delta_steps = (uu___111_1081.no_delta_steps);
            unfold_until = (uu___111_1081.unfold_until);
            unfold_only = (uu___111_1081.unfold_only);
            unfold_attr = (uu___111_1081.unfold_attr);
            unfold_tac = (uu___111_1081.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1081.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___111_1081.erase_universes);
            allow_unbound_universes = (uu___111_1081.allow_unbound_universes);
            reify_ = (uu___111_1081.reify_);
            compress_uvars = (uu___111_1081.compress_uvars);
            no_full_norm = (uu___111_1081.no_full_norm);
            check_no_uvars = (uu___111_1081.check_no_uvars);
            unmeta = (uu___111_1081.unmeta);
            unascribe = (uu___111_1081.unascribe)
          }
      | EraseUniverses ->
          let uu___112_1082 = fs in
          {
            beta = (uu___112_1082.beta);
            iota = (uu___112_1082.iota);
            zeta = (uu___112_1082.zeta);
            weak = (uu___112_1082.weak);
            hnf = (uu___112_1082.hnf);
            primops = (uu___112_1082.primops);
            no_delta_steps = (uu___112_1082.no_delta_steps);
            unfold_until = (uu___112_1082.unfold_until);
            unfold_only = (uu___112_1082.unfold_only);
            unfold_attr = (uu___112_1082.unfold_attr);
            unfold_tac = (uu___112_1082.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1082.pure_subterms_within_computations);
            simplify = (uu___112_1082.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___112_1082.allow_unbound_universes);
            reify_ = (uu___112_1082.reify_);
            compress_uvars = (uu___112_1082.compress_uvars);
            no_full_norm = (uu___112_1082.no_full_norm);
            check_no_uvars = (uu___112_1082.check_no_uvars);
            unmeta = (uu___112_1082.unmeta);
            unascribe = (uu___112_1082.unascribe)
          }
      | AllowUnboundUniverses ->
          let uu___113_1083 = fs in
          {
            beta = (uu___113_1083.beta);
            iota = (uu___113_1083.iota);
            zeta = (uu___113_1083.zeta);
            weak = (uu___113_1083.weak);
            hnf = (uu___113_1083.hnf);
            primops = (uu___113_1083.primops);
            no_delta_steps = (uu___113_1083.no_delta_steps);
            unfold_until = (uu___113_1083.unfold_until);
            unfold_only = (uu___113_1083.unfold_only);
            unfold_attr = (uu___113_1083.unfold_attr);
            unfold_tac = (uu___113_1083.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1083.pure_subterms_within_computations);
            simplify = (uu___113_1083.simplify);
            erase_universes = (uu___113_1083.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___113_1083.reify_);
            compress_uvars = (uu___113_1083.compress_uvars);
            no_full_norm = (uu___113_1083.no_full_norm);
            check_no_uvars = (uu___113_1083.check_no_uvars);
            unmeta = (uu___113_1083.unmeta);
            unascribe = (uu___113_1083.unascribe)
          }
      | Reify ->
          let uu___114_1084 = fs in
          {
            beta = (uu___114_1084.beta);
            iota = (uu___114_1084.iota);
            zeta = (uu___114_1084.zeta);
            weak = (uu___114_1084.weak);
            hnf = (uu___114_1084.hnf);
            primops = (uu___114_1084.primops);
            no_delta_steps = (uu___114_1084.no_delta_steps);
            unfold_until = (uu___114_1084.unfold_until);
            unfold_only = (uu___114_1084.unfold_only);
            unfold_attr = (uu___114_1084.unfold_attr);
            unfold_tac = (uu___114_1084.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1084.pure_subterms_within_computations);
            simplify = (uu___114_1084.simplify);
            erase_universes = (uu___114_1084.erase_universes);
            allow_unbound_universes = (uu___114_1084.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___114_1084.compress_uvars);
            no_full_norm = (uu___114_1084.no_full_norm);
            check_no_uvars = (uu___114_1084.check_no_uvars);
            unmeta = (uu___114_1084.unmeta);
            unascribe = (uu___114_1084.unascribe)
          }
      | CompressUvars ->
          let uu___115_1085 = fs in
          {
            beta = (uu___115_1085.beta);
            iota = (uu___115_1085.iota);
            zeta = (uu___115_1085.zeta);
            weak = (uu___115_1085.weak);
            hnf = (uu___115_1085.hnf);
            primops = (uu___115_1085.primops);
            no_delta_steps = (uu___115_1085.no_delta_steps);
            unfold_until = (uu___115_1085.unfold_until);
            unfold_only = (uu___115_1085.unfold_only);
            unfold_attr = (uu___115_1085.unfold_attr);
            unfold_tac = (uu___115_1085.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1085.pure_subterms_within_computations);
            simplify = (uu___115_1085.simplify);
            erase_universes = (uu___115_1085.erase_universes);
            allow_unbound_universes = (uu___115_1085.allow_unbound_universes);
            reify_ = (uu___115_1085.reify_);
            compress_uvars = true;
            no_full_norm = (uu___115_1085.no_full_norm);
            check_no_uvars = (uu___115_1085.check_no_uvars);
            unmeta = (uu___115_1085.unmeta);
            unascribe = (uu___115_1085.unascribe)
          }
      | NoFullNorm ->
          let uu___116_1086 = fs in
          {
            beta = (uu___116_1086.beta);
            iota = (uu___116_1086.iota);
            zeta = (uu___116_1086.zeta);
            weak = (uu___116_1086.weak);
            hnf = (uu___116_1086.hnf);
            primops = (uu___116_1086.primops);
            no_delta_steps = (uu___116_1086.no_delta_steps);
            unfold_until = (uu___116_1086.unfold_until);
            unfold_only = (uu___116_1086.unfold_only);
            unfold_attr = (uu___116_1086.unfold_attr);
            unfold_tac = (uu___116_1086.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1086.pure_subterms_within_computations);
            simplify = (uu___116_1086.simplify);
            erase_universes = (uu___116_1086.erase_universes);
            allow_unbound_universes = (uu___116_1086.allow_unbound_universes);
            reify_ = (uu___116_1086.reify_);
            compress_uvars = (uu___116_1086.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___116_1086.check_no_uvars);
            unmeta = (uu___116_1086.unmeta);
            unascribe = (uu___116_1086.unascribe)
          }
      | CheckNoUvars ->
          let uu___117_1087 = fs in
          {
            beta = (uu___117_1087.beta);
            iota = (uu___117_1087.iota);
            zeta = (uu___117_1087.zeta);
            weak = (uu___117_1087.weak);
            hnf = (uu___117_1087.hnf);
            primops = (uu___117_1087.primops);
            no_delta_steps = (uu___117_1087.no_delta_steps);
            unfold_until = (uu___117_1087.unfold_until);
            unfold_only = (uu___117_1087.unfold_only);
            unfold_attr = (uu___117_1087.unfold_attr);
            unfold_tac = (uu___117_1087.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1087.pure_subterms_within_computations);
            simplify = (uu___117_1087.simplify);
            erase_universes = (uu___117_1087.erase_universes);
            allow_unbound_universes = (uu___117_1087.allow_unbound_universes);
            reify_ = (uu___117_1087.reify_);
            compress_uvars = (uu___117_1087.compress_uvars);
            no_full_norm = (uu___117_1087.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___117_1087.unmeta);
            unascribe = (uu___117_1087.unascribe)
          }
      | Unmeta ->
          let uu___118_1088 = fs in
          {
            beta = (uu___118_1088.beta);
            iota = (uu___118_1088.iota);
            zeta = (uu___118_1088.zeta);
            weak = (uu___118_1088.weak);
            hnf = (uu___118_1088.hnf);
            primops = (uu___118_1088.primops);
            no_delta_steps = (uu___118_1088.no_delta_steps);
            unfold_until = (uu___118_1088.unfold_until);
            unfold_only = (uu___118_1088.unfold_only);
            unfold_attr = (uu___118_1088.unfold_attr);
            unfold_tac = (uu___118_1088.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1088.pure_subterms_within_computations);
            simplify = (uu___118_1088.simplify);
            erase_universes = (uu___118_1088.erase_universes);
            allow_unbound_universes = (uu___118_1088.allow_unbound_universes);
            reify_ = (uu___118_1088.reify_);
            compress_uvars = (uu___118_1088.compress_uvars);
            no_full_norm = (uu___118_1088.no_full_norm);
            check_no_uvars = (uu___118_1088.check_no_uvars);
            unmeta = true;
            unascribe = (uu___118_1088.unascribe)
          }
      | Unascribe ->
          let uu___119_1089 = fs in
          {
            beta = (uu___119_1089.beta);
            iota = (uu___119_1089.iota);
            zeta = (uu___119_1089.zeta);
            weak = (uu___119_1089.weak);
            hnf = (uu___119_1089.hnf);
            primops = (uu___119_1089.primops);
            no_delta_steps = (uu___119_1089.no_delta_steps);
            unfold_until = (uu___119_1089.unfold_until);
            unfold_only = (uu___119_1089.unfold_only);
            unfold_attr = (uu___119_1089.unfold_attr);
            unfold_tac = (uu___119_1089.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1089.pure_subterms_within_computations);
            simplify = (uu___119_1089.simplify);
            erase_universes = (uu___119_1089.erase_universes);
            allow_unbound_universes = (uu___119_1089.allow_unbound_universes);
            reify_ = (uu___119_1089.reify_);
            compress_uvars = (uu___119_1089.compress_uvars);
            no_full_norm = (uu___119_1089.no_full_norm);
            check_no_uvars = (uu___119_1089.check_no_uvars);
            unmeta = (uu___119_1089.unmeta);
            unascribe = true
          }
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s -> FStar_List.fold_right fstep_add_one s default_steps
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t }[@@deriving show]
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
let (__proj__Mkpsc__item__psc_subst :
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1128 -> []) }
let (psc_range : psc -> FStar_Range.range) = fun psc -> psc.psc_range
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc -> psc.psc_subst ()
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  auto_reflect: Prims.int FStar_Pervasives_Native.option ;
  strong_reduction_ok: Prims.bool ;
  requires_binder_substitution: Prims.bool ;
  interpretation:
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    }[@@deriving show]
let (__proj__Mkprimitive_step__item__name :
  primitive_step -> FStar_Ident.lid) =
  fun projectee ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
let (__proj__Mkprimitive_step__item__auto_reflect :
  primitive_step -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__auto_reflect
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
let (__proj__Mkprimitive_step__item__interpretation :
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
type closure =
  | Clos of
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option, closure)
     FStar_Pervasives_Native.tuple2 Prims.list,
  FStar_Syntax_Syntax.term,
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option, closure)
     FStar_Pervasives_Native.tuple2 Prims.list,
    FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
    FStar_Syntax_Syntax.memo,
  Prims.bool) FStar_Pervasives_Native.tuple4 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy [@@deriving show]
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee ->
    match projectee with | Clos _0 -> true | uu____1371 -> false
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option, closure)
       FStar_Pervasives_Native.tuple2 Prims.list,
      FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option, closure)
         FStar_Pervasives_Native.tuple2 Prims.list,
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
        FStar_Syntax_Syntax.memo,
      Prims.bool) FStar_Pervasives_Native.tuple4)
  = fun projectee -> match projectee with | Clos _0 -> _0
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee ->
    match projectee with | Univ _0 -> true | uu____1473 -> false
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Univ _0 -> _0
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee -> match projectee with | Dummy -> true | uu____1484 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option, closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option, closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy)
let (closure_to_string : closure -> Prims.string) =
  fun uu___79_1503 ->
    match uu___79_1503 with
    | Clos (uu____1504, t, uu____1506, uu____1507) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1552 -> "Univ"
    | Dummy -> "dummy"
type debug_switches =
  {
  gen: Prims.bool ;
  primop: Prims.bool ;
  b380: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }[@@deriving show]
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__print_normalized
type cfg =
  {
  steps: fsteps ;
  tcenv: FStar_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step FStar_Util.psmap ;
  strong: Prims.bool ;
  memoize_lazy: Prims.bool ;
  normalize_pure_lets: Prims.bool }[@@deriving show]
let (__proj__Mkcfg__item__steps : cfg -> fsteps) =
  fun projectee ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__steps
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__tcenv
let (__proj__Mkcfg__item__debug : cfg -> debug_switches) =
  fun projectee ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__debug
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__delta_level
let (__proj__Mkcfg__item__primitive_steps :
  cfg -> primitive_step FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__primitive_steps
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__strong
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__memoize_lazy
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__normalize_pure_lets
let (add_steps :
  primitive_step FStar_Util.psmap ->
    primitive_step Prims.list -> primitive_step FStar_Util.psmap)
  =
  fun m ->
    fun l ->
      FStar_List.fold_right
        (fun p ->
           fun m1 ->
             let uu____1804 = FStar_Ident.text_of_lid p.name in
             FStar_Util.psmap_add m1 uu____1804 p) l m
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l ->
    let uu____1816 = FStar_Util.psmap_empty () in add_steps uu____1816 l
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun fv ->
      let uu____1827 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____1827
type branches =
  (FStar_Syntax_Syntax.pat,
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,
    FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple3 Prims.list
[@@deriving show]
type stack_elt =
  | Arg of (closure, FStar_Syntax_Syntax.aqual, FStar_Range.range)
  FStar_Pervasives_Native.tuple3 
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list, FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | MemoLazy of (env, FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo 
  | Match of (env, branches, FStar_Range.range)
  FStar_Pervasives_Native.tuple3 
  | Abs of (env, FStar_Syntax_Syntax.binders, env,
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5 
  | App of (env, FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.aqual,
  FStar_Range.range) FStar_Pervasives_Native.tuple4 
  | Meta of (FStar_Syntax_Syntax.metadata, FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | Let of (env, FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.letbinding,
  FStar_Range.range) FStar_Pervasives_Native.tuple4 
  | Cfg of cfg 
  | Debug of (FStar_Syntax_Syntax.term, FStar_Util.time)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Arg _0 -> true | uu____1969 -> false
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure, FStar_Syntax_Syntax.aqual, FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee -> match projectee with | Arg _0 -> _0
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | UnivArgs _0 -> true | uu____2005 -> false
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list, FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | UnivArgs _0 -> _0
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | MemoLazy _0 -> true | uu____2041 -> false
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env, FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee -> match projectee with | MemoLazy _0 -> _0
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Match _0 -> true | uu____2110 -> false
let (__proj__Match__item___0 :
  stack_elt ->
    (env, branches, FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Abs _0 -> true | uu____2152 -> false
let (__proj__Abs__item___0 :
  stack_elt ->
    (env, FStar_Syntax_Syntax.binders, env,
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee -> match projectee with | Abs _0 -> _0
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | App _0 -> true | uu____2208 -> false
let (__proj__App__item___0 :
  stack_elt ->
    (env, FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.aqual,
      FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee -> match projectee with | App _0 -> _0
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta _0 -> true | uu____2248 -> false
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata, FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Let _0 -> true | uu____2280 -> false
let (__proj__Let__item___0 :
  stack_elt ->
    (env, FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.letbinding,
      FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Cfg _0 -> true | uu____2316 -> false
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee -> match projectee with | Cfg _0 -> _0
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Debug _0 -> true | uu____2332 -> false
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term, FStar_Util.time)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____2357 = FStar_Syntax_Util.head_and_args' t in
    match uu____2357 with | (hd1, uu____2371) -> hd1
let mk :
  'Auu____2391 .
    'Auu____2391 ->
      FStar_Range.range -> 'Auu____2391 FStar_Syntax_Syntax.syntax
  = fun t -> fun r -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg ->
    fun r ->
      fun t ->
        if cfg.memoize_lazy
        then
          let uu____2445 = FStar_ST.op_Bang r in
          match uu____2445 with
          | FStar_Pervasives_Native.Some uu____2493 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env ->
    let uu____2547 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____2547 (FStar_String.concat "; ")
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_2554 ->
    match uu___80_2554 with
    | Arg (c, uu____2556, uu____2557) ->
        let uu____2558 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____2558
    | MemoLazy uu____2559 -> "MemoLazy"
    | Abs (uu____2566, bs, uu____2568, uu____2569, uu____2570) ->
        let uu____2575 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____2575
    | UnivArgs uu____2580 -> "UnivArgs"
    | Match uu____2587 -> "Match"
    | App (uu____2594, t, uu____2596, uu____2597) ->
        let uu____2598 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____2598
    | Meta (m, uu____2600) -> "Meta"
    | Let uu____2601 -> "Let"
    | Cfg uu____2610 -> "Cfg"
    | Debug (t, uu____2612) ->
        let uu____2613 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____2613
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s ->
    let uu____2621 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____2621 (FStar_String.concat "; ")
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg -> fun f -> if (cfg.debug).gen then f () else ()
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg -> fun f -> if (cfg.debug).primop then f () else ()
let is_empty : 'Auu____2652 . 'Auu____2652 Prims.list -> Prims.bool =
  fun uu___81_2658 ->
    match uu___81_2658 with | [] -> true | uu____2661 -> false
let lookup_bvar :
  'Auu____2668 'Auu____2669 .
    ('Auu____2668, 'Auu____2669) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2669
  =
  fun env ->
    fun x ->
      try
        let uu____2693 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____2693
      with
      | uu____2706 ->
          let uu____2707 =
            let uu____2708 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____2708 in
          failwith uu____2707
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l ->
    let uu____2714 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid in
    if uu____2714
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____2718 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid in
       if uu____2718
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____2722 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid in
          if uu____2722
          then
            FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
          else FStar_Pervasives_Native.None))
let (norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg ->
    fun env ->
      fun u ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____2748 =
            FStar_List.fold_left
              (fun uu____2774 ->
                 fun u1 ->
                   match uu____2774 with
                   | (cur_kernel, cur_max, out) ->
                       let uu____2799 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____2799 with
                        | (k_u, n1) ->
                            let uu____2814 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____2814
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____2748 with
          | (uu____2832, u1, out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2857 =
                   let uu____2858 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____2858 in
                 match uu____2857 with
                 | Univ u3 -> aux u3
                 | Dummy -> [u2]
                 | uu____2876 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2884 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2890 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2899 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2908 -> [u2]
          | FStar_Syntax_Syntax.U_unknown -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2915 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2915 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2932 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2932 with
                    | (FStar_Syntax_Syntax.U_zero, n1) ->
                        let uu____2940 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3 ->
                                  let uu____2948 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2948 with
                                  | (uu____2953, m) -> n1 <= m)) in
                        if uu____2940 then rest1 else us1
                    | uu____2958 -> us1)
               | uu____2963 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2967 = aux u3 in
              FStar_List.map (fun _0_40 -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2967 in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2971 = aux u in
           match uu____2971 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero)::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero)::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero)::us -> FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
let rec (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg ->
    fun env ->
      fun t ->
        log cfg
          (fun uu____3075 ->
             let uu____3076 = FStar_Syntax_Print.tag_of_term t in
             let uu____3077 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3076
               uu____3077);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3084 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3086 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3111 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3112 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3113 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3114 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3115 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3132 =
                      let uu____3133 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____3134 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3133 uu____3134 in
                    failwith uu____3132
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3137 =
                    let uu____3138 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____3138 in
                  mk uu____3137 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
                  let uu____3145 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3145
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3147 = lookup_bvar env x in
                  (match uu____3147 with
                   | Univ uu____3150 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy -> t1
                   | Clos (env1, t0, uu____3153, uu____3154) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1, args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
                  let uu____3266 = closures_as_binders_delayed cfg env bs in
                  (match uu____3266 with
                   | (bs1, env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____3294 =
                         let uu____3295 =
                           let uu____3312 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____3312) in
                         FStar_Syntax_Syntax.Tm_abs uu____3295 in
                       mk uu____3294 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                  let uu____3343 = closures_as_binders_delayed cfg env bs in
                  (match uu____3343 with
                   | (bs1, env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
                  let uu____3385 =
                    let uu____3396 =
                      let uu____3403 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____3403] in
                    closures_as_binders_delayed cfg env uu____3396 in
                  (match uu____3385 with
                   | (x1, env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____3421 =
                         let uu____3422 =
                           let uu____3429 =
                             let uu____3430 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____3430
                               FStar_Pervasives_Native.fst in
                           (uu____3429, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____3422 in
                       mk uu____3421 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11, (annot, tacopt), lopt)
                  ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3521 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____3521
                    | FStar_Util.Inr c ->
                        let uu____3535 = close_comp cfg env c in
                        FStar_Util.Inr uu____3535 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____3551 =
                    let uu____3552 =
                      let uu____3579 = closure_as_term_delayed cfg env t11 in
                      (uu____3579, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3552 in
                  mk uu____3551 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_quoted (t', qi) ->
                  (match qi.FStar_Syntax_Syntax.qkind with
                   | FStar_Syntax_Syntax.Quote_dynamic ->
                       let uu____3620 =
                         let uu____3621 =
                           let uu____3628 =
                             closure_as_term_delayed cfg env t' in
                           (uu____3628, qi) in
                         FStar_Syntax_Syntax.Tm_quoted uu____3621 in
                       mk uu____3620 t1.FStar_Syntax_Syntax.pos
                   | FStar_Syntax_Syntax.Quote_static ->
                       let qi1 =
                         FStar_Syntax_Syntax.on_antiquoted
                           (closure_as_term_delayed cfg env) qi in
                       mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta
                  (t', FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3652 =
                    let uu____3653 =
                      let uu____3660 = closure_as_term_delayed cfg env t' in
                      let uu____3663 =
                        let uu____3664 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____3664 in
                      (uu____3660, uu____3663) in
                    FStar_Syntax_Syntax.Tm_meta uu____3653 in
                  mk uu____3652 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) ->
                  let uu____3724 =
                    let uu____3725 =
                      let uu____3732 = closure_as_term_delayed cfg env t' in
                      let uu____3735 =
                        let uu____3736 =
                          let uu____3743 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____3743) in
                        FStar_Syntax_Syntax.Meta_monadic uu____3736 in
                      (uu____3732, uu____3735) in
                    FStar_Syntax_Syntax.Tm_meta uu____3725 in
                  mk uu____3724 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t', FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody))
                  ->
                  let uu____3762 =
                    let uu____3763 =
                      let uu____3770 = closure_as_term_delayed cfg env t' in
                      let uu____3773 =
                        let uu____3774 =
                          let uu____3783 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____3783) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3774 in
                      (uu____3770, uu____3773) in
                    FStar_Syntax_Syntax.Tm_meta uu____3763 in
                  mk uu____3762 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t', m) ->
                  let uu____3796 =
                    let uu____3797 =
                      let uu____3804 = closure_as_term_delayed cfg env t' in
                      (uu____3804, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____3797 in
                  mk uu____3796 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1 -> fun uu____3844 -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____3863 =
                    let uu____3874 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____3874
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____3893 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___124_3905 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_3905.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_3905.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3893)) in
                  (match uu____3863 with
                   | (nm, body1) ->
                       let lb1 =
                         let uu___125_3921 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___125_3921.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___125_3921.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___125_3921.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___125_3921.FStar_Syntax_Syntax.lbpos)
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3932, lbs), body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3991 -> fun env2 -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____4016 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____4016
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4036 -> fun env2 -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____4058 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____4058
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___126_4070 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___126_4070.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___126_4070.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41 -> FStar_Util.Inl _0_41)) in
                    let uu___127_4071 = lb in
                    let uu____4072 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___127_4071.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___127_4071.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4072;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___127_4071.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___127_4071.FStar_Syntax_Syntax.lbpos)
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4102 -> fun env1 -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1, branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____4191 =
                    match uu____4191 with
                    | (pat, w_opt, tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4246 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                              let uu____4267 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4327 ->
                                        fun uu____4328 ->
                                          match (uu____4327, uu____4328) with
                                          | ((pats1, env3), (p1, b)) ->
                                              let uu____4419 =
                                                norm_pat env3 p1 in
                                              (match uu____4419 with
                                               | (p2, env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____4267 with
                               | (pats1, env3) ->
                                   ((let uu___128_4501 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___128_4501.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___129_4520 = x in
                                let uu____4521 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4520.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4520.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4521
                                } in
                              ((let uu___130_4535 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4535.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___131_4546 = x in
                                let uu____4547 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4546.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4546.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4547
                                } in
                              ((let uu___132_4561 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4561.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x, t2) ->
                              let x1 =
                                let uu___133_4577 = x in
                                let uu____4578 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___133_4577.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___133_4577.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4578
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___134_4585 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___134_4585.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____4588 = norm_pat env1 pat in
                        (match uu____4588 with
                         | (pat1, env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4617 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____4617 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____4623 =
                    let uu____4624 =
                      let uu____4647 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____4647) in
                    FStar_Syntax_Syntax.Tm_match uu____4624 in
                  mk uu____4623 t1.FStar_Syntax_Syntax.pos))
and (closure_as_term_delayed :
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg ->
    fun env ->
      fun t ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> t
        | uu____4733 -> closure_as_term cfg env t
and (closures_as_args_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
        FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
        ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
          FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
          Prims.list)
  =
  fun cfg ->
    fun env ->
      fun args ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> args
        | uu____4759 ->
            FStar_List.map
              (fun uu____4776 ->
                 match uu____4776 with
                 | (x, imp) ->
                     let uu____4795 = closure_as_term_delayed cfg env x in
                     (uu____4795, imp)) args
and (closures_as_binders_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,
          env) FStar_Pervasives_Native.tuple2)
  =
  fun cfg ->
    fun env ->
      fun bs ->
        let uu____4809 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4858 ->
                  fun uu____4859 ->
                    match (uu____4858, uu____4859) with
                    | ((env1, out), (b, imp)) ->
                        let b1 =
                          let uu___135_4929 = b in
                          let uu____4930 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___135_4929.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___135_4929.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4930
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____4809 with | (env1, bs1) -> ((FStar_List.rev bs1), env1)
and (close_comp :
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg ->
    fun env ->
      fun c ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> c
        | uu____5023 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t, uopt) ->
                 let uu____5036 = closure_as_term_delayed cfg env t in
                 let uu____5037 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____5036 uu____5037
             | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                 let uu____5050 = closure_as_term_delayed cfg env t in
                 let uu____5051 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5050 uu____5051
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_5077 ->
                           match uu___82_5077 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5081 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____5081
                           | f -> f)) in
                 let uu____5085 =
                   let uu___136_5086 = c1 in
                   let uu____5087 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5087;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___136_5086.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____5085)
and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1 ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_5097 ->
            match uu___83_5097 with
            | FStar_Syntax_Syntax.DECREASES uu____5098 -> false
            | uu____5101 -> true))
and (close_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun env ->
      fun lopt ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___84_5119 ->
                      match uu___84_5119 with
                      | FStar_Syntax_Syntax.DECREASES uu____5120 -> false
                      | uu____5123 -> true)) in
            let rc1 =
              let uu___137_5125 = rc in
              let uu____5126 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___137_5125.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5126;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____5133 -> lopt
let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_int) in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_bool) in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_char) in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_string) in
  let arg_as_list a e a =
    let uu____5215 =
      let uu____5222 = FStar_Syntax_Embeddings.e_list e in
      FStar_Syntax_Embeddings.try_unembed uu____5222 in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5215 in
  let arg_as_bounded_int uu____5246 =
    match uu____5246 with
    | (a, uu____5258) ->
        let uu____5265 =
          let uu____5266 = FStar_Syntax_Subst.compress a in
          uu____5266.FStar_Syntax_Syntax.n in
        (match uu____5265 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5276;
                FStar_Syntax_Syntax.vars = uu____5277;_},
              ({
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_int (i, FStar_Pervasives_Native.None));
                 FStar_Syntax_Syntax.pos = uu____5279;
                 FStar_Syntax_Syntax.vars = uu____5280;_},
               uu____5281)::[])
             when
             let uu____5320 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             FStar_Util.ends_with uu____5320 "int_to_t" ->
             let uu____5321 =
               let uu____5326 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____5326) in
             FStar_Pervasives_Native.Some uu____5321
         | uu____5331 -> FStar_Pervasives_Native.None) in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5371 = f a in FStar_Pervasives_Native.Some uu____5371
    | uu____5372 -> FStar_Pervasives_Native.None in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5420 = f a0 a1 in FStar_Pervasives_Native.Some uu____5420
    | uu____5421 -> FStar_Pervasives_Native.None in
  let unary_op a422 a423 a424 a425 a426 =
    (Obj.magic
       (fun a ->
          fun as_a ->
            fun f ->
              fun res ->
                fun args ->
                  let uu____5463 = FStar_List.map as_a args in
                  lift_unary () ()
                    (fun a421 -> (Obj.magic (f res.psc_range)) a421)
                    uu____5463)) a422 a423 a424 a425 a426 in
  let binary_op a429 a430 a431 a432 a433 =
    (Obj.magic
       (fun a ->
          fun as_a ->
            fun f ->
              fun res ->
                fun args ->
                  let uu____5512 = FStar_List.map as_a args in
                  lift_binary () ()
                    (fun a427 ->
                       fun a428 -> (Obj.magic (f res.psc_range)) a427 a428)
                    uu____5512)) a429 a430 a431 a432 a433 in
  let as_primitive_step is_strong uu____5539 =
    match uu____5539 with
    | (l, arity, f) ->
        {
          name = l;
          arity;
          auto_reflect = FStar_Pervasives_Native.None;
          strong_reduction_ok = is_strong;
          requires_binder_substitution = false;
          interpretation = f
        } in
  let unary_int_op f =
    unary_op () (fun a434 -> (Obj.magic arg_as_int) a434)
      (fun a435 ->
         fun a436 ->
           (Obj.magic
              (fun r ->
                 fun x ->
                   let uu____5587 = f x in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_int r uu____5587)) a435 a436) in
  let binary_int_op f =
    binary_op () (fun a437 -> (Obj.magic arg_as_int) a437)
      (fun a438 ->
         fun a439 ->
           fun a440 ->
             (Obj.magic
                (fun r ->
                   fun x ->
                     fun y ->
                       let uu____5615 = f x y in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_int r uu____5615)) a438
               a439 a440) in
  let unary_bool_op f =
    unary_op () (fun a441 -> (Obj.magic arg_as_bool) a441)
      (fun a442 ->
         fun a443 ->
           (Obj.magic
              (fun r ->
                 fun x ->
                   let uu____5636 = f x in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_bool r uu____5636)) a442 a443) in
  let binary_bool_op f =
    binary_op () (fun a444 -> (Obj.magic arg_as_bool) a444)
      (fun a445 ->
         fun a446 ->
           fun a447 ->
             (Obj.magic
                (fun r ->
                   fun x ->
                     fun y ->
                       let uu____5664 = f x y in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_bool r uu____5664)) a445
               a446 a447) in
  let binary_string_op f =
    binary_op () (fun a448 -> (Obj.magic arg_as_string) a448)
      (fun a449 ->
         fun a450 ->
           fun a451 ->
             (Obj.magic
                (fun r ->
                   fun x ->
                     fun y ->
                       let uu____5692 = f x y in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_string r uu____5692)) a449
               a450 a451) in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5800 =
          let uu____5809 = as_a a in
          let uu____5812 = as_b b in (uu____5809, uu____5812) in
        (match uu____5800 with
         | (FStar_Pervasives_Native.Some a1, FStar_Pervasives_Native.Some b1)
             ->
             let uu____5827 =
               let uu____5828 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____5828 in
             FStar_Pervasives_Native.Some uu____5827
         | uu____5829 -> FStar_Pervasives_Native.None)
    | uu____5838 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____5852 =
        let uu____5853 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5853 in
      mk uu____5852 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5863 =
      let uu____5866 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5866 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5863 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____5898 =
      let uu____5899 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____5899 in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____5898 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5917 = arg_as_string a1 in
        (match uu____5917 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5923 =
               Obj.magic
                 (arg_as_list () (Obj.magic FStar_Syntax_Embeddings.e_string)
                    a2) in
             (match uu____5923 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5936 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____5936
              | uu____5937 -> FStar_Pervasives_Native.None)
         | uu____5942 -> FStar_Pervasives_Native.None)
    | uu____5945 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5955 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____5955 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false") in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5984 =
          let uu____6005 = arg_as_string fn in
          let uu____6008 = arg_as_int from_line in
          let uu____6011 = arg_as_int from_col in
          let uu____6014 = arg_as_int to_line in
          let uu____6017 = arg_as_int to_col in
          (uu____6005, uu____6008, uu____6011, uu____6014, uu____6017) in
        (match uu____5984 with
         | (FStar_Pervasives_Native.Some fn1, FStar_Pervasives_Native.Some
            from_l, FStar_Pervasives_Native.Some from_c,
            FStar_Pervasives_Native.Some to_l, FStar_Pervasives_Native.Some
            to_c) ->
             let r =
               let uu____6048 =
                 let uu____6049 = FStar_BigInt.to_int_fs from_l in
                 let uu____6050 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____6049 uu____6050 in
               let uu____6051 =
                 let uu____6052 = FStar_BigInt.to_int_fs to_l in
                 let uu____6053 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____6052 uu____6053 in
               FStar_Range.mk_range fn1 uu____6048 uu____6051 in
             let uu____6054 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r in
             FStar_Pervasives_Native.Some uu____6054
         | uu____6055 -> FStar_Pervasives_Native.None)
    | uu____6076 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ, uu____6103)::(a1, uu____6105)::(a2, uu____6107)::[] ->
        let uu____6144 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6144 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6157 -> FStar_Pervasives_Native.None)
    | uu____6158 -> failwith "Unexpected number of arguments" in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1, uu____6185)::[] ->
        let uu____6194 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1 in
        (match uu____6194 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6200 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r in
             FStar_Pervasives_Native.Some uu____6200
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    | uu____6201 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____6225 =
      let uu____6240 =
        let uu____6255 =
          let uu____6270 =
            let uu____6285 =
              let uu____6300 =
                let uu____6315 =
                  let uu____6330 =
                    let uu____6345 =
                      let uu____6360 =
                        let uu____6375 =
                          let uu____6390 =
                            let uu____6405 =
                              let uu____6420 =
                                let uu____6435 =
                                  let uu____6450 =
                                    let uu____6465 =
                                      let uu____6480 =
                                        let uu____6495 =
                                          let uu____6510 =
                                            let uu____6525 =
                                              let uu____6540 =
                                                let uu____6553 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"] in
                                                (uu____6553,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a452 ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a452)
                                                     (fun a453 ->
                                                        fun a454 ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a453 a454))) in
                                              let uu____6560 =
                                                let uu____6575 =
                                                  let uu____6588 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"] in
                                                  (uu____6588,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a455 ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.e_char)))
                                                            a455)
                                                       (fun a456 ->
                                                          fun a457 ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a456 a457))) in
                                                let uu____6595 =
                                                  let uu____6610 =
                                                    let uu____6625 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"] in
                                                    (uu____6625,
                                                      (Prims.parse_int "2"),
                                                      string_concat') in
                                                  let uu____6634 =
                                                    let uu____6651 =
                                                      let uu____6666 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"] in
                                                      (uu____6666,
                                                        (Prims.parse_int "5"),
                                                        mk_range1) in
                                                    [uu____6651] in
                                                  uu____6610 :: uu____6634 in
                                                uu____6575 :: uu____6595 in
                                              uu____6540 :: uu____6560 in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6525 in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6510 in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a458 ->
                                                (Obj.magic arg_as_string)
                                                  a458)
                                             (fun a459 ->
                                                fun a460 ->
                                                  fun a461 ->
                                                    (Obj.magic
                                                       string_compare') a459
                                                      a460 a461)))
                                          :: uu____6495 in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a462 ->
                                              (Obj.magic arg_as_bool) a462)
                                           (fun a463 ->
                                              fun a464 ->
                                                (Obj.magic string_of_bool1)
                                                  a463 a464)))
                                        :: uu____6480 in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a465 ->
                                            (Obj.magic arg_as_int) a465)
                                         (fun a466 ->
                                            fun a467 ->
                                              (Obj.magic string_of_int1) a466
                                                a467)))
                                      :: uu____6465 in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a468 ->
                                          (Obj.magic arg_as_int) a468)
                                       (fun a469 ->
                                          (Obj.magic arg_as_char) a469)
                                       (fun a470 ->
                                          fun a471 ->
                                            (Obj.magic
                                               (FStar_Syntax_Embeddings.embed
                                                  FStar_Syntax_Embeddings.e_string))
                                              a470 a471)
                                       (fun a472 ->
                                          fun a473 ->
                                            fun a474 ->
                                              (Obj.magic
                                                 (fun r ->
                                                    fun x ->
                                                      fun y ->
                                                        let uu____6857 =
                                                          FStar_BigInt.to_int_fs
                                                            x in
                                                        FStar_String.make
                                                          uu____6857 y)) a472
                                                a473 a474)))
                                    :: uu____6450 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x -> fun y -> Prims.strcat x y)))
                                  :: uu____6435 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x -> fun y -> Prims.strcat x y)))
                                :: uu____6420 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x -> fun y -> x || y))) ::
                              uu____6405 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x -> fun y -> x && y))) ::
                            uu____6390 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x -> Prims.op_Negation x))) ::
                          uu____6375 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x -> fun y -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6360 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op () (fun a475 -> (Obj.magic arg_as_int) a475)
                         (fun a476 ->
                            fun a477 ->
                              fun a478 ->
                                (Obj.magic
                                   (fun r ->
                                      fun x ->
                                        fun y ->
                                          let uu____7024 =
                                            FStar_BigInt.ge_big_int x y in
                                          FStar_Syntax_Embeddings.embed
                                            FStar_Syntax_Embeddings.e_bool r
                                            uu____7024)) a476 a477 a478)))
                      :: uu____6345 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a479 -> (Obj.magic arg_as_int) a479)
                       (fun a480 ->
                          fun a481 ->
                            fun a482 ->
                              (Obj.magic
                                 (fun r ->
                                    fun x ->
                                      fun y ->
                                        let uu____7050 =
                                          FStar_BigInt.gt_big_int x y in
                                        FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_bool r
                                          uu____7050)) a480 a481 a482)))
                    :: uu____6330 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a483 -> (Obj.magic arg_as_int) a483)
                     (fun a484 ->
                        fun a485 ->
                          fun a486 ->
                            (Obj.magic
                               (fun r ->
                                  fun x ->
                                    fun y ->
                                      let uu____7076 =
                                        FStar_BigInt.le_big_int x y in
                                      FStar_Syntax_Embeddings.embed
                                        FStar_Syntax_Embeddings.e_bool r
                                        uu____7076)) a484 a485 a486)))
                  :: uu____6315 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a487 -> (Obj.magic arg_as_int) a487)
                   (fun a488 ->
                      fun a489 ->
                        fun a490 ->
                          (Obj.magic
                             (fun r ->
                                fun x ->
                                  fun y ->
                                    let uu____7102 =
                                      FStar_BigInt.lt_big_int x y in
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_bool r
                                      uu____7102)) a488 a489 a490)))
                :: uu____6300 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x -> fun y -> FStar_BigInt.div_big_int x y)))
              :: uu____6285 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x -> fun y -> FStar_BigInt.mult_big_int x y)))
            :: uu____6270 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x -> fun y -> FStar_BigInt.sub_big_int x y)))
          :: uu____6255 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x -> fun y -> FStar_BigInt.add_big_int x y))) ::
        uu____6240 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x -> FStar_BigInt.minus_big_int x))) :: uu____6225 in
  let weak_ops =
    let uu____7241 =
      let uu____7260 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"] in
      (uu____7260, (Prims.parse_int "1"), prims_to_fstar_range_step) in
    [uu____7241] in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____7344 =
        let uu____7345 =
          let uu____7346 = FStar_Syntax_Syntax.as_arg c in [uu____7346] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7345 in
      uu____7344 FStar_Pervasives_Native.None r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m ->
              let uu____7396 =
                let uu____7409 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                (uu____7409, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a491 -> (Obj.magic arg_as_bounded_int) a491)
                     (fun a492 ->
                        fun a493 ->
                          fun a494 ->
                            (Obj.magic
                               (fun r ->
                                  fun uu____7425 ->
                                    fun uu____7426 ->
                                      match (uu____7425, uu____7426) with
                                      | ((int_to_t1, x), (uu____7445, y)) ->
                                          let uu____7455 =
                                            FStar_BigInt.add_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____7455)) a492 a493 a494))) in
              let uu____7456 =
                let uu____7471 =
                  let uu____7484 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  (uu____7484, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a495 -> (Obj.magic arg_as_bounded_int) a495)
                       (fun a496 ->
                          fun a497 ->
                            fun a498 ->
                              (Obj.magic
                                 (fun r ->
                                    fun uu____7500 ->
                                      fun uu____7501 ->
                                        match (uu____7500, uu____7501) with
                                        | ((int_to_t1, x), (uu____7520, y))
                                            ->
                                            let uu____7530 =
                                              FStar_BigInt.sub_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____7530)) a496 a497 a498))) in
                let uu____7531 =
                  let uu____7546 =
                    let uu____7559 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    (uu____7559, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a499 -> (Obj.magic arg_as_bounded_int) a499)
                         (fun a500 ->
                            fun a501 ->
                              fun a502 ->
                                (Obj.magic
                                   (fun r ->
                                      fun uu____7575 ->
                                        fun uu____7576 ->
                                          match (uu____7575, uu____7576) with
                                          | ((int_to_t1, x), (uu____7595, y))
                                              ->
                                              let uu____7605 =
                                                FStar_BigInt.mult_big_int x y in
                                              int_as_bounded r int_to_t1
                                                uu____7605)) a500 a501 a502))) in
                  let uu____7606 =
                    let uu____7621 =
                      let uu____7634 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      (uu____7634, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a503 -> (Obj.magic arg_as_bounded_int) a503)
                           (fun a504 ->
                              fun a505 ->
                                (Obj.magic
                                   (fun r ->
                                      fun uu____7646 ->
                                        match uu____7646 with
                                        | (int_to_t1, x) ->
                                            FStar_Syntax_Embeddings.embed
                                              FStar_Syntax_Embeddings.e_int r
                                              x)) a504 a505))) in
                    [uu____7621] in
                  uu____7546 :: uu____7606 in
                uu____7471 :: uu____7531 in
              uu____7396 :: uu____7456)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m ->
              let uu____7760 =
                let uu____7773 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                (uu____7773, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a506 -> (Obj.magic arg_as_bounded_int) a506)
                     (fun a507 ->
                        fun a508 ->
                          fun a509 ->
                            (Obj.magic
                               (fun r ->
                                  fun uu____7789 ->
                                    fun uu____7790 ->
                                      match (uu____7789, uu____7790) with
                                      | ((int_to_t1, x), (uu____7809, y)) ->
                                          let uu____7819 =
                                            FStar_BigInt.div_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____7819)) a507 a508 a509))) in
              let uu____7820 =
                let uu____7835 =
                  let uu____7848 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  (uu____7848, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a510 -> (Obj.magic arg_as_bounded_int) a510)
                       (fun a511 ->
                          fun a512 ->
                            fun a513 ->
                              (Obj.magic
                                 (fun r ->
                                    fun uu____7864 ->
                                      fun uu____7865 ->
                                        match (uu____7864, uu____7865) with
                                        | ((int_to_t1, x), (uu____7884, y))
                                            ->
                                            let uu____7894 =
                                              FStar_BigInt.mod_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____7894)) a511 a512 a513))) in
                [uu____7835] in
              uu____7760 :: uu____7820)) in
    FStar_List.append add_sub_mul_v div_mod_unsigned in
  let strong_steps =
    FStar_List.map (as_primitive_step true)
      (FStar_List.append basic_ops bounded_arith_ops) in
  let weak_steps = FStar_List.map (as_primitive_step false) weak_ops in
  FStar_All.pipe_left prim_from_list
    (FStar_List.append strong_steps weak_steps)
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ, uu____8006)::(a1, uu____8008)::(a2, uu____8010)::[] ->
        let uu____8047 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____8047 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___138_8053 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_8053.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___138_8053.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___139_8057 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8057.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8057.FStar_Syntax_Syntax.vars)
                })
         | uu____8058 -> FStar_Pervasives_Native.None)
    | (_typ, uu____8060)::uu____8061::(a1, uu____8063)::(a2, uu____8065)::[]
        ->
        let uu____8114 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____8114 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___138_8120 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_8120.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___138_8120.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___139_8124 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8124.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8124.FStar_Syntax_Syntax.vars)
                })
         | uu____8125 -> FStar_Pervasives_Native.None)
    | uu____8126 -> failwith "Unexpected number of arguments" in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  prim_from_list [propositional_equality; hetero_propositional_equality]
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____8178 = FStar_ST.op_Bang unembed_binder_knot in
    match uu____8178 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
let mk_psc_subst :
  'Auu____8223 .
    cfg ->
      ((FStar_Syntax_Syntax.bv, 'Auu____8223) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,
        closure) FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg ->
    fun env ->
      FStar_List.fold_right
        (fun uu____8283 ->
           fun subst1 ->
             match uu____8283 with
             | (binder_opt, closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b, Clos
                     (env1, term, uu____8324, uu____8325)) ->
                      let uu____8384 = b in
                      (match uu____8384 with
                       | (bv, uu____8392) ->
                           let uu____8393 =
                             let uu____8394 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid in
                             Prims.op_Negation uu____8394 in
                           if uu____8393
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____8399 = unembed_binder term1 in
                              match uu____8399 with
                              | FStar_Pervasives_Native.None -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8406 =
                                      let uu___140_8407 = bv in
                                      let uu____8408 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___140_8407.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___140_8407.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8408
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____8406 in
                                  let b_for_x =
                                    let uu____8412 =
                                      let uu____8419 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8419) in
                                    FStar_Syntax_Syntax.NT uu____8412 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_8429 ->
                                         match uu___85_8429 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8430,
                                              {
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_name
                                                  b';
                                                FStar_Syntax_Syntax.pos =
                                                  uu____8432;
                                                FStar_Syntax_Syntax.vars =
                                                  uu____8433;_})
                                             ->
                                             let uu____8438 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname in
                                             Prims.op_Negation uu____8438
                                         | uu____8439 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____8440 -> subst1)) env []
let reduce_primops :
  'Auu____8457 'Auu____8458 .
    cfg ->
      ((FStar_Syntax_Syntax.bv, 'Auu____8457) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,
        closure) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8458 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg ->
    fun env ->
      fun stack ->
        fun tm ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8500 = FStar_Syntax_Util.head_and_args tm in
             match uu____8500 with
             | (head1, args) ->
                 let uu____8537 =
                   let uu____8538 = FStar_Syntax_Util.un_uinst head1 in
                   uu____8538.FStar_Syntax_Syntax.n in
                 (match uu____8537 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8542 = find_prim_step cfg fv in
                      (match uu____8542 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8564 ->
                                   let uu____8565 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____8566 =
                                     FStar_Util.string_of_int l in
                                   let uu____8573 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8565 uu____8566 uu____8573);
                              tm)
                           else
                             (let uu____8575 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args in
                              match uu____8575 with
                              | (args_1, args_2) ->
                                  (log_primops cfg
                                     (fun uu____8686 ->
                                        let uu____8687 =
                                          FStar_Syntax_Print.term_to_string
                                            tm in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____8687);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____8690 ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      } in
                                    let uu____8692 =
                                      prim_step.interpretation psc args_1 in
                                    match uu____8692 with
                                    | FStar_Pervasives_Native.None ->
                                        (log_primops cfg
                                           (fun uu____8698 ->
                                              let uu____8699 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____8699);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____8705 ->
                                              let uu____8706 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm in
                                              let uu____8707 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____8706 uu____8707);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____8708 ->
                           (log_primops cfg
                              (fun uu____8712 ->
                                 let uu____8713 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8713);
                            tm)
                       | FStar_Pervasives_Native.None -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8717 ->
                            let uu____8718 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8718);
                       (match args with
                        | (a1, uu____8720)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8737 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8749 ->
                            let uu____8750 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8750);
                       (match args with
                        | (t, uu____8752)::(r, uu____8754)::[] ->
                            let uu____8781 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r in
                            (match uu____8781 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___141_8785 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___141_8785.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___141_8785.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None -> tm)
                        | uu____8788 -> tm))
                  | uu____8797 -> tm))
let reduce_equality :
  'Auu____8802 'Auu____8803 .
    cfg ->
      ((FStar_Syntax_Syntax.bv, 'Auu____8802) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,
        closure) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8803 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg ->
    fun tm ->
      reduce_primops
        (let uu___142_8841 = cfg in
         {
           steps =
             (let uu___143_8844 = default_steps in
              {
                beta = (uu___143_8844.beta);
                iota = (uu___143_8844.iota);
                zeta = (uu___143_8844.zeta);
                weak = (uu___143_8844.weak);
                hnf = (uu___143_8844.hnf);
                primops = true;
                no_delta_steps = (uu___143_8844.no_delta_steps);
                unfold_until = (uu___143_8844.unfold_until);
                unfold_only = (uu___143_8844.unfold_only);
                unfold_attr = (uu___143_8844.unfold_attr);
                unfold_tac = (uu___143_8844.unfold_tac);
                pure_subterms_within_computations =
                  (uu___143_8844.pure_subterms_within_computations);
                simplify = (uu___143_8844.simplify);
                erase_universes = (uu___143_8844.erase_universes);
                allow_unbound_universes =
                  (uu___143_8844.allow_unbound_universes);
                reify_ = (uu___143_8844.reify_);
                compress_uvars = (uu___143_8844.compress_uvars);
                no_full_norm = (uu___143_8844.no_full_norm);
                check_no_uvars = (uu___143_8844.check_no_uvars);
                unmeta = (uu___143_8844.unmeta);
                unascribe = (uu___143_8844.unascribe)
              });
           tcenv = (uu___142_8841.tcenv);
           debug = (uu___142_8841.debug);
           delta_level = (uu___142_8841.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___142_8841.strong);
           memoize_lazy = (uu___142_8841.memoize_lazy);
           normalize_pure_lets = (uu___142_8841.normalize_pure_lets)
         }) tm
let is_norm_request :
  'Auu____8848 .
    FStar_Syntax_Syntax.term -> 'Auu____8848 Prims.list -> Prims.bool
  =
  fun hd1 ->
    fun args ->
      let uu____8861 =
        let uu____8868 =
          let uu____8869 = FStar_Syntax_Util.un_uinst hd1 in
          uu____8869.FStar_Syntax_Syntax.n in
        (uu____8868, args) in
      match uu____8861 with
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____8875::uu____8876::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____8880::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv, steps::uu____8885::uu____8886::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____8889 -> false
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_8900 ->
    match uu___86_8900 with
    | FStar_Syntax_Embeddings.Zeta -> [Zeta]
    | FStar_Syntax_Embeddings.Iota -> [Iota]
    | FStar_Syntax_Embeddings.Delta ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl -> [Simplify]
    | FStar_Syntax_Embeddings.Weak -> [Weak]
    | FStar_Syntax_Embeddings.HNF -> [HNF]
    | FStar_Syntax_Embeddings.Primops -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____8906 =
          let uu____8909 =
            let uu____8910 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____8910 in
          [uu____8909] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____8906
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s -> FStar_List.concatMap tr_norm_step s
let get_norm_request :
  'Auu____8926 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term, 'Auu____8926) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list, FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm ->
    fun args ->
      let parse_steps s =
        let uu____8968 =
          let uu____8973 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step in
          FStar_Syntax_Embeddings.try_unembed uu____8973 s in
        match uu____8968 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____8989 = tr_norm_steps steps in
            FStar_Pervasives_Native.Some uu____8989
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      match args with
      | uu____9006::(tm, uu____9008)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm, uu____9037)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps, uu____9058)::uu____9059::(tm, uu____9061)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s in
          let uu____9098 =
            let uu____9103 = full_norm steps in parse_steps uu____9103 in
          (match uu____9098 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s in
               let s2 = add_exclude s1 Zeta in
               let s3 = add_exclude s2 Iota in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9142 -> FStar_Pervasives_Native.None
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_9159 ->
    match uu___87_9159 with
    | (App
        (uu____9162,
         {
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify);
           FStar_Syntax_Syntax.pos = uu____9163;
           FStar_Syntax_Syntax.vars = uu____9164;_},
         uu____9165, uu____9166))::uu____9167
        -> true
    | uu____9174 -> false
let firstn :
  'Auu____9180 .
    Prims.int ->
      'Auu____9180 Prims.list ->
        ('Auu____9180 Prims.list, 'Auu____9180 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k ->
    fun l ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let (should_reify : cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg ->
    fun stack ->
      match stack with
      | (App
          (uu____9216,
           {
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify);
             FStar_Syntax_Syntax.pos = uu____9217;
             FStar_Syntax_Syntax.vars = uu____9218;_},
           uu____9219, uu____9220))::uu____9221
          -> (cfg.steps).reify_
      | uu____9228 -> false
let rec (norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env ->
      fun stack ->
        fun t ->
          let t1 =
            if (cfg.debug).norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____9412 ->
                   let uu____9437 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9437
               | uu____9438 -> ())
            else ();
            FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____9446 ->
               let uu____9447 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____9448 = FStar_Syntax_Print.term_to_string t1 in
               let uu____9449 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____9456 =
                 let uu____9457 =
                   let uu____9460 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9460 in
                 stack_to_string uu____9457 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____9447 uu____9448 uu____9449 uu____9456);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____9483 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____9484 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____9485 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9486;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant;
                 FStar_Syntax_Syntax.fv_qual = uu____9487;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9490;
                 FStar_Syntax_Syntax.fv_delta = uu____9491;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9492;
                 FStar_Syntax_Syntax.fv_delta = uu____9493;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9494);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____9501 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1, args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____9537 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid in
                  Prims.op_Negation uu____9537)
               ->
               let cfg' =
                 let uu___144_9539 = cfg in
                 {
                   steps =
                     (let uu___145_9542 = cfg.steps in
                      {
                        beta = (uu___145_9542.beta);
                        iota = (uu___145_9542.iota);
                        zeta = (uu___145_9542.zeta);
                        weak = (uu___145_9542.weak);
                        hnf = (uu___145_9542.hnf);
                        primops = (uu___145_9542.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___145_9542.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___145_9542.unfold_attr);
                        unfold_tac = (uu___145_9542.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___145_9542.pure_subterms_within_computations);
                        simplify = (uu___145_9542.simplify);
                        erase_universes = (uu___145_9542.erase_universes);
                        allow_unbound_universes =
                          (uu___145_9542.allow_unbound_universes);
                        reify_ = (uu___145_9542.reify_);
                        compress_uvars = (uu___145_9542.compress_uvars);
                        no_full_norm = (uu___145_9542.no_full_norm);
                        check_no_uvars = (uu___145_9542.check_no_uvars);
                        unmeta = (uu___145_9542.unmeta);
                        unascribe = (uu___145_9542.unascribe)
                      });
                   tcenv = (uu___144_9539.tcenv);
                   debug = (uu___144_9539.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___144_9539.primitive_steps);
                   strong = (uu___144_9539.strong);
                   memoize_lazy = (uu___144_9539.memoize_lazy);
                   normalize_pure_lets = true
                 } in
               let uu____9545 = get_norm_request (norm cfg' env []) args in
               (match uu____9545 with
                | FStar_Pervasives_Native.None ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____9576 ->
                              fun stack1 ->
                                match uu____9576 with
                                | (a, aq) ->
                                    let uu____9588 =
                                      let uu____9589 =
                                        let uu____9596 =
                                          let uu____9597 =
                                            let uu____9628 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None in
                                            (env, a, uu____9628, false) in
                                          Clos uu____9597 in
                                        (uu____9596, aq,
                                          (t1.FStar_Syntax_Syntax.pos)) in
                                      Arg uu____9589 in
                                    uu____9588 :: stack1) args) in
                    (log cfg
                       (fun uu____9712 ->
                          let uu____9713 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args) in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____9713);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s, tm) ->
                    let delta_level =
                      let uu____9735 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_9740 ->
                                match uu___88_9740 with
                                | UnfoldUntil uu____9741 -> true
                                | UnfoldOnly uu____9742 -> true
                                | uu____9745 -> false)) in
                      if uu____9735
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___146_9750 = cfg in
                      let uu____9751 = to_fsteps s in
                      {
                        steps = uu____9751;
                        tcenv = (uu___146_9750.tcenv);
                        debug = (uu___146_9750.debug);
                        delta_level;
                        primitive_steps = (uu___146_9750.primitive_steps);
                        strong = (uu___146_9750.strong);
                        memoize_lazy = (uu___146_9750.memoize_lazy);
                        normalize_pure_lets = true
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      if (cfg.debug).print_normalized
                      then
                        let uu____9760 =
                          let uu____9761 =
                            let uu____9766 = FStar_Util.now () in
                            (t1, uu____9766) in
                          Debug uu____9761 in
                        uu____9760 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____9770 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____9770
           | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____9779 =
                      let uu____9786 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____9786, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____9779 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____9796 = FStar_Syntax_Syntax.lid_of_fv fv in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____9796 in
               let uu____9797 = FStar_TypeChecker_Env.qninfo_is_action qninfo in
               if uu____9797
               then
                 let b = should_reify cfg stack in
                 (log cfg
                    (fun uu____9803 ->
                       let uu____9804 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____9805 = FStar_Util.string_of_bool b in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____9804 uu____9805);
                  if b
                  then
                    (let uu____9806 = FStar_List.tl stack in
                     do_unfold_fv cfg env uu____9806 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____9814 = find_prim_step cfg fv in
                     FStar_Option.isNone uu____9814) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_9820 ->
                               match uu___89_9820 with
                               | FStar_TypeChecker_Env.UnfoldTac -> false
                               | FStar_TypeChecker_Env.NoDelta -> false
                               | FStar_TypeChecker_Env.Inlining -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only
                                   -> true
                               | FStar_TypeChecker_Env.Unfold l ->
                                   FStar_TypeChecker_Common.delta_depth_greater_than
                                     fv.FStar_Syntax_Syntax.fv_delta l))) in
                  let should_delta1 =
                    should_delta &&
                      (let attrs =
                         FStar_TypeChecker_Env.attrs_of_qninfo qninfo in
                       ((Prims.op_Negation (cfg.steps).unfold_tac) ||
                          (let uu____9830 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs in
                           Prims.op_Negation uu____9830))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None,
                                FStar_Pervasives_Native.Some uu____9849) ->
                                 false
                             | (FStar_Pervasives_Native.Some ats,
                                FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____9884, uu____9885) -> false))) in
                  log cfg
                    (fun uu____9907 ->
                       let uu____9908 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____9909 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____9910 =
                         FStar_Util.string_of_bool should_delta1 in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____9908
                         uu____9909 uu____9910);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____9913 = lookup_bvar env x in
               (match uu____9913 with
                | Univ uu____9916 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy -> failwith "Term variable not found"
                | Clos (env1, t0, r, fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____9965 = FStar_ST.op_Bang r in
                      (match uu____9965 with
                       | FStar_Pervasives_Native.Some (env2, t') ->
                           (log cfg
                              (fun uu____10083 ->
                                 let uu____10084 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____10085 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10084
                                   uu____10085);
                            (let uu____10086 =
                               let uu____10087 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____10087.FStar_Syntax_Syntax.n in
                             match uu____10086 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10090 ->
                                 norm cfg env2 stack t'
                             | uu____10107 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
               (match stack with
                | (UnivArgs uu____10177)::uu____10178 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10187)::uu____10188 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c, uu____10198, uu____10199))::stack_rest ->
                    (match c with
                     | Univ uu____10203 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10212 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____10233 ->
                                    let uu____10234 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10234);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____10274 ->
                                    let uu____10275 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10275);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     log cfg
                       (fun uu____10353 ->
                          let uu____10354 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10354);
                     norm cfg env stack1 t1)
                | (Debug uu____10355)::uu____10356 ->
                    if (cfg.steps).weak
                    then
                      let uu____10363 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____10363
                    else
                      (let uu____10365 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10365 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____10407 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10444 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10444)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_10449 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_10449.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_10449.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10450 -> lopt in
                           (log cfg
                              (fun uu____10456 ->
                                 let uu____10457 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10457);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___148_10466 = cfg in
                               {
                                 steps = (uu___148_10466.steps);
                                 tcenv = (uu___148_10466.tcenv);
                                 debug = (uu___148_10466.debug);
                                 delta_level = (uu___148_10466.delta_level);
                                 primitive_steps =
                                   (uu___148_10466.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_10466.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_10466.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10477)::uu____10478 ->
                    if (cfg.steps).weak
                    then
                      let uu____10485 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____10485
                    else
                      (let uu____10487 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10487 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____10529 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10566 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10566)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_10571 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_10571.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_10571.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10572 -> lopt in
                           (log cfg
                              (fun uu____10578 ->
                                 let uu____10579 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10579);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___148_10588 = cfg in
                               {
                                 steps = (uu___148_10588.steps);
                                 tcenv = (uu___148_10588.tcenv);
                                 debug = (uu___148_10588.debug);
                                 delta_level = (uu___148_10588.delta_level);
                                 primitive_steps =
                                   (uu___148_10588.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_10588.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_10588.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____10599)::uu____10600 ->
                    if (cfg.steps).weak
                    then
                      let uu____10611 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____10611
                    else
                      (let uu____10613 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10613 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____10655 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10692 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10692)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_10697 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_10697.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_10697.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10698 -> lopt in
                           (log cfg
                              (fun uu____10704 ->
                                 let uu____10705 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10705);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___148_10714 = cfg in
                               {
                                 steps = (uu___148_10714.steps);
                                 tcenv = (uu___148_10714.tcenv);
                                 debug = (uu___148_10714.debug);
                                 delta_level = (uu___148_10714.delta_level);
                                 primitive_steps =
                                   (uu___148_10714.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_10714.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_10714.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____10725)::uu____10726 ->
                    if (cfg.steps).weak
                    then
                      let uu____10737 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____10737
                    else
                      (let uu____10739 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10739 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____10781 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10818 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10818)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_10823 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_10823.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_10823.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10824 -> lopt in
                           (log cfg
                              (fun uu____10830 ->
                                 let uu____10831 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10831);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___148_10840 = cfg in
                               {
                                 steps = (uu___148_10840.steps);
                                 tcenv = (uu___148_10840.tcenv);
                                 debug = (uu___148_10840.debug);
                                 delta_level = (uu___148_10840.delta_level);
                                 primitive_steps =
                                   (uu___148_10840.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_10840.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_10840.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____10851)::uu____10852 ->
                    if (cfg.steps).weak
                    then
                      let uu____10867 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____10867
                    else
                      (let uu____10869 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10869 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____10911 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10948 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10948)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_10953 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_10953.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_10953.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10954 -> lopt in
                           (log cfg
                              (fun uu____10960 ->
                                 let uu____10961 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10961);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___148_10970 = cfg in
                               {
                                 steps = (uu___148_10970.steps);
                                 tcenv = (uu___148_10970.tcenv);
                                 debug = (uu___148_10970.debug);
                                 delta_level = (uu___148_10970.delta_level);
                                 primitive_steps =
                                   (uu___148_10970.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_10970.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_10970.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____10981 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____10981
                    else
                      (let uu____10983 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10983 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____11025 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____11062 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11062)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_11067 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_11067.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_11067.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11068 -> lopt in
                           (log cfg
                              (fun uu____11074 ->
                                 let uu____11075 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11075);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___148_11084 = cfg in
                               {
                                 steps = (uu___148_11084.steps);
                                 tcenv = (uu___148_11084.tcenv);
                                 debug = (uu___148_11084.debug);
                                 delta_level = (uu___148_11084.delta_level);
                                 primitive_steps =
                                   (uu___148_11084.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_11084.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_11084.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1, args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____11133 ->
                         fun stack1 ->
                           match uu____11133 with
                           | (a, aq) ->
                               let uu____11145 =
                                 let uu____11146 =
                                   let uu____11153 =
                                     let uu____11154 =
                                       let uu____11185 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____11185, false) in
                                     Clos uu____11154 in
                                   (uu____11153, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____11146 in
                               uu____11145 :: stack1) args) in
               (log cfg
                  (fun uu____11269 ->
                     let uu____11270 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11270);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x, f) ->
               if (cfg.steps).weak
               then
                 (match (env, stack) with
                  | ([], []) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___149_11306 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___149_11306.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___149_11306.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____11307 ->
                      let uu____11312 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11312)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____11315 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____11315 with
                  | (closing, f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____11346 =
                          let uu____11347 =
                            let uu____11354 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___150_11356 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___150_11356.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___150_11356.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11354) in
                          FStar_Syntax_Syntax.Tm_refine uu____11347 in
                        mk uu____11346 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
               if (cfg.steps).weak
               then
                 let uu____11375 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____11375
               else
                 (let uu____11377 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____11377 with
                  | (bs1, c1) ->
                      let c2 =
                        let uu____11385 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1 -> fun uu____11409 -> dummy :: env1)
                               env) in
                        norm_comp cfg uu____11385 c1 in
                      let t2 =
                        let uu____11431 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____11431 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) ->
               (match stack with
                | (Match uu____11542)::uu____11543 ->
                    (log cfg
                       (fun uu____11554 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____11555)::uu____11556 ->
                    (log cfg
                       (fun uu____11567 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____11568,
                     {
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify);
                       FStar_Syntax_Syntax.pos = uu____11569;
                       FStar_Syntax_Syntax.vars = uu____11570;_},
                     uu____11571, uu____11572))::uu____11573
                    ->
                    (log cfg
                       (fun uu____11582 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____11583)::uu____11584 ->
                    (log cfg
                       (fun uu____11595 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____11596 ->
                    (log cfg
                       (fun uu____11599 ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____11603 ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____11620 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____11620
                         | FStar_Util.Inr c ->
                             let uu____11628 = norm_comp cfg env c in
                             FStar_Util.Inr uu____11628 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____11641 =
                               let uu____11642 =
                                 let uu____11669 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____11669, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11642 in
                             mk uu____11641 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____11688 ->
                           let uu____11689 =
                             let uu____11690 =
                               let uu____11691 =
                                 let uu____11718 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____11718, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11691 in
                             mk uu____11690 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____11689))))
           | FStar_Syntax_Syntax.Tm_match (head1, branches) ->
               let stack1 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack in
               norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b, lbs), lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb ->
                         let uu____11828 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____11828 with
                         | (openings, lbunivs) ->
                             let cfg1 =
                               let uu___151_11848 = cfg in
                               let uu____11849 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___151_11848.steps);
                                 tcenv = uu____11849;
                                 debug = (uu___151_11848.debug);
                                 delta_level = (uu___151_11848.delta_level);
                                 primitive_steps =
                                   (uu___151_11848.primitive_steps);
                                 strong = (uu___151_11848.strong);
                                 memoize_lazy = (uu___151_11848.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11848.normalize_pure_lets)
                               } in
                             let norm1 t2 =
                               let uu____11854 =
                                 let uu____11855 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____11855 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____11854 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___152_11858 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___152_11858.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___152_11858.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___152_11858.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___152_11858.FStar_Syntax_Syntax.lbpos)
                             })) in
               let uu____11859 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11859
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11870,
                 { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____11871;
                   FStar_Syntax_Syntax.lbunivs = uu____11872;
                   FStar_Syntax_Syntax.lbtyp = uu____11873;
                   FStar_Syntax_Syntax.lbeff = uu____11874;
                   FStar_Syntax_Syntax.lbdef = uu____11875;
                   FStar_Syntax_Syntax.lbattrs = uu____11876;
                   FStar_Syntax_Syntax.lbpos = uu____11877;_}::uu____11878),
                uu____11879)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____11919 =
                 (Prims.op_Negation (cfg.steps).no_delta_steps) &&
                   ((((cfg.steps).pure_subterms_within_computations &&
                        (FStar_Syntax_Util.has_attribute
                           lb.FStar_Syntax_Syntax.lbattrs
                           FStar_Parser_Const.inline_let_attr))
                       ||
                       ((FStar_Syntax_Util.is_pure_effect n1) &&
                          (cfg.normalize_pure_lets ||
                             (FStar_Syntax_Util.has_attribute
                                lb.FStar_Syntax_Syntax.lbattrs
                                FStar_Parser_Const.inline_let_attr))))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.steps).pure_subterms_within_computations))) in
               if uu____11919
               then
                 let binder =
                   let uu____11921 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____11921 in
                 let env1 =
                   let uu____11931 =
                     let uu____11938 =
                       let uu____11939 =
                         let uu____11970 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11970,
                           false) in
                       Clos uu____11939 in
                     ((FStar_Pervasives_Native.Some binder), uu____11938) in
                   uu____11931 :: env in
                 (log cfg
                    (fun uu____12063 ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____12067 ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12068 = closure_as_term cfg env t1 in
                     rebuild cfg env stack uu____12068))
                 else
                   (let uu____12070 =
                      let uu____12075 =
                        let uu____12076 =
                          let uu____12077 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left in
                          FStar_All.pipe_right uu____12077
                            FStar_Syntax_Syntax.mk_binder in
                        [uu____12076] in
                      FStar_Syntax_Subst.open_term uu____12075 body in
                    match uu____12070 with
                    | (bs, body1) ->
                        (log cfg
                           (fun uu____12086 ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                          let lbname =
                            let x =
                              let uu____12094 = FStar_List.hd bs in
                              FStar_Pervasives_Native.fst uu____12094 in
                            FStar_Util.Inl
                              (let uu___153_12104 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___153_12104.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___153_12104.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }) in
                          log cfg
                            (fun uu____12107 ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___154_12109 = lb in
                             let uu____12110 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___154_12109.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___154_12109.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12110;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___154_12109.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___154_12109.FStar_Syntax_Syntax.lbpos)
                             } in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____12145 -> dummy :: env1) env) in
                           let stack1 = (Cfg cfg) :: stack in
                           let cfg1 =
                             let uu___155_12168 = cfg in
                             {
                               steps = (uu___155_12168.steps);
                               tcenv = (uu___155_12168.tcenv);
                               debug = (uu___155_12168.debug);
                               delta_level = (uu___155_12168.delta_level);
                               primitive_steps =
                                 (uu___155_12168.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___155_12168.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___155_12168.normalize_pure_lets)
                             } in
                           log cfg1
                             (fun uu____12171 ->
                                FStar_Util.print_string
                                  "+++ Normalizing Tm_let -- body\n");
                           norm cfg1 env'
                             ((Let
                                 (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                             :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true, lbs), body) when
               (cfg.steps).compress_uvars ||
                 ((Prims.op_Negation (cfg.steps).zeta) &&
                    (cfg.steps).pure_subterms_within_computations)
               ->
               let uu____12188 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____12188 with
                | (lbs1, body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____12224 =
                               let uu___156_12225 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___156_12225.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___156_12225.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____12224 in
                           let uu____12226 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____12226 with
                           | (xs, def_body, lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____12252 =
                                   FStar_List.map (fun uu____12268 -> dummy)
                                     lbs1 in
                                 let uu____12269 =
                                   let uu____12278 =
                                     FStar_List.map
                                       (fun uu____12298 -> dummy) xs1 in
                                   FStar_List.append uu____12278 env in
                                 FStar_List.append uu____12252 uu____12269 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12322 =
                                       let uu___157_12323 = rc in
                                       let uu____12324 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___157_12323.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12324;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___157_12323.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____12322
                                 | uu____12331 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___158_12335 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___158_12335.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___158_12335.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___158_12335.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___158_12335.FStar_Syntax_Syntax.lbpos)
                               }) lbs1 in
                    let env' =
                      let uu____12345 =
                        FStar_List.map (fun uu____12361 -> dummy) lbs2 in
                      FStar_List.append uu____12345 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____12369 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____12369 with
                     | (lbs3, body3) ->
                         let t2 =
                           let uu___159_12385 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___159_12385.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___159_12385.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs, body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____12412 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____12412
           | FStar_Syntax_Syntax.Tm_let (lbs, body) ->
               let uu____12431 =
                 FStar_List.fold_right
                   (fun lb ->
                      fun uu____12507 ->
                        match uu____12507 with
                        | (rec_env, memos, i) ->
                            let bv =
                              let uu___160_12628 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___160_12628.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___160_12628.FStar_Syntax_Syntax.sort)
                              } in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____12431 with
                | (rec_env, memos, uu____12841) ->
                    let uu____12894 =
                      FStar_List.map2
                        (fun lb ->
                           fun memo ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb ->
                           fun env1 ->
                             let uu____13205 =
                               let uu____13212 =
                                 let uu____13213 =
                                   let uu____13244 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13244, false) in
                                 Clos uu____13213 in
                               (FStar_Pervasives_Native.None, uu____13212) in
                             uu____13205 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1, m) ->
               (log cfg
                  (fun uu____13354 ->
                     let uu____13355 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13355);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1, t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13377 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____13379::uu____13380 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l, r, uu____13385) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____13408 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____13422 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____13422
                              | uu____13433 -> m in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____13437 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13463 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13481 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____13498 =
                        let uu____13499 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos in
                        let uu____13500 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13499 uu____13500 in
                      failwith uu____13498
                    else rebuild cfg env stack t2
                | uu____13502 -> norm cfg env stack t2))
and (do_unfold_fv :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env ->
      fun stack ->
        fun t0 ->
          fun qninfo ->
            fun f ->
              let r_env =
                let uu____13512 = FStar_Syntax_Syntax.range_of_fv f in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____13512 in
              let uu____13513 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo in
              match uu____13513 with
              | FStar_Pervasives_Native.None ->
                  (log cfg
                     (fun uu____13526 ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us, t) ->
                  (log cfg
                     (fun uu____13537 ->
                        let uu____13538 =
                          FStar_Syntax_Print.term_to_string t0 in
                        let uu____13539 = FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____13538 uu____13539);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____13544 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                         FStar_Syntax_Subst.set_use_range uu____13544 t) in
                    let n1 = FStar_List.length us in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us', uu____13553))::stack1 ->
                          let env1 =
                            FStar_All.pipe_right us'
                              (FStar_List.fold_left
                                 (fun env1 ->
                                    fun u ->
                                      (FStar_Pervasives_Native.None,
                                        (Univ u))
                                      :: env1) env) in
                          norm cfg env1 stack1 t1
                      | uu____13608 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____13611 ->
                          let uu____13614 =
                            let uu____13615 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____13615 in
                          failwith uu____13614
                    else norm cfg env stack t1))
and (reduce_impure_comp :
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,
            (FStar_Syntax_Syntax.monad_name, FStar_Syntax_Syntax.monad_name)
              FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env ->
      fun stack ->
        fun head1 ->
          fun m ->
            fun t ->
              let t1 = norm cfg env [] t in
              let stack1 = (Cfg cfg) :: stack in
              let cfg1 =
                if (cfg.steps).pure_subterms_within_computations
                then
                  let new_steps =
                    [PureSubtermsWithinComputations;
                    Primops;
                    AllowUnboundUniverses;
                    EraseUniverses;
                    Exclude Zeta;
                    Inlining] in
                  let uu___161_13639 = cfg in
                  let uu____13640 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps in
                  {
                    steps = uu____13640;
                    tcenv = (uu___161_13639.tcenv);
                    debug = (uu___161_13639.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___161_13639.primitive_steps);
                    strong = (uu___161_13639.strong);
                    memoize_lazy = (uu___161_13639.memoize_lazy);
                    normalize_pure_lets =
                      (uu___161_13639.normalize_pure_lets)
                  }
                else
                  (let uu___162_13642 = cfg in
                   {
                     steps =
                       (let uu___163_13645 = cfg.steps in
                        {
                          beta = (uu___163_13645.beta);
                          iota = (uu___163_13645.iota);
                          zeta = false;
                          weak = (uu___163_13645.weak);
                          hnf = (uu___163_13645.hnf);
                          primops = (uu___163_13645.primops);
                          no_delta_steps = (uu___163_13645.no_delta_steps);
                          unfold_until = (uu___163_13645.unfold_until);
                          unfold_only = (uu___163_13645.unfold_only);
                          unfold_attr = (uu___163_13645.unfold_attr);
                          unfold_tac = (uu___163_13645.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___163_13645.pure_subterms_within_computations);
                          simplify = (uu___163_13645.simplify);
                          erase_universes = (uu___163_13645.erase_universes);
                          allow_unbound_universes =
                            (uu___163_13645.allow_unbound_universes);
                          reify_ = (uu___163_13645.reify_);
                          compress_uvars = (uu___163_13645.compress_uvars);
                          no_full_norm = (uu___163_13645.no_full_norm);
                          check_no_uvars = (uu___163_13645.check_no_uvars);
                          unmeta = (uu___163_13645.unmeta);
                          unascribe = (uu___163_13645.unascribe)
                        });
                     tcenv = (uu___162_13642.tcenv);
                     debug = (uu___162_13642.debug);
                     delta_level = (uu___162_13642.delta_level);
                     primitive_steps = (uu___162_13642.primitive_steps);
                     strong = (uu___162_13642.strong);
                     memoize_lazy = (uu___162_13642.memoize_lazy);
                     normalize_pure_lets =
                       (uu___162_13642.normalize_pure_lets)
                   }) in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1, m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1) in
              norm cfg1 env
                ((Meta (metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1
and (do_reify_monadic :
  (Prims.unit -> FStar_Syntax_Syntax.term) ->
    cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun fallback ->
    fun cfg ->
      fun env ->
        fun stack ->
          fun head1 ->
            fun m ->
              fun t ->
                let head0 = head1 in
                let head2 = FStar_Syntax_Util.unascribe head1 in
                log cfg
                  (fun uu____13675 ->
                     let uu____13676 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____13677 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____13676
                       uu____13677);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2 in
                 let uu____13679 =
                   let uu____13680 = FStar_Syntax_Subst.compress head3 in
                   uu____13680.FStar_Syntax_Syntax.n in
                 match uu____13679 with
                 | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                     let ed =
                       let uu____13698 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____13698 in
                     let uu____13699 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____13699 with
                      | (uu____13700, bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____13706 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____13714 =
                                   let uu____13715 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____13715.FStar_Syntax_Syntax.n in
                                 match uu____13714 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1, FStar_Syntax_Syntax.Meta_monadic
                                      (uu____13721, uu____13722))
                                     ->
                                     let uu____13731 =
                                       let uu____13732 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____13732.FStar_Syntax_Syntax.n in
                                     (match uu____13731 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,
                                           FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____13738, msrc, uu____13740))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____13749 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____13749
                                      | uu____13750 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____13751 ->
                                     FStar_Pervasives_Native.None in
                               let uu____13752 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____13752 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___164_13757 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___164_13757.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___164_13757.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___164_13757.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___164_13757.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___164_13757.FStar_Syntax_Syntax.lbpos)
                                      } in
                                    let uu____13758 = FStar_List.tl stack in
                                    let uu____13759 =
                                      let uu____13760 =
                                        let uu____13763 =
                                          let uu____13764 =
                                            let uu____13777 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____13777) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____13764 in
                                        FStar_Syntax_Syntax.mk uu____13763 in
                                      uu____13760
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____13758 uu____13759
                                | FStar_Pervasives_Native.None ->
                                    let uu____13793 =
                                      let uu____13794 = is_return body in
                                      match uu____13794 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____13798;
                                            FStar_Syntax_Syntax.vars =
                                              uu____13799;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____13804 -> false in
                                    if uu____13793
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head3.FStar_Syntax_Syntax.pos in
                                       let head4 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify
                                           lb.FStar_Syntax_Syntax.lbdef in
                                       let body1 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify body in
                                       let body_rc =
                                         {
                                           FStar_Syntax_Syntax.residual_effect
                                             = m;
                                           FStar_Syntax_Syntax.residual_typ =
                                             (FStar_Pervasives_Native.Some t);
                                           FStar_Syntax_Syntax.residual_flags
                                             = []
                                         } in
                                       let body2 =
                                         let uu____13827 =
                                           let uu____13830 =
                                             let uu____13831 =
                                               let uu____13848 =
                                                 let uu____13851 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____13851] in
                                               (uu____13848, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____13831 in
                                           FStar_Syntax_Syntax.mk uu____13830 in
                                         uu____13827
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____13867 =
                                           let uu____13868 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____13868.FStar_Syntax_Syntax.n in
                                         match uu____13867 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,
                                              uu____13874::uu____13875::[])
                                             ->
                                             let uu____13882 =
                                               let uu____13885 =
                                                 let uu____13886 =
                                                   let uu____13893 =
                                                     let uu____13896 =
                                                       let uu____13897 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____13897 in
                                                     let uu____13898 =
                                                       let uu____13901 =
                                                         let uu____13902 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____13902 in
                                                       [uu____13901] in
                                                     uu____13896 ::
                                                       uu____13898 in
                                                   (bind1, uu____13893) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____13886 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____13885 in
                                             uu____13882
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____13910 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let maybe_range_arg =
                                         let uu____13916 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs in
                                         if uu____13916
                                         then
                                           let uu____13919 =
                                             let uu____13920 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____13920 in
                                           let uu____13921 =
                                             let uu____13924 =
                                               let uu____13925 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____13925 in
                                             [uu____13924] in
                                           uu____13919 :: uu____13921
                                         else [] in
                                       let reified =
                                         let uu____13930 =
                                           let uu____13933 =
                                             let uu____13934 =
                                               let uu____13949 =
                                                 let uu____13952 =
                                                   let uu____13955 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp in
                                                   let uu____13956 =
                                                     let uu____13959 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t in
                                                     [uu____13959] in
                                                   uu____13955 :: uu____13956 in
                                                 let uu____13960 =
                                                   let uu____13963 =
                                                     let uu____13966 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____13967 =
                                                       let uu____13970 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4 in
                                                       let uu____13971 =
                                                         let uu____13974 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____13975 =
                                                           let uu____13978 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____13978] in
                                                         uu____13974 ::
                                                           uu____13975 in
                                                       uu____13970 ::
                                                         uu____13971 in
                                                     uu____13966 ::
                                                       uu____13967 in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____13963 in
                                                 FStar_List.append
                                                   uu____13952 uu____13960 in
                                               (bind_inst, uu____13949) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____13934 in
                                           FStar_Syntax_Syntax.mk uu____13933 in
                                         uu____13930
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____13990 ->
                                            let uu____13991 =
                                              FStar_Syntax_Print.term_to_string
                                                head0 in
                                            let uu____13992 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____13991 uu____13992);
                                       (let uu____13993 = FStar_List.tl stack in
                                        norm cfg env uu____13993 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app, args) ->
                     let ed =
                       let uu____14017 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14017 in
                     let uu____14018 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____14018 with
                      | (uu____14019, bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____14054 =
                                  let uu____14055 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____14055.FStar_Syntax_Syntax.n in
                                match uu____14054 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2, uu____14061) -> t2
                                | uu____14066 -> head4 in
                              let uu____14067 =
                                let uu____14068 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____14068.FStar_Syntax_Syntax.n in
                              match uu____14067 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____14074 -> FStar_Pervasives_Native.None in
                            let uu____14075 = maybe_extract_fv head4 in
                            match uu____14075 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____14085 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____14085
                                ->
                                let head5 = norm cfg env [] head4 in
                                let action_unfolded =
                                  let uu____14090 = maybe_extract_fv head5 in
                                  match uu____14090 with
                                  | FStar_Pervasives_Native.Some uu____14095
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____14096 ->
                                      FStar_Pervasives_Native.Some false in
                                (head5, action_unfolded)
                            | uu____14101 ->
                                (head4, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____14116 =
                              match uu____14116 with
                              | (e, q) ->
                                  let uu____14123 =
                                    let uu____14124 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____14124.FStar_Syntax_Syntax.n in
                                  (match uu____14123 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,
                                        FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1, m2, t'))
                                       ->
                                       let uu____14139 =
                                         FStar_Syntax_Util.is_pure_effect m1 in
                                       Prims.op_Negation uu____14139
                                   | uu____14140 -> false) in
                            let uu____14141 =
                              let uu____14142 =
                                let uu____14149 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____14149 :: args in
                              FStar_Util.for_some is_arg_impure uu____14142 in
                            if uu____14141
                            then
                              let uu____14154 =
                                let uu____14155 =
                                  FStar_Syntax_Print.term_to_string head3 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____14155 in
                              failwith uu____14154
                            else ());
                           (let uu____14157 = maybe_unfold_action head_app in
                            match uu____14157 with
                            | (head_app1, found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head3.FStar_Syntax_Syntax.pos in
                                let body =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head_app1, args)) in
                                let body1 =
                                  match found_action with
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Syntax_Util.mk_reify body
                                  | FStar_Pervasives_Native.Some (false) ->
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_meta
                                           (body,
                                             (FStar_Syntax_Syntax.Meta_monadic
                                                (m, t))))
                                  | FStar_Pervasives_Native.Some (true) ->
                                      body in
                                (log cfg
                                   (fun uu____14198 ->
                                      let uu____14199 =
                                        FStar_Syntax_Print.term_to_string
                                          head0 in
                                      let uu____14200 =
                                        FStar_Syntax_Print.term_to_string
                                          body1 in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____14199 uu____14200);
                                 (let uu____14201 = FStar_List.tl stack in
                                  norm cfg env uu____14201 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e, FStar_Syntax_Syntax.Meta_monadic uu____14203) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e, FStar_Syntax_Syntax.Meta_monadic_lift
                      (msrc, mtgt, t'))
                     ->
                     let lifted =
                       let uu____14227 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____14227 in
                     (log cfg
                        (fun uu____14231 ->
                           let uu____14232 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____14232);
                      (let uu____14233 = FStar_List.tl stack in
                       norm cfg env uu____14233 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e, branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____14354 ->
                               match uu____14354 with
                               | (pat, wopt, tm) ->
                                   let uu____14402 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____14402))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos in
                     let uu____14434 = FStar_List.tl stack in
                     norm cfg env uu____14434 tm
                 | uu____14435 -> fallback ())
and (reify_lift :
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun e ->
      fun msrc ->
        fun mtgt ->
          fun t ->
            let env = cfg.tcenv in
            log cfg
              (fun uu____14449 ->
                 let uu____14450 = FStar_Ident.string_of_lid msrc in
                 let uu____14451 = FStar_Ident.string_of_lid mtgt in
                 let uu____14452 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14450
                   uu____14451 uu____14452);
            (let uu____14453 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc) in
             if uu____14453
             then
               let ed =
                 let uu____14455 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt in
                 FStar_TypeChecker_Env.get_effect_decl env uu____14455 in
               let uu____14456 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____14456 with
               | (uu____14457, return_repr) ->
                   let return_inst =
                     let uu____14466 =
                       let uu____14467 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____14467.FStar_Syntax_Syntax.n in
                     match uu____14466 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm, uu____14473::[]) ->
                         let uu____14480 =
                           let uu____14483 =
                             let uu____14484 =
                               let uu____14491 =
                                 let uu____14494 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____14494] in
                               (return_tm, uu____14491) in
                             FStar_Syntax_Syntax.Tm_uinst uu____14484 in
                           FStar_Syntax_Syntax.mk uu____14483 in
                         uu____14480 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14502 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____14505 =
                     let uu____14508 =
                       let uu____14509 =
                         let uu____14524 =
                           let uu____14527 = FStar_Syntax_Syntax.as_arg t in
                           let uu____14528 =
                             let uu____14531 = FStar_Syntax_Syntax.as_arg e in
                             [uu____14531] in
                           uu____14527 :: uu____14528 in
                         (return_inst, uu____14524) in
                       FStar_Syntax_Syntax.Tm_app uu____14509 in
                     FStar_Syntax_Syntax.mk uu____14508 in
                   uu____14505 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14540 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt in
                match uu____14540 with
                | FStar_Pervasives_Native.None ->
                    let uu____14543 =
                      let uu____14544 = FStar_Ident.text_of_lid msrc in
                      let uu____14545 = FStar_Ident.text_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14544 uu____14545 in
                    failwith uu____14543
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14546;
                      FStar_TypeChecker_Env.mtarget = uu____14547;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14548;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None;_};_}
                    ->
                    let uu____14563 =
                      let uu____14564 = FStar_Ident.text_of_lid msrc in
                      let uu____14565 = FStar_Ident.text_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14564 uu____14565 in
                    failwith uu____14563
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14566;
                      FStar_TypeChecker_Env.mtarget = uu____14567;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14568;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14592 =
                      env.FStar_TypeChecker_Env.universe_of env t in
                    let uu____14593 = FStar_Syntax_Util.mk_reify e in
                    lift uu____14592 t FStar_Syntax_Syntax.tun uu____14593))
and (norm_pattern_args :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
        FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
        Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
          FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
          Prims.list Prims.list)
  =
  fun cfg ->
    fun env ->
      fun args ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____14649 ->
                   match uu____14649 with
                   | (a, imp) ->
                       let uu____14660 = norm cfg env [] a in
                       (uu____14660, imp))))
and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg ->
    fun env ->
      fun comp ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t, uopt) ->
            let uu___165_14674 = comp in
            let uu____14675 =
              let uu____14676 =
                let uu____14685 = norm cfg env [] t in
                let uu____14686 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____14685, uu____14686) in
              FStar_Syntax_Syntax.Total uu____14676 in
            {
              FStar_Syntax_Syntax.n = uu____14675;
              FStar_Syntax_Syntax.pos =
                (uu___165_14674.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___165_14674.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
            let uu___166_14701 = comp in
            let uu____14702 =
              let uu____14703 =
                let uu____14712 = norm cfg env [] t in
                let uu____14713 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____14712, uu____14713) in
              FStar_Syntax_Syntax.GTotal uu____14703 in
            {
              FStar_Syntax_Syntax.n = uu____14702;
              FStar_Syntax_Syntax.pos =
                (uu___166_14701.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___166_14701.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____14765 ->
                      match uu____14765 with
                      | (a, i) ->
                          let uu____14776 = norm cfg env [] a in
                          (uu____14776, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___90_14787 ->
                      match uu___90_14787 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____14791 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____14791
                      | f -> f)) in
            let uu___167_14795 = comp in
            let uu____14796 =
              let uu____14797 =
                let uu___168_14798 = ct in
                let uu____14799 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____14800 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____14803 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____14799;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___168_14798.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____14800;
                  FStar_Syntax_Syntax.effect_args = uu____14803;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____14797 in
            {
              FStar_Syntax_Syntax.n = uu____14796;
              FStar_Syntax_Syntax.pos =
                (uu___167_14795.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___167_14795.FStar_Syntax_Syntax.vars)
            }
and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg ->
    fun env ->
      fun uu____14814 ->
        match uu____14814 with
        | (x, imp) ->
            let uu____14817 =
              let uu___169_14818 = x in
              let uu____14819 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___169_14818.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___169_14818.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14819
              } in
            (uu____14817, imp)
and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg ->
    fun env ->
      fun bs ->
        let uu____14825 =
          FStar_List.fold_left
            (fun uu____14843 ->
               fun b ->
                 match uu____14843 with
                 | (nbs', env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____14825 with | (nbs, uu____14883) -> FStar_List.rev nbs
and (norm_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun env ->
      fun lopt ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu____14899 =
              let uu___170_14900 = rc in
              let uu____14901 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___170_14900.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14901;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___170_14900.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____14899
        | uu____14908 -> lopt
and (maybe_simplify :
  cfg ->
    ((FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env ->
      fun stack ->
        fun tm ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          if (cfg.debug).b380
          then
            (let uu____14929 = FStar_Syntax_Print.term_to_string tm in
             let uu____14930 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____14929
               uu____14930)
          else ();
          tm'
and (maybe_simplify_aux :
  cfg ->
    ((FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env ->
      fun stack ->
        fun tm ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____14950 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify in
          if uu____14950
          then tm1
          else
            (let w t =
               let uu___171_14962 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___171_14962.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___171_14962.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               let uu____14971 =
                 let uu____14972 = FStar_Syntax_Util.unmeta t in
                 uu____14972.FStar_Syntax_Syntax.n in
               match uu____14971 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14979 -> FStar_Pervasives_Native.None in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t, uu____15024)::args1, (bv, uu____15027)::bs1) ->
                   let uu____15061 =
                     let uu____15062 = FStar_Syntax_Subst.compress t in
                     uu____15062.FStar_Syntax_Syntax.n in
                   (match uu____15061 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____15066 -> false)
               | ([], []) -> true
               | (uu____15087, uu____15088) -> false in
             let is_applied bs t =
               let uu____15124 = FStar_Syntax_Util.head_and_args' t in
               match uu____15124 with
               | (hd1, args) ->
                   let uu____15157 =
                     let uu____15158 = FStar_Syntax_Subst.compress hd1 in
                     uu____15158.FStar_Syntax_Syntax.n in
                   (match uu____15157 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____15164 -> FStar_Pervasives_Native.None) in
             let is_applied_maybe_squashed bs t =
               let uu____15176 = FStar_Syntax_Util.is_squash t in
               match uu____15176 with
               | FStar_Pervasives_Native.Some (uu____15187, t') ->
                   is_applied bs t'
               | uu____15199 ->
                   let uu____15208 = FStar_Syntax_Util.is_auto_squash t in
                   (match uu____15208 with
                    | FStar_Pervasives_Native.Some (uu____15219, t') ->
                        is_applied bs t'
                    | uu____15231 -> is_applied bs t) in
             let is_quantified_const phi =
               let uu____15248 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu____15248 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid, (p, uu____15255)::(q, uu____15257)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____15292 =
                     FStar_Syntax_Util.destruct_typ_as_formula p in
                   (match uu____15292 with
                    | FStar_Pervasives_Native.None ->
                        let uu____15297 =
                          let uu____15298 = FStar_Syntax_Subst.compress p in
                          uu____15298.FStar_Syntax_Syntax.n in
                        (match uu____15297 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15304 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q in
                             FStar_Pervasives_Native.Some uu____15304
                         | uu____15305 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1, (p1, uu____15308)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____15333 =
                          let uu____15334 = FStar_Syntax_Subst.compress p1 in
                          uu____15334.FStar_Syntax_Syntax.n in
                        (match uu____15333 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15340 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q in
                             FStar_Pervasives_Native.Some uu____15340
                         | uu____15341 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs, pats, phi1)) ->
                        let uu____15345 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1 in
                        (match uu____15345 with
                         | FStar_Pervasives_Native.None ->
                             let uu____15350 =
                               is_applied_maybe_squashed bs phi1 in
                             (match uu____15350 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0)) in
                                  let uu____15357 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q in
                                  FStar_Pervasives_Native.Some uu____15357
                              | FStar_Pervasives_Native.None ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1, (p1, uu____15360)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____15385 =
                               is_applied_maybe_squashed bs p1 in
                             (match uu____15385 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0)) in
                                  let uu____15392 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q in
                                  FStar_Pervasives_Native.Some uu____15392
                              | uu____15393 -> FStar_Pervasives_Native.None)
                         | uu____15396 -> FStar_Pervasives_Native.None)
                    | uu____15399 -> FStar_Pervasives_Native.None)
               | uu____15402 -> FStar_Pervasives_Native.None in
             let is_const_match phi =
               let uu____15413 =
                 let uu____15414 = FStar_Syntax_Subst.compress phi in
                 uu____15414.FStar_Syntax_Syntax.n in
               match uu____15413 with
               | FStar_Syntax_Syntax.Tm_match (uu____15419, br::brs) ->
                   let uu____15486 = br in
                   (match uu____15486 with
                    | (uu____15503, uu____15504, e) ->
                        let r =
                          let uu____15525 = simp_t e in
                          match uu____15525 with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15531 =
                                FStar_List.for_all
                                  (fun uu____15549 ->
                                     match uu____15549 with
                                     | (uu____15562, uu____15563, e') ->
                                         let uu____15577 = simp_t e' in
                                         uu____15577 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs in
                              if uu____15531
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None in
                        r)
               | uu____15585 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____15590 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____15590
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15611 =
                 match uu____15611 with
                 | (t1, q) ->
                     let uu____15624 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____15624 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
                      | uu____15652 -> (t1, q)) in
               let uu____15661 = FStar_Syntax_Util.head_and_args t in
               match uu____15661 with
               | (head1, args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
             let rec clearly_inhabited ty =
               let uu____15723 =
                 let uu____15724 = FStar_Syntax_Util.unmeta ty in
                 uu____15724.FStar_Syntax_Syntax.n in
               match uu____15723 with
               | FStar_Syntax_Syntax.Tm_uinst (t, uu____15728) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15733, c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15753 -> false in
             let simplify1 arg =
               let uu____15776 = simp_t (FStar_Pervasives_Native.fst arg) in
               (uu____15776, arg) in
             let uu____15785 = is_quantified_const tm1 in
             match uu____15785 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____15789 = norm cfg env [] tm2 in
                 maybe_simplify_aux cfg env stack uu____15789
             | FStar_Pervasives_Native.None ->
                 let uu____15790 =
                   let uu____15791 = FStar_Syntax_Subst.compress tm1 in
                   uu____15791.FStar_Syntax_Syntax.n in
                 (match uu____15790 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15795;
                              FStar_Syntax_Syntax.vars = uu____15796;_},
                            uu____15797);
                         FStar_Syntax_Syntax.pos = uu____15798;
                         FStar_Syntax_Syntax.vars = uu____15799;_},
                       args)
                      ->
                      let uu____15825 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____15825
                      then
                        let uu____15826 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        (match uu____15826 with
                         | (FStar_Pervasives_Native.Some (true), uu____15873)::
                             (uu____15874, (arg, uu____15876))::[] ->
                             maybe_auto_squash arg
                         | (uu____15925, (arg, uu____15927))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____15928)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____15977)::uu____15978::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16029::(FStar_Pervasives_Native.Some
                                         (false), uu____16030)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16081 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16095 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____16095
                         then
                           let uu____16096 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1) in
                           match uu____16096 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____16143)::uu____16144::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16195::(FStar_Pervasives_Native.Some
                                           (true), uu____16196)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____16247)::(uu____16248, (arg, uu____16250))::[]
                               -> maybe_auto_squash arg
                           | (uu____16299, (arg, uu____16301))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____16302)::[]
                               -> maybe_auto_squash arg
                           | uu____16351 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16365 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____16365
                            then
                              let uu____16366 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1) in
                              match uu____16366 with
                              | uu____16413::(FStar_Pervasives_Native.Some
                                              (true), uu____16414)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____16465)::uu____16466::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____16517)::(uu____16518,
                                                (arg, uu____16520))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16569, (p, uu____16571))::(uu____16572,
                                                                  (q,
                                                                   uu____16574))::[]
                                  ->
                                  let uu____16621 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____16621
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16623 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16637 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____16637
                               then
                                 let uu____16638 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1) in
                                 match uu____16638 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____16685)::(FStar_Pervasives_Native.Some
                                                   (true), uu____16686)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____16737)::(FStar_Pervasives_Native.Some
                                                   (false), uu____16738)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____16789)::(FStar_Pervasives_Native.Some
                                                   (false), uu____16790)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____16841)::(FStar_Pervasives_Native.Some
                                                   (true), uu____16842)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____16893, (arg, uu____16895))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____16896)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____16945)::(uu____16946,
                                                   (arg, uu____16948))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____16997, (arg, uu____16999))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____17000)::[]
                                     ->
                                     let uu____17049 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____17049
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____17050)::(uu____17051,
                                                   (arg, uu____17053))::[]
                                     ->
                                     let uu____17102 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____17102
                                 | (uu____17103, (p, uu____17105))::(uu____17106,
                                                                    (q,
                                                                    uu____17108))::[]
                                     ->
                                     let uu____17155 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____17155
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17157 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17171 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____17171
                                  then
                                    let uu____17172 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1) in
                                    match uu____17172 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____17219)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____17250)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17281 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17295 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____17295
                                     then
                                       match args with
                                       | (t, uu____17297)::[] ->
                                           let uu____17314 =
                                             let uu____17315 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____17315.FStar_Syntax_Syntax.n in
                                           (match uu____17314 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17318::[], body,
                                                 uu____17320)
                                                ->
                                                let uu____17347 = simp_t body in
                                                (match uu____17347 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17350 -> tm1)
                                            | uu____17353 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17355))::(t, uu____17357)::[]
                                           ->
                                           let uu____17396 =
                                             let uu____17397 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____17397.FStar_Syntax_Syntax.n in
                                           (match uu____17396 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17400::[], body,
                                                 uu____17402)
                                                ->
                                                let uu____17429 = simp_t body in
                                                (match uu____17429 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17432 -> tm1)
                                            | uu____17435 -> tm1)
                                       | uu____17436 -> tm1
                                     else
                                       (let uu____17446 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____17446
                                        then
                                          match args with
                                          | (t, uu____17448)::[] ->
                                              let uu____17465 =
                                                let uu____17466 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____17466.FStar_Syntax_Syntax.n in
                                              (match uu____17465 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17469::[], body,
                                                    uu____17471)
                                                   ->
                                                   let uu____17498 =
                                                     simp_t body in
                                                   (match uu____17498 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17501 -> tm1)
                                               | uu____17504 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17506))::(t, uu____17508)::[]
                                              ->
                                              let uu____17547 =
                                                let uu____17548 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____17548.FStar_Syntax_Syntax.n in
                                              (match uu____17547 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17551::[], body,
                                                    uu____17553)
                                                   ->
                                                   let uu____17580 =
                                                     simp_t body in
                                                   (match uu____17580 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____17583 -> tm1)
                                               | uu____17586 -> tm1)
                                          | uu____17587 -> tm1
                                        else
                                          (let uu____17597 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu____17597
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17598;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17599;_},
                                                uu____17600)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17617;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17618;_},
                                                uu____17619)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____17636 -> tm1
                                           else
                                             (let uu____17646 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1 in
                                              match uu____17646 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero,
                                                   t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____17666 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____17676;
                         FStar_Syntax_Syntax.vars = uu____17677;_},
                       args)
                      ->
                      let uu____17699 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____17699
                      then
                        let uu____17700 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        (match uu____17700 with
                         | (FStar_Pervasives_Native.Some (true), uu____17747)::
                             (uu____17748, (arg, uu____17750))::[] ->
                             maybe_auto_squash arg
                         | (uu____17799, (arg, uu____17801))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____17802)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____17851)::uu____17852::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17903::(FStar_Pervasives_Native.Some
                                         (false), uu____17904)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17955 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17969 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____17969
                         then
                           let uu____17970 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1) in
                           match uu____17970 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____18017)::uu____18018::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18069::(FStar_Pervasives_Native.Some
                                           (true), uu____18070)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____18121)::(uu____18122, (arg, uu____18124))::[]
                               -> maybe_auto_squash arg
                           | (uu____18173, (arg, uu____18175))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____18176)::[]
                               -> maybe_auto_squash arg
                           | uu____18225 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18239 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____18239
                            then
                              let uu____18240 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1) in
                              match uu____18240 with
                              | uu____18287::(FStar_Pervasives_Native.Some
                                              (true), uu____18288)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____18339)::uu____18340::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____18391)::(uu____18392,
                                                (arg, uu____18394))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18443, (p, uu____18445))::(uu____18446,
                                                                  (q,
                                                                   uu____18448))::[]
                                  ->
                                  let uu____18495 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____18495
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18497 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18511 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____18511
                               then
                                 let uu____18512 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1) in
                                 match uu____18512 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____18559)::(FStar_Pervasives_Native.Some
                                                   (true), uu____18560)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____18611)::(FStar_Pervasives_Native.Some
                                                   (false), uu____18612)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____18663)::(FStar_Pervasives_Native.Some
                                                   (false), uu____18664)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____18715)::(FStar_Pervasives_Native.Some
                                                   (true), uu____18716)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18767, (arg, uu____18769))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____18770)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____18819)::(uu____18820,
                                                   (arg, uu____18822))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18871, (arg, uu____18873))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____18874)::[]
                                     ->
                                     let uu____18923 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____18923
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____18924)::(uu____18925,
                                                   (arg, uu____18927))::[]
                                     ->
                                     let uu____18976 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____18976
                                 | (uu____18977, (p, uu____18979))::(uu____18980,
                                                                    (q,
                                                                    uu____18982))::[]
                                     ->
                                     let uu____19029 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____19029
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19031 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19045 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____19045
                                  then
                                    let uu____19046 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1) in
                                    match uu____19046 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____19093)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____19124)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19155 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19169 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____19169
                                     then
                                       match args with
                                       | (t, uu____19171)::[] ->
                                           let uu____19188 =
                                             let uu____19189 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____19189.FStar_Syntax_Syntax.n in
                                           (match uu____19188 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19192::[], body,
                                                 uu____19194)
                                                ->
                                                let uu____19221 = simp_t body in
                                                (match uu____19221 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19224 -> tm1)
                                            | uu____19227 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19229))::(t, uu____19231)::[]
                                           ->
                                           let uu____19270 =
                                             let uu____19271 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____19271.FStar_Syntax_Syntax.n in
                                           (match uu____19270 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19274::[], body,
                                                 uu____19276)
                                                ->
                                                let uu____19303 = simp_t body in
                                                (match uu____19303 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19306 -> tm1)
                                            | uu____19309 -> tm1)
                                       | uu____19310 -> tm1
                                     else
                                       (let uu____19320 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____19320
                                        then
                                          match args with
                                          | (t, uu____19322)::[] ->
                                              let uu____19339 =
                                                let uu____19340 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____19340.FStar_Syntax_Syntax.n in
                                              (match uu____19339 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19343::[], body,
                                                    uu____19345)
                                                   ->
                                                   let uu____19372 =
                                                     simp_t body in
                                                   (match uu____19372 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19375 -> tm1)
                                               | uu____19378 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19380))::(t, uu____19382)::[]
                                              ->
                                              let uu____19421 =
                                                let uu____19422 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____19422.FStar_Syntax_Syntax.n in
                                              (match uu____19421 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19425::[], body,
                                                    uu____19427)
                                                   ->
                                                   let uu____19454 =
                                                     simp_t body in
                                                   (match uu____19454 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____19457 -> tm1)
                                               | uu____19460 -> tm1)
                                          | uu____19461 -> tm1
                                        else
                                          (let uu____19471 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu____19471
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19472;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19473;_},
                                                uu____19474)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19491;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19492;_},
                                                uu____19493)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19510 -> tm1
                                           else
                                             (let uu____19520 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1 in
                                              match uu____19520 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero,
                                                   t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19540 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
                      let uu____19555 = simp_t t in
                      (match uu____19555 with
                       | FStar_Pervasives_Native.Some (true) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false) -> tm1
                       | FStar_Pervasives_Native.None -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____19558 ->
                      let uu____19581 = is_const_match tm1 in
                      (match uu____19581 with
                       | FStar_Pervasives_Native.Some (true) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None -> tm1)
                  | uu____19584 -> tm1))
and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env ->
      fun stack ->
        fun t ->
          log cfg
            (fun uu____19595 ->
               let uu____19596 = FStar_Syntax_Print.tag_of_term t in
               let uu____19597 = FStar_Syntax_Print.term_to_string t in
               let uu____19598 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____19605 =
                 let uu____19606 =
                   let uu____19609 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____19609 in
                 stack_to_string uu____19606 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____19596 uu____19597 uu____19598 uu____19605);
          (let t1 = maybe_simplify cfg env stack t in
           match stack with
           | [] -> t1
           | (Debug (tm, time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now () in
                   let uu____19640 =
                     let uu____19641 =
                       let uu____19642 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____19642 in
                     FStar_Util.string_of_int uu____19641 in
                   let uu____19647 = FStar_Syntax_Print.term_to_string tm in
                   let uu____19648 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____19640 uu____19647 uu____19648)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m, r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____19702 ->
                     let uu____19703 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 "\tSet memo %s\n" uu____19703);
                rebuild cfg env stack1 t1)
           | (Let (env', bs, lb, r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t1 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r in
               rebuild cfg env' stack1 t2
           | (Abs (env', bs, env'', lopt, r))::stack1 ->
               let bs1 = norm_binders cfg env' bs in
               let lopt1 = norm_lcomp_opt cfg env'' lopt in
               let uu____19739 =
                 let uu___172_19740 = FStar_Syntax_Util.abs bs1 t1 lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___172_19740.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___172_19740.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____19739
           | (Arg (Univ uu____19741, uu____19742, uu____19743))::uu____19744
               -> failwith "Impossible"
           | (Arg (Dummy, uu____19747, uu____19748))::uu____19749 ->
               failwith "Impossible"
           | (UnivArgs (us, r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us in
               rebuild cfg env stack1 t2
           | (Arg
               (Clos (env_arg, tm, uu____19764, uu____19765), aq, r))::stack1
               when
               let uu____19815 = head_of t1 in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____19815 ->
               let t2 =
                 let uu____19819 =
                   let uu____19820 =
                     let uu____19821 = closure_as_term cfg env_arg tm in
                     (uu____19821, aq) in
                   FStar_Syntax_Syntax.extend_app t1 uu____19820 in
                 uu____19819 FStar_Pervasives_Native.None r in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg, tm, m, uu____19827), aq, r))::stack1 ->
               (log cfg
                  (fun uu____19880 ->
                     let uu____19881 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____19881);
                if Prims.op_Negation (cfg.steps).iota
                then
                  (if (cfg.steps).hnf
                   then
                     let arg = closure_as_term cfg env_arg tm in
                     let t2 =
                       FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                         FStar_Pervasives_Native.None r in
                     rebuild cfg env_arg stack1 t2
                   else
                     (let stack2 = (App (env, t1, aq, r)) :: stack1 in
                      norm cfg env_arg stack2 tm))
                else
                  (let uu____19891 = FStar_ST.op_Bang m in
                   match uu____19891 with
                   | FStar_Pervasives_Native.None ->
                       if (cfg.steps).hnf
                       then
                         let arg = closure_as_term cfg env_arg tm in
                         let t2 =
                           FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                             FStar_Pervasives_Native.None r in
                         rebuild cfg env_arg stack1 t2
                       else
                         (let stack2 = (MemoLazy m) :: (App (env, t1, aq, r))
                            :: stack1 in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____20028, a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1, head1, aq, r))::stack' when should_reify cfg stack
               ->
               let t0 = t1 in
               let fallback msg uu____20075 =
                 log cfg
                   (fun uu____20079 ->
                      let uu____20080 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____20080);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t2) in
               let uu____20084 =
                 let uu____20085 = FStar_Syntax_Subst.compress t1 in
                 uu____20085.FStar_Syntax_Syntax.n in
               (match uu____20084 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2, FStar_Syntax_Syntax.Meta_monadic_lift
                     (msrc, mtgt, ty))
                    ->
                    let lifted =
                      let uu____20112 = closure_as_term cfg env1 ty in
                      reify_lift cfg t2 msrc mtgt uu____20112 in
                    (log cfg
                       (fun uu____20116 ->
                          let uu____20117 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____20117);
                     (let uu____20118 = FStar_List.tl stack in
                      norm cfg env1 uu____20118 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____20119);
                       FStar_Syntax_Syntax.pos = uu____20120;
                       FStar_Syntax_Syntax.vars = uu____20121;_},
                     (e, uu____20123)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____20152 when
                    (cfg.steps).primops ->
                    let uu____20167 = FStar_Syntax_Util.head_and_args t1 in
                    (match uu____20167 with
                     | (hd1, args) ->
                         let uu____20204 =
                           let uu____20205 = FStar_Syntax_Util.un_uinst hd1 in
                           uu____20205.FStar_Syntax_Syntax.n in
                         (match uu____20204 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____20209 = find_prim_step cfg fv in
                              (match uu____20209 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____20212; arity = uu____20213;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____20215;
                                     requires_binder_substitution =
                                       uu____20216;
                                     interpretation = uu____20217;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____20230 -> fallback " (3)" ())
                          | uu____20233 -> fallback " (4)" ()))
                | uu____20234 -> fallback " (2)" ())
           | (App (env1, head1, aq, r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r in
               rebuild cfg env1 stack1 t2
           | (Match (env1, branches, r))::stack1 ->
               (log cfg
                  (fun uu____20254 ->
                     let uu____20255 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____20255);
                (let scrutinee = t1 in
                 let norm_and_rebuild_match uu____20260 =
                   log cfg
                     (fun uu____20265 ->
                        let uu____20266 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____20267 =
                          let uu____20268 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____20285 ->
                                    match uu____20285 with
                                    | (p, uu____20295, uu____20296) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____20268
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____20266 uu____20267);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___91_20313 ->
                                match uu___91_20313 with
                                | FStar_TypeChecker_Env.Inlining -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only
                                    -> true
                                | uu____20314 -> false)) in
                      let uu___173_20315 = cfg in
                      {
                        steps =
                          (let uu___174_20318 = cfg.steps in
                           {
                             beta = (uu___174_20318.beta);
                             iota = (uu___174_20318.iota);
                             zeta = false;
                             weak = (uu___174_20318.weak);
                             hnf = (uu___174_20318.hnf);
                             primops = (uu___174_20318.primops);
                             no_delta_steps = (uu___174_20318.no_delta_steps);
                             unfold_until = (uu___174_20318.unfold_until);
                             unfold_only = (uu___174_20318.unfold_only);
                             unfold_attr = (uu___174_20318.unfold_attr);
                             unfold_tac = (uu___174_20318.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___174_20318.pure_subterms_within_computations);
                             simplify = (uu___174_20318.simplify);
                             erase_universes =
                               (uu___174_20318.erase_universes);
                             allow_unbound_universes =
                               (uu___174_20318.allow_unbound_universes);
                             reify_ = (uu___174_20318.reify_);
                             compress_uvars = (uu___174_20318.compress_uvars);
                             no_full_norm = (uu___174_20318.no_full_norm);
                             check_no_uvars = (uu___174_20318.check_no_uvars);
                             unmeta = (uu___174_20318.unmeta);
                             unascribe = (uu___174_20318.unascribe)
                           });
                        tcenv = (uu___173_20315.tcenv);
                        debug = (uu___173_20315.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___173_20315.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___173_20315.memoize_lazy);
                        normalize_pure_lets =
                          (uu___173_20315.normalize_pure_lets)
                      } in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____20350 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                          let uu____20371 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20431 ->
                                    fun uu____20432 ->
                                      match (uu____20431, uu____20432) with
                                      | ((pats1, env3), (p1, b)) ->
                                          let uu____20523 = norm_pat env3 p1 in
                                          (match uu____20523 with
                                           | (p2, env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____20371 with
                           | (pats1, env3) ->
                               ((let uu___175_20605 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___175_20605.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___176_20624 = x in
                            let uu____20625 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___176_20624.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___176_20624.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20625
                            } in
                          ((let uu___177_20639 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___177_20639.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___178_20650 = x in
                            let uu____20651 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___178_20650.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___178_20650.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20651
                            } in
                          ((let uu___179_20665 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___179_20665.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x, t2) ->
                          let x1 =
                            let uu___180_20681 = x in
                            let uu____20682 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___180_20681.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___180_20681.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20682
                            } in
                          let t3 = norm_or_whnf env2 t2 in
                          ((let uu___181_20689 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___181_20689.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20699 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1 ->
                                  let uu____20713 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____20713 with
                                  | (p, wopt, e) ->
                                      let uu____20733 = norm_pat env1 p in
                                      (match uu____20733 with
                                       | (p1, env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____20758 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____20758 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____20764 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____20764) in
                 let rec is_cons head1 =
                   let uu____20769 =
                     let uu____20770 = FStar_Syntax_Subst.compress head1 in
                     uu____20770.FStar_Syntax_Syntax.n in
                   match uu____20769 with
                   | FStar_Syntax_Syntax.Tm_uinst (h, uu____20774) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____20779 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20780;
                         FStar_Syntax_Syntax.fv_delta = uu____20781;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor);_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20782;
                         FStar_Syntax_Syntax.fv_delta = uu____20783;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____20784);_}
                       -> true
                   | uu____20791 -> false in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig in
                   let uu____20936 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____20936 with
                   | (head1, args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____21023 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____21062 ->
                                 let uu____21063 =
                                   let uu____21064 = is_cons head1 in
                                   Prims.op_Negation uu____21064 in
                                 FStar_Util.Inr uu____21063)
                        | FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) ->
                            let uu____21089 =
                              let uu____21090 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____21090.FStar_Syntax_Syntax.n in
                            (match uu____21089 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____21108 ->
                                 let uu____21109 =
                                   let uu____21110 = is_cons head1 in
                                   Prims.op_Negation uu____21110 in
                                 FStar_Util.Inr uu____21109))
                 and matches_args out a p =
                   match (a, p) with
                   | ([], []) -> FStar_Util.Inl out
                   | ((t2, uu____21179)::rest_a, (p1, uu____21182)::rest_p)
                       ->
                       let uu____21226 = matches_pat t2 p1 in
                       (match uu____21226 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____21275 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1, wopt, b)::rest ->
                       let uu____21381 = matches_pat scrutinee1 p1 in
                       (match uu____21381 with
                        | FStar_Util.Inr (false) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____21421 ->
                                  let uu____21422 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____21423 =
                                    let uu____21424 =
                                      FStar_List.map
                                        (fun uu____21434 ->
                                           match uu____21434 with
                                           | (uu____21439, t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s in
                                    FStar_All.pipe_right uu____21424
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21422 uu____21423);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____21470 ->
                                       match uu____21470 with
                                       | (bv, t2) ->
                                           let uu____21493 =
                                             let uu____21500 =
                                               let uu____21503 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____21503 in
                                             let uu____21504 =
                                               let uu____21505 =
                                                 let uu____21536 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2)) in
                                                 ([], t2, uu____21536, false) in
                                               Clos uu____21505 in
                                             (uu____21500, uu____21504) in
                                           uu____21493 :: env2) env1 s in
                              let uu____21653 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____21653))) in
                 if (cfg.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))
let (plugins :
  (primitive_step -> Prims.unit, Prims.unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref [] in
  let register p =
    let uu____21676 =
      let uu____21679 = FStar_ST.op_Bang plugins in p :: uu____21679 in
    FStar_ST.op_Colon_Equals plugins uu____21676 in
  let retrieve uu____21777 = FStar_ST.op_Bang plugins in (register, retrieve)
let (register_plugin : primitive_step -> Prims.unit) =
  fun p -> FStar_Pervasives_Native.fst plugins p
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____21842 -> FStar_Pervasives_Native.snd plugins ()
let (config' :
  primitive_step Prims.list ->
    step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  =
  fun psteps ->
    fun s ->
      fun e ->
        let d =
          FStar_All.pipe_right s
            (FStar_List.collect
               (fun uu___92_21875 ->
                  match uu___92_21875 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____21879 -> [])) in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____21885 -> d in
        let uu____21888 = to_fsteps s in
        let uu____21889 =
          let uu____21890 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm") in
          let uu____21891 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops") in
          let uu____21892 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380") in
          let uu____21893 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed") in
          let uu____21894 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms") in
          {
            gen = uu____21890;
            primop = uu____21891;
            b380 = uu____21892;
            norm_delayed = uu____21893;
            print_normalized = uu____21894
          } in
        let uu____21895 =
          let uu____21898 =
            let uu____21901 = retrieve_plugins () in
            FStar_List.append uu____21901 psteps in
          add_steps built_in_primitive_steps uu____21898 in
        let uu____21904 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____21906 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations) in
             Prims.op_Negation uu____21906) in
        {
          steps = uu____21888;
          tcenv = e;
          debug = uu____21889;
          delta_level = d1;
          primitive_steps = uu____21895;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____21904
        }
let (config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg) =
  fun s -> fun e -> config' [] s e
let (normalize_with_primitive_steps :
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps ->
    fun s -> fun e -> fun t -> let c = config' ps s e in norm c [] [] t
let (normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s -> fun e -> fun t -> normalize_with_primitive_steps [] s e t
let (normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s ->
    fun e ->
      fun t -> let uu____21964 = config s e in norm_comp uu____21964 [] t
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun u ->
      let uu____21977 = config [] env in norm_universe uu____21977 [] u
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun c ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env in
      let non_info t =
        let uu____21995 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____21995 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____22002 -> c
      | FStar_Syntax_Syntax.GTotal (t, uopt) when non_info t ->
          let uu___182_22021 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___182_22021.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___182_22021.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____22028 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____22028
          then
            let ct1 =
              let uu____22030 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name in
              match uu____22030 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____22037 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid in
                    if uu____22037
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags in
                  let uu___183_22041 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___183_22041.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___183_22041.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___183_22041.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___184_22043 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___184_22043.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___184_22043.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___184_22043.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___184_22043.FStar_Syntax_Syntax.flags)
                  } in
            let uu___185_22044 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___185_22044.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___185_22044.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____22046 -> c
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env ->
    fun lc ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env in
      let non_info t =
        let uu____22058 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____22058 in
      let uu____22065 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____22065
      then
        let uu____22066 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name in
        match uu____22066 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____22072 ->
                 let uu____22073 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____22073)
        | FStar_Pervasives_Native.None -> lc
      else lc
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env ->
    fun t ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____22090 =
                let uu____22095 =
                  let uu____22096 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22096 in
                (FStar_Errors.Warning_NormalizationFailure, uu____22095) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____22090);
             t) in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      let c1 =
        try
          let uu____22107 = config [AllowUnboundUniverses] env in
          norm_comp uu____22107 [] c
        with
        | e ->
            ((let uu____22120 =
                let uu____22125 =
                  let uu____22126 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22126 in
                (FStar_Errors.Warning_NormalizationFailure, uu____22125) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____22120);
             c) in
      FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1
let (normalize_refinement :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps ->
    fun env ->
      fun t0 ->
        let t = normalize (FStar_List.append steps [Beta]) env t0 in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1 in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y, phi1) ->
                   let uu____22163 =
                     let uu____22164 =
                       let uu____22171 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____22171) in
                     FStar_Syntax_Syntax.Tm_refine uu____22164 in
                   mk uu____22163 t01.FStar_Syntax_Syntax.pos
               | uu____22176 -> t2)
          | uu____22177 -> t2 in
        aux t
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      normalize
        [Primops;
        Weak;
        HNF;
        UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
        Beta] env t
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun remove ->
    fun env ->
      fun t ->
        normalize
          (FStar_List.append (if remove then [CheckNoUvars] else [])
             [Beta;
             NoDeltaSteps;
             CompressUvars;
             Exclude Zeta;
             Exclude Iota;
             NoFullNorm]) env t
let (reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env -> fun t -> reduce_or_remove_uvar_solutions false env t
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env -> fun t -> reduce_or_remove_uvar_solutions true env t
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun e ->
      fun t_e ->
        let uu____22217 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____22217 with
        | (formals, c) ->
            (match formals with
             | [] -> e
             | uu____22246 ->
                 let uu____22253 = FStar_Syntax_Util.abs_formals e in
                 (match uu____22253 with
                  | (actuals, uu____22263, uu____22264) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____22278 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____22278 with
                         | (binders, args) ->
                             let uu____22295 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____22295
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____22303 ->
          let uu____22304 = FStar_Syntax_Util.head_and_args t in
          (match uu____22304 with
           | (head1, args) ->
               let uu____22341 =
                 let uu____22342 = FStar_Syntax_Subst.compress head1 in
                 uu____22342.FStar_Syntax_Syntax.n in
               (match uu____22341 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____22345, thead) ->
                    let uu____22371 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____22371 with
                     | (formals, tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____22413 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___190_22421 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___190_22421.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___190_22421.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___190_22421.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___190_22421.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___190_22421.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___190_22421.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___190_22421.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___190_22421.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___190_22421.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___190_22421.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___190_22421.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___190_22421.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___190_22421.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___190_22421.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___190_22421.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___190_22421.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___190_22421.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___190_22421.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___190_22421.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___190_22421.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___190_22421.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___190_22421.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___190_22421.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___190_22421.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___190_22421.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___190_22421.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___190_22421.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___190_22421.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___190_22421.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___190_22421.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___190_22421.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___190_22421.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___190_22421.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____22413 with
                            | (uu____22422, ty, uu____22424) ->
                                eta_expand_with_type env t ty))
                | uu____22425 ->
                    let uu____22426 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___191_22434 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___191_22434.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___191_22434.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___191_22434.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___191_22434.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___191_22434.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___191_22434.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___191_22434.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___191_22434.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___191_22434.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___191_22434.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___191_22434.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___191_22434.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___191_22434.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___191_22434.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___191_22434.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___191_22434.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___191_22434.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___191_22434.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___191_22434.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___191_22434.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___191_22434.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___191_22434.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___191_22434.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___191_22434.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___191_22434.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___191_22434.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___191_22434.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___191_22434.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___191_22434.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___191_22434.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___191_22434.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___191_22434.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___191_22434.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____22426 with
                     | (uu____22435, ty, uu____22437) ->
                         eta_expand_with_type env t ty)))
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos in
    let t1 = FStar_Syntax_Subst.compress t in
    let elim_bv x =
      let uu___192_22494 = x in
      let uu____22495 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___192_22494.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___192_22494.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____22495
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____22498 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____22523 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____22524 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____22525 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____22526 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____22533 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____22534 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____22535 -> t1
    | FStar_Syntax_Syntax.Tm_unknown -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) ->
        let elim_rc rc =
          let uu___193_22563 = rc in
          let uu____22564 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term in
          let uu____22571 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___193_22563.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____22564;
            FStar_Syntax_Syntax.residual_flags = uu____22571
          } in
        let uu____22574 =
          let uu____22575 =
            let uu____22592 = elim_delayed_subst_binders bs in
            let uu____22599 = elim_delayed_subst_term t2 in
            let uu____22600 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____22592, uu____22599, uu____22600) in
          FStar_Syntax_Syntax.Tm_abs uu____22575 in
        mk1 uu____22574
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu____22629 =
          let uu____22630 =
            let uu____22643 = elim_delayed_subst_binders bs in
            let uu____22650 = elim_delayed_subst_comp c in
            (uu____22643, uu____22650) in
          FStar_Syntax_Syntax.Tm_arrow uu____22630 in
        mk1 uu____22629
    | FStar_Syntax_Syntax.Tm_refine (bv, phi) ->
        let uu____22663 =
          let uu____22664 =
            let uu____22671 = elim_bv bv in
            let uu____22672 = elim_delayed_subst_term phi in
            (uu____22671, uu____22672) in
          FStar_Syntax_Syntax.Tm_refine uu____22664 in
        mk1 uu____22663
    | FStar_Syntax_Syntax.Tm_app (t2, args) ->
        let uu____22695 =
          let uu____22696 =
            let uu____22711 = elim_delayed_subst_term t2 in
            let uu____22712 = elim_delayed_subst_args args in
            (uu____22711, uu____22712) in
          FStar_Syntax_Syntax.Tm_app uu____22696 in
        mk1 uu____22695
    | FStar_Syntax_Syntax.Tm_match (t2, branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___194_22776 = p in
              let uu____22777 =
                let uu____22778 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____22778 in
              {
                FStar_Syntax_Syntax.v = uu____22777;
                FStar_Syntax_Syntax.p =
                  (uu___194_22776.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___195_22780 = p in
              let uu____22781 =
                let uu____22782 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____22782 in
              {
                FStar_Syntax_Syntax.v = uu____22781;
                FStar_Syntax_Syntax.p =
                  (uu___195_22780.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
              let uu___196_22789 = p in
              let uu____22790 =
                let uu____22791 =
                  let uu____22798 = elim_bv x in
                  let uu____22799 = elim_delayed_subst_term t0 in
                  (uu____22798, uu____22799) in
                FStar_Syntax_Syntax.Pat_dot_term uu____22791 in
              {
                FStar_Syntax_Syntax.v = uu____22790;
                FStar_Syntax_Syntax.p =
                  (uu___196_22789.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
              let uu___197_22818 = p in
              let uu____22819 =
                let uu____22820 =
                  let uu____22833 =
                    FStar_List.map
                      (fun uu____22856 ->
                         match uu____22856 with
                         | (x, b) ->
                             let uu____22869 = elim_pat x in (uu____22869, b))
                      pats in
                  (fv, uu____22833) in
                FStar_Syntax_Syntax.Pat_cons uu____22820 in
              {
                FStar_Syntax_Syntax.v = uu____22819;
                FStar_Syntax_Syntax.p =
                  (uu___197_22818.FStar_Syntax_Syntax.p)
              }
          | uu____22882 -> p in
        let elim_branch uu____22904 =
          match uu____22904 with
          | (pat, wopt, t3) ->
              let uu____22930 = elim_pat pat in
              let uu____22933 =
                FStar_Util.map_opt wopt elim_delayed_subst_term in
              let uu____22936 = elim_delayed_subst_term t3 in
              (uu____22930, uu____22933, uu____22936) in
        let uu____22941 =
          let uu____22942 =
            let uu____22965 = elim_delayed_subst_term t2 in
            let uu____22966 = FStar_List.map elim_branch branches in
            (uu____22965, uu____22966) in
          FStar_Syntax_Syntax.Tm_match uu____22942 in
        mk1 uu____22941
    | FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) ->
        let elim_ascription uu____23075 =
          match uu____23075 with
          | (tc, topt) ->
              let uu____23110 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____23120 = elim_delayed_subst_term t3 in
                    FStar_Util.Inl uu____23120
                | FStar_Util.Inr c ->
                    let uu____23122 = elim_delayed_subst_comp c in
                    FStar_Util.Inr uu____23122 in
              let uu____23123 =
                FStar_Util.map_opt topt elim_delayed_subst_term in
              (uu____23110, uu____23123) in
        let uu____23132 =
          let uu____23133 =
            let uu____23160 = elim_delayed_subst_term t2 in
            let uu____23161 = elim_ascription a in
            (uu____23160, uu____23161, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____23133 in
        mk1 uu____23132
    | FStar_Syntax_Syntax.Tm_let (lbs, t2) ->
        let elim_lb lb =
          let uu___198_23206 = lb in
          let uu____23207 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp in
          let uu____23210 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___198_23206.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___198_23206.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____23207;
            FStar_Syntax_Syntax.lbeff =
              (uu___198_23206.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____23210;
            FStar_Syntax_Syntax.lbattrs =
              (uu___198_23206.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___198_23206.FStar_Syntax_Syntax.lbpos)
          } in
        let uu____23213 =
          let uu____23214 =
            let uu____23227 =
              let uu____23234 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____23234) in
            let uu____23243 = elim_delayed_subst_term t2 in
            (uu____23227, uu____23243) in
          FStar_Syntax_Syntax.Tm_let uu____23214 in
        mk1 uu____23213
    | FStar_Syntax_Syntax.Tm_uvar (uv, t2) ->
        let uu____23276 =
          let uu____23277 =
            let uu____23294 = elim_delayed_subst_term t2 in (uv, uu____23294) in
          FStar_Syntax_Syntax.Tm_uvar uu____23277 in
        mk1 uu____23276
    | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi in
        let uu____23312 =
          let uu____23313 =
            let uu____23320 = elim_delayed_subst_term tm in
            (uu____23320, qi1) in
          FStar_Syntax_Syntax.Tm_quoted uu____23313 in
        mk1 uu____23312
    | FStar_Syntax_Syntax.Tm_meta (t2, md) ->
        let uu____23327 =
          let uu____23328 =
            let uu____23335 = elim_delayed_subst_term t2 in
            let uu____23336 = elim_delayed_subst_meta md in
            (uu____23335, uu____23336) in
          FStar_Syntax_Syntax.Tm_meta uu____23328 in
        mk1 uu____23327
and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1 ->
    FStar_List.map
      (fun uu___93_23343 ->
         match uu___93_23343 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____23347 = elim_delayed_subst_term t in
             FStar_Syntax_Syntax.DECREASES uu____23347
         | f -> f) flags1
and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uopt) ->
        let uu____23368 =
          let uu____23369 =
            let uu____23378 = elim_delayed_subst_term t in
            (uu____23378, uopt) in
          FStar_Syntax_Syntax.Total uu____23369 in
        mk1 uu____23368
    | FStar_Syntax_Syntax.GTotal (t, uopt) ->
        let uu____23391 =
          let uu____23392 =
            let uu____23401 = elim_delayed_subst_term t in
            (uu____23401, uopt) in
          FStar_Syntax_Syntax.GTotal uu____23392 in
        mk1 uu____23391
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___199_23406 = ct in
          let uu____23407 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ in
          let uu____23410 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____23419 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___199_23406.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___199_23406.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____23407;
            FStar_Syntax_Syntax.effect_args = uu____23410;
            FStar_Syntax_Syntax.flags = uu____23419
          } in
        mk1 (FStar_Syntax_Syntax.Comp ct1)
and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_23422 ->
    match uu___94_23422 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____23434 = FStar_List.map elim_delayed_subst_args args in
        FStar_Syntax_Syntax.Meta_pattern uu____23434
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____23467 =
          let uu____23474 = elim_delayed_subst_term t in (m, uu____23474) in
        FStar_Syntax_Syntax.Meta_monadic uu____23467
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) ->
        let uu____23482 =
          let uu____23491 = elim_delayed_subst_term t in
          (m1, m2, uu____23491) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23482
    | m -> m
and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
    FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
      FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args ->
    FStar_List.map
      (fun uu____23514 ->
         match uu____23514 with
         | (t, q) ->
             let uu____23525 = elim_delayed_subst_term t in (uu____23525, q))
      args
and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs ->
    FStar_List.map
      (fun uu____23545 ->
         match uu____23545 with
         | (x, q) ->
             let uu____23556 =
               let uu___200_23557 = x in
               let uu____23558 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___200_23557.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___200_23557.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____23558
               } in
             (uu____23556, q)) bs
let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,
            (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
              FStar_Pervasives_Native.tuple2 Prims.list,
            (FStar_Syntax_Syntax.term,
              FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
              FStar_Util.either)
            FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun univ_names ->
      fun binders ->
        fun tc ->
          let t =
            match (binders, tc) with
            | ([], FStar_Util.Inl t) -> t
            | ([], FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____23634, FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____23640, FStar_Util.Inl t) ->
                let uu____23646 =
                  let uu____23649 =
                    let uu____23650 =
                      let uu____23663 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____23663) in
                    FStar_Syntax_Syntax.Tm_arrow uu____23650 in
                  FStar_Syntax_Syntax.mk uu____23649 in
                uu____23646 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____23667 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____23667 with
          | (univ_names1, t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = elim_delayed_subst_term t3 in
              let uu____23695 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23750 ->
                    let uu____23751 =
                      let uu____23760 =
                        let uu____23761 = FStar_Syntax_Subst.compress t4 in
                        uu____23761.FStar_Syntax_Syntax.n in
                      (uu____23760, tc) in
                    (match uu____23751 with
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inr uu____23786) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inl uu____23823) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____23862, FStar_Util.Inl uu____23863) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____23886 -> failwith "Impossible") in
              (match uu____23695 with
               | (binders1, tc1) -> (univ_names1, binders1, tc1))
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,
            (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
              FStar_Pervasives_Native.tuple2 Prims.list,
            FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun univ_names ->
      fun binders ->
        fun t ->
          let uu____23991 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____23991 with
          | (univ_names1, binders1, tc) ->
              let uu____24049 = FStar_Util.left tc in
              (univ_names1, binders1, uu____24049)
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,
            (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
              FStar_Pervasives_Native.tuple2 Prims.list,
            FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun univ_names ->
      fun binders ->
        fun c ->
          let uu____24084 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____24084 with
          | (univ_names1, binders1, tc) ->
              let uu____24144 = FStar_Util.right tc in
              (univ_names1, binders1, uu____24144)
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env ->
    fun s ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid, univ_names, binders, typ, lids, lids') ->
          let uu____24177 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____24177 with
           | (univ_names1, binders1, typ1) ->
               let uu___201_24205 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___201_24205.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___201_24205.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___201_24205.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___201_24205.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
          let uu___202_24226 = s in
          let uu____24227 =
            let uu____24228 =
              let uu____24237 = FStar_List.map (elim_uvars env) sigs in
              (uu____24237, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____24228 in
          {
            FStar_Syntax_Syntax.sigel = uu____24227;
            FStar_Syntax_Syntax.sigrng =
              (uu___202_24226.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___202_24226.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___202_24226.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___202_24226.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon
          (lid, univ_names, typ, lident, i, lids) ->
          let uu____24254 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____24254 with
           | (univ_names1, uu____24272, typ1) ->
               let uu___203_24286 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___203_24286.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___203_24286.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___203_24286.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___203_24286.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) ->
          let uu____24292 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____24292 with
           | (univ_names1, uu____24310, typ1) ->
               let uu___204_24324 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_24324.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_24324.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_24324.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_24324.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let uu____24358 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____24358 with
                    | (opening, lbunivs) ->
                        let elim t =
                          let uu____24381 =
                            let uu____24382 =
                              let uu____24383 =
                                FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env uu____24383 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24382 in
                          elim_delayed_subst_term uu____24381 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___205_24386 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___205_24386.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___205_24386.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___205_24386.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___205_24386.FStar_Syntax_Syntax.lbpos)
                        })) in
          let uu___206_24387 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___206_24387.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___206_24387.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___206_24387.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___206_24387.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___207_24399 = s in
          let uu____24400 =
            let uu____24401 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____24401 in
          {
            FStar_Syntax_Syntax.sigel = uu____24400;
            FStar_Syntax_Syntax.sigrng =
              (uu___207_24399.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___207_24399.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___207_24399.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___207_24399.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l, us, t) ->
          let uu____24405 = elim_uvars_aux_t env us [] t in
          (match uu____24405 with
           | (us1, uu____24423, t1) ->
               let uu___208_24437 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___208_24437.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___208_24437.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___208_24437.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___208_24437.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24438 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24440 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____24440 with
           | (univs1, binders, signature) ->
               let uu____24468 =
                 let uu____24477 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____24477 with
                 | (univs_opening, univs2) ->
                     let uu____24504 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____24504) in
               (match uu____24468 with
                | (univs_opening, univs_closing) ->
                    let uu____24521 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____24527 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____24528 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____24527, uu____24528) in
                    (match uu____24521 with
                     | (b_opening, b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____24550 =
                           match uu____24550 with
                           | (us, t) ->
                               let n_us = FStar_List.length us in
                               let uu____24568 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____24568 with
                                | (us1, t1) ->
                                    let uu____24579 =
                                      let uu____24584 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____24591 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____24584, uu____24591) in
                                    (match uu____24579 with
                                     | (b_opening1, b_closing1) ->
                                         let uu____24604 =
                                           let uu____24609 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____24618 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____24609, uu____24618) in
                                         (match uu____24604 with
                                          | (univs_opening1, univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____24634 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____24634 in
                                              let uu____24635 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____24635 with
                                               | (uu____24656, uu____24657,
                                                  t3) ->
                                                   let t4 =
                                                     let uu____24672 =
                                                       let uu____24673 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24673 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24672 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____24678 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____24678 with
                           | (uu____24691, uu____24692, t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____24752 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____24769 =
                               let uu____24770 =
                                 FStar_Syntax_Subst.compress body in
                               uu____24770.FStar_Syntax_Syntax.n in
                             match uu____24769 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,
                                  (FStar_Util.Inl typ,
                                   FStar_Pervasives_Native.None),
                                  FStar_Pervasives_Native.None)
                                 -> (defn, typ)
                             | uu____24829 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____24858 =
                               let uu____24859 =
                                 FStar_Syntax_Subst.compress t in
                               uu____24859.FStar_Syntax_Syntax.n in
                             match uu____24858 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars, body, uu____24880) ->
                                 let uu____24901 = destruct_action_body body in
                                 (match uu____24901 with
                                  | (defn, typ) -> (pars, defn, typ))
                             | uu____24946 ->
                                 let uu____24947 = destruct_action_body t in
                                 (match uu____24947 with
                                  | (defn, typ) -> ([], defn, typ)) in
                           let uu____24996 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____24996 with
                           | (action_univs, t) ->
                               let uu____25005 = destruct_action_typ_templ t in
                               (match uu____25005 with
                                | (action_params, action_defn, action_typ) ->
                                    let a' =
                                      let uu___209_25046 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___209_25046.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___209_25046.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      } in
                                    a') in
                         let ed1 =
                           let uu___210_25048 = ed in
                           let uu____25049 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____25050 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____25051 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____25052 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____25053 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____25054 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____25055 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____25056 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____25057 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____25058 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____25059 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____25060 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____25061 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____25062 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___210_25048.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___210_25048.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____25049;
                             FStar_Syntax_Syntax.bind_wp = uu____25050;
                             FStar_Syntax_Syntax.if_then_else = uu____25051;
                             FStar_Syntax_Syntax.ite_wp = uu____25052;
                             FStar_Syntax_Syntax.stronger = uu____25053;
                             FStar_Syntax_Syntax.close_wp = uu____25054;
                             FStar_Syntax_Syntax.assert_p = uu____25055;
                             FStar_Syntax_Syntax.assume_p = uu____25056;
                             FStar_Syntax_Syntax.null_wp = uu____25057;
                             FStar_Syntax_Syntax.trivial = uu____25058;
                             FStar_Syntax_Syntax.repr = uu____25059;
                             FStar_Syntax_Syntax.return_repr = uu____25060;
                             FStar_Syntax_Syntax.bind_repr = uu____25061;
                             FStar_Syntax_Syntax.actions = uu____25062;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___210_25048.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         let uu___211_25065 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___211_25065.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___211_25065.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___211_25065.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___211_25065.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_25082 =
            match uu___95_25082 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us, t) ->
                let uu____25109 = elim_uvars_aux_t env us [] t in
                (match uu____25109 with
                 | (us1, uu____25133, t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___212_25152 = sub_eff in
            let uu____25153 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____25156 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___212_25152.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___212_25152.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____25153;
              FStar_Syntax_Syntax.lift = uu____25156
            } in
          let uu___213_25159 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___213_25159.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___213_25159.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___213_25159.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___213_25159.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid, univ_names, binders, comp, flags1) ->
          let uu____25169 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____25169 with
           | (univ_names1, binders1, comp1) ->
               let uu___214_25203 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___214_25203.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___214_25203.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___214_25203.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___214_25203.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25214 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25215 -> s
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env -> fun t -> normalize [EraseUniverses; AllowUnboundUniverses] env t