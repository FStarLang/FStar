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
  | Unascribe[@@deriving show]
let uu___is_Beta: step -> Prims.bool =
  fun projectee  -> match projectee with | Beta  -> true | uu____22 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____26 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____30 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_Weak: step -> Prims.bool =
  fun projectee  -> match projectee with | Weak  -> true | uu____46 -> false
let uu___is_HNF: step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____50 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____54 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____58 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____62 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____66 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____71 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldOnly: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____85 -> false
let __proj__UnfoldOnly__item___0: step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldAttr: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____103 -> false
let __proj__UnfoldAttr__item___0: step -> FStar_Syntax_Syntax.attribute =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____114 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____118 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____122 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____126 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____130 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____134 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____138 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____142 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____146 -> false
let uu___is_Unmeta: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____150 -> false
let uu___is_Unascribe: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____154 -> false
type steps = step Prims.list[@@deriving show]
let cases:
  'Auu____162 'Auu____163 .
    ('Auu____163 -> 'Auu____162) ->
      'Auu____162 ->
        'Auu____163 FStar_Pervasives_Native.option -> 'Auu____162
  =
  fun f  ->
    fun d  ->
      fun uu___75_180  ->
        match uu___75_180 with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> d
type fsteps =
  {
  beta: Prims.bool;
  iota: Prims.bool;
  zeta: Prims.bool;
  weak: Prims.bool;
  hnf: Prims.bool;
  primops: Prims.bool;
  eager_unfolding: Prims.bool;
  inlining: Prims.bool;
  no_delta_steps: Prims.bool;
  unfold_until:
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option;
  unfold_only: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option;
  unfold_attr:
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option;
  unfold_tac: Prims.bool;
  pure_subterms_within_computations: Prims.bool;
  simplify: Prims.bool;
  erase_universes: Prims.bool;
  allow_unbound_universes: Prims.bool;
  reify_: Prims.bool;
  compress_uvars: Prims.bool;
  no_full_norm: Prims.bool;
  check_no_uvars: Prims.bool;
  unmeta: Prims.bool;
  unascribe: Prims.bool;}[@@deriving show]
let __proj__Mkfsteps__item__beta: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__iota: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__zeta: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__weak: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__hnf: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__primops: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__eager_unfolding: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
        unascribe = __fname__unascribe;_} -> __fname__eager_unfolding
let __proj__Mkfsteps__item__inlining: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
        unascribe = __fname__unascribe;_} -> __fname__inlining
let __proj__Mkfsteps__item__no_delta_steps: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__unfold_until:
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__unfold_only:
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__unfold_attr:
  fsteps ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__unfold_tac: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__pure_subterms_within_computations:
  fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__simplify: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__erase_universes: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__allow_unbound_universes: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__reify_: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__compress_uvars: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__no_full_norm: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__check_no_uvars: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__unmeta: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let __proj__Mkfsteps__item__unascribe: fsteps -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
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
let default_steps: fsteps =
  {
    beta = true;
    iota = true;
    zeta = true;
    weak = false;
    hnf = false;
    primops = false;
    eager_unfolding = false;
    inlining = false;
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
let rec to_fsteps: step Prims.list -> fsteps =
  fun s  ->
    let add_opt x uu___76_1161 =
      match uu___76_1161 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
      | FStar_Pervasives_Native.Some xs ->
          FStar_Pervasives_Native.Some (x :: xs) in
    let add_one1 s1 fs =
      match s1 with
      | Beta  ->
          let uu___94_1188 = fs in
          {
            beta = true;
            iota = (uu___94_1188.iota);
            zeta = (uu___94_1188.zeta);
            weak = (uu___94_1188.weak);
            hnf = (uu___94_1188.hnf);
            primops = (uu___94_1188.primops);
            eager_unfolding = (uu___94_1188.eager_unfolding);
            inlining = (uu___94_1188.inlining);
            no_delta_steps = (uu___94_1188.no_delta_steps);
            unfold_until = (uu___94_1188.unfold_until);
            unfold_only = (uu___94_1188.unfold_only);
            unfold_attr = (uu___94_1188.unfold_attr);
            unfold_tac = (uu___94_1188.unfold_tac);
            pure_subterms_within_computations =
              (uu___94_1188.pure_subterms_within_computations);
            simplify = (uu___94_1188.simplify);
            erase_universes = (uu___94_1188.erase_universes);
            allow_unbound_universes = (uu___94_1188.allow_unbound_universes);
            reify_ = (uu___94_1188.reify_);
            compress_uvars = (uu___94_1188.compress_uvars);
            no_full_norm = (uu___94_1188.no_full_norm);
            check_no_uvars = (uu___94_1188.check_no_uvars);
            unmeta = (uu___94_1188.unmeta);
            unascribe = (uu___94_1188.unascribe)
          }
      | Iota  ->
          let uu___95_1189 = fs in
          {
            beta = (uu___95_1189.beta);
            iota = true;
            zeta = (uu___95_1189.zeta);
            weak = (uu___95_1189.weak);
            hnf = (uu___95_1189.hnf);
            primops = (uu___95_1189.primops);
            eager_unfolding = (uu___95_1189.eager_unfolding);
            inlining = (uu___95_1189.inlining);
            no_delta_steps = (uu___95_1189.no_delta_steps);
            unfold_until = (uu___95_1189.unfold_until);
            unfold_only = (uu___95_1189.unfold_only);
            unfold_attr = (uu___95_1189.unfold_attr);
            unfold_tac = (uu___95_1189.unfold_tac);
            pure_subterms_within_computations =
              (uu___95_1189.pure_subterms_within_computations);
            simplify = (uu___95_1189.simplify);
            erase_universes = (uu___95_1189.erase_universes);
            allow_unbound_universes = (uu___95_1189.allow_unbound_universes);
            reify_ = (uu___95_1189.reify_);
            compress_uvars = (uu___95_1189.compress_uvars);
            no_full_norm = (uu___95_1189.no_full_norm);
            check_no_uvars = (uu___95_1189.check_no_uvars);
            unmeta = (uu___95_1189.unmeta);
            unascribe = (uu___95_1189.unascribe)
          }
      | Zeta  ->
          let uu___96_1190 = fs in
          {
            beta = (uu___96_1190.beta);
            iota = (uu___96_1190.iota);
            zeta = true;
            weak = (uu___96_1190.weak);
            hnf = (uu___96_1190.hnf);
            primops = (uu___96_1190.primops);
            eager_unfolding = (uu___96_1190.eager_unfolding);
            inlining = (uu___96_1190.inlining);
            no_delta_steps = (uu___96_1190.no_delta_steps);
            unfold_until = (uu___96_1190.unfold_until);
            unfold_only = (uu___96_1190.unfold_only);
            unfold_attr = (uu___96_1190.unfold_attr);
            unfold_tac = (uu___96_1190.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1190.pure_subterms_within_computations);
            simplify = (uu___96_1190.simplify);
            erase_universes = (uu___96_1190.erase_universes);
            allow_unbound_universes = (uu___96_1190.allow_unbound_universes);
            reify_ = (uu___96_1190.reify_);
            compress_uvars = (uu___96_1190.compress_uvars);
            no_full_norm = (uu___96_1190.no_full_norm);
            check_no_uvars = (uu___96_1190.check_no_uvars);
            unmeta = (uu___96_1190.unmeta);
            unascribe = (uu___96_1190.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___97_1191 = fs in
          {
            beta = false;
            iota = (uu___97_1191.iota);
            zeta = (uu___97_1191.zeta);
            weak = (uu___97_1191.weak);
            hnf = (uu___97_1191.hnf);
            primops = (uu___97_1191.primops);
            eager_unfolding = (uu___97_1191.eager_unfolding);
            inlining = (uu___97_1191.inlining);
            no_delta_steps = (uu___97_1191.no_delta_steps);
            unfold_until = (uu___97_1191.unfold_until);
            unfold_only = (uu___97_1191.unfold_only);
            unfold_attr = (uu___97_1191.unfold_attr);
            unfold_tac = (uu___97_1191.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1191.pure_subterms_within_computations);
            simplify = (uu___97_1191.simplify);
            erase_universes = (uu___97_1191.erase_universes);
            allow_unbound_universes = (uu___97_1191.allow_unbound_universes);
            reify_ = (uu___97_1191.reify_);
            compress_uvars = (uu___97_1191.compress_uvars);
            no_full_norm = (uu___97_1191.no_full_norm);
            check_no_uvars = (uu___97_1191.check_no_uvars);
            unmeta = (uu___97_1191.unmeta);
            unascribe = (uu___97_1191.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___98_1192 = fs in
          {
            beta = (uu___98_1192.beta);
            iota = false;
            zeta = (uu___98_1192.zeta);
            weak = (uu___98_1192.weak);
            hnf = (uu___98_1192.hnf);
            primops = (uu___98_1192.primops);
            eager_unfolding = (uu___98_1192.eager_unfolding);
            inlining = (uu___98_1192.inlining);
            no_delta_steps = (uu___98_1192.no_delta_steps);
            unfold_until = (uu___98_1192.unfold_until);
            unfold_only = (uu___98_1192.unfold_only);
            unfold_attr = (uu___98_1192.unfold_attr);
            unfold_tac = (uu___98_1192.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1192.pure_subterms_within_computations);
            simplify = (uu___98_1192.simplify);
            erase_universes = (uu___98_1192.erase_universes);
            allow_unbound_universes = (uu___98_1192.allow_unbound_universes);
            reify_ = (uu___98_1192.reify_);
            compress_uvars = (uu___98_1192.compress_uvars);
            no_full_norm = (uu___98_1192.no_full_norm);
            check_no_uvars = (uu___98_1192.check_no_uvars);
            unmeta = (uu___98_1192.unmeta);
            unascribe = (uu___98_1192.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___99_1193 = fs in
          {
            beta = (uu___99_1193.beta);
            iota = (uu___99_1193.iota);
            zeta = false;
            weak = (uu___99_1193.weak);
            hnf = (uu___99_1193.hnf);
            primops = (uu___99_1193.primops);
            eager_unfolding = (uu___99_1193.eager_unfolding);
            inlining = (uu___99_1193.inlining);
            no_delta_steps = (uu___99_1193.no_delta_steps);
            unfold_until = (uu___99_1193.unfold_until);
            unfold_only = (uu___99_1193.unfold_only);
            unfold_attr = (uu___99_1193.unfold_attr);
            unfold_tac = (uu___99_1193.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1193.pure_subterms_within_computations);
            simplify = (uu___99_1193.simplify);
            erase_universes = (uu___99_1193.erase_universes);
            allow_unbound_universes = (uu___99_1193.allow_unbound_universes);
            reify_ = (uu___99_1193.reify_);
            compress_uvars = (uu___99_1193.compress_uvars);
            no_full_norm = (uu___99_1193.no_full_norm);
            check_no_uvars = (uu___99_1193.check_no_uvars);
            unmeta = (uu___99_1193.unmeta);
            unascribe = (uu___99_1193.unascribe)
          }
      | Exclude uu____1194 -> failwith "Bad exclude"
      | Weak  ->
          let uu___100_1195 = fs in
          {
            beta = (uu___100_1195.beta);
            iota = (uu___100_1195.iota);
            zeta = (uu___100_1195.zeta);
            weak = true;
            hnf = (uu___100_1195.hnf);
            primops = (uu___100_1195.primops);
            eager_unfolding = (uu___100_1195.eager_unfolding);
            inlining = (uu___100_1195.inlining);
            no_delta_steps = (uu___100_1195.no_delta_steps);
            unfold_until = (uu___100_1195.unfold_until);
            unfold_only = (uu___100_1195.unfold_only);
            unfold_attr = (uu___100_1195.unfold_attr);
            unfold_tac = (uu___100_1195.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1195.pure_subterms_within_computations);
            simplify = (uu___100_1195.simplify);
            erase_universes = (uu___100_1195.erase_universes);
            allow_unbound_universes = (uu___100_1195.allow_unbound_universes);
            reify_ = (uu___100_1195.reify_);
            compress_uvars = (uu___100_1195.compress_uvars);
            no_full_norm = (uu___100_1195.no_full_norm);
            check_no_uvars = (uu___100_1195.check_no_uvars);
            unmeta = (uu___100_1195.unmeta);
            unascribe = (uu___100_1195.unascribe)
          }
      | HNF  ->
          let uu___101_1196 = fs in
          {
            beta = (uu___101_1196.beta);
            iota = (uu___101_1196.iota);
            zeta = (uu___101_1196.zeta);
            weak = (uu___101_1196.weak);
            hnf = true;
            primops = (uu___101_1196.primops);
            eager_unfolding = (uu___101_1196.eager_unfolding);
            inlining = (uu___101_1196.inlining);
            no_delta_steps = (uu___101_1196.no_delta_steps);
            unfold_until = (uu___101_1196.unfold_until);
            unfold_only = (uu___101_1196.unfold_only);
            unfold_attr = (uu___101_1196.unfold_attr);
            unfold_tac = (uu___101_1196.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1196.pure_subterms_within_computations);
            simplify = (uu___101_1196.simplify);
            erase_universes = (uu___101_1196.erase_universes);
            allow_unbound_universes = (uu___101_1196.allow_unbound_universes);
            reify_ = (uu___101_1196.reify_);
            compress_uvars = (uu___101_1196.compress_uvars);
            no_full_norm = (uu___101_1196.no_full_norm);
            check_no_uvars = (uu___101_1196.check_no_uvars);
            unmeta = (uu___101_1196.unmeta);
            unascribe = (uu___101_1196.unascribe)
          }
      | Primops  ->
          let uu___102_1197 = fs in
          {
            beta = (uu___102_1197.beta);
            iota = (uu___102_1197.iota);
            zeta = (uu___102_1197.zeta);
            weak = (uu___102_1197.weak);
            hnf = (uu___102_1197.hnf);
            primops = true;
            eager_unfolding = (uu___102_1197.eager_unfolding);
            inlining = (uu___102_1197.inlining);
            no_delta_steps = (uu___102_1197.no_delta_steps);
            unfold_until = (uu___102_1197.unfold_until);
            unfold_only = (uu___102_1197.unfold_only);
            unfold_attr = (uu___102_1197.unfold_attr);
            unfold_tac = (uu___102_1197.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1197.pure_subterms_within_computations);
            simplify = (uu___102_1197.simplify);
            erase_universes = (uu___102_1197.erase_universes);
            allow_unbound_universes = (uu___102_1197.allow_unbound_universes);
            reify_ = (uu___102_1197.reify_);
            compress_uvars = (uu___102_1197.compress_uvars);
            no_full_norm = (uu___102_1197.no_full_norm);
            check_no_uvars = (uu___102_1197.check_no_uvars);
            unmeta = (uu___102_1197.unmeta);
            unascribe = (uu___102_1197.unascribe)
          }
      | Eager_unfolding  ->
          let uu___103_1198 = fs in
          {
            beta = (uu___103_1198.beta);
            iota = (uu___103_1198.iota);
            zeta = (uu___103_1198.zeta);
            weak = (uu___103_1198.weak);
            hnf = (uu___103_1198.hnf);
            primops = (uu___103_1198.primops);
            eager_unfolding = true;
            inlining = (uu___103_1198.inlining);
            no_delta_steps = (uu___103_1198.no_delta_steps);
            unfold_until = (uu___103_1198.unfold_until);
            unfold_only = (uu___103_1198.unfold_only);
            unfold_attr = (uu___103_1198.unfold_attr);
            unfold_tac = (uu___103_1198.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1198.pure_subterms_within_computations);
            simplify = (uu___103_1198.simplify);
            erase_universes = (uu___103_1198.erase_universes);
            allow_unbound_universes = (uu___103_1198.allow_unbound_universes);
            reify_ = (uu___103_1198.reify_);
            compress_uvars = (uu___103_1198.compress_uvars);
            no_full_norm = (uu___103_1198.no_full_norm);
            check_no_uvars = (uu___103_1198.check_no_uvars);
            unmeta = (uu___103_1198.unmeta);
            unascribe = (uu___103_1198.unascribe)
          }
      | Inlining  ->
          let uu___104_1199 = fs in
          {
            beta = (uu___104_1199.beta);
            iota = (uu___104_1199.iota);
            zeta = (uu___104_1199.zeta);
            weak = (uu___104_1199.weak);
            hnf = (uu___104_1199.hnf);
            primops = (uu___104_1199.primops);
            eager_unfolding = (uu___104_1199.eager_unfolding);
            inlining = true;
            no_delta_steps = (uu___104_1199.no_delta_steps);
            unfold_until = (uu___104_1199.unfold_until);
            unfold_only = (uu___104_1199.unfold_only);
            unfold_attr = (uu___104_1199.unfold_attr);
            unfold_tac = (uu___104_1199.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1199.pure_subterms_within_computations);
            simplify = (uu___104_1199.simplify);
            erase_universes = (uu___104_1199.erase_universes);
            allow_unbound_universes = (uu___104_1199.allow_unbound_universes);
            reify_ = (uu___104_1199.reify_);
            compress_uvars = (uu___104_1199.compress_uvars);
            no_full_norm = (uu___104_1199.no_full_norm);
            check_no_uvars = (uu___104_1199.check_no_uvars);
            unmeta = (uu___104_1199.unmeta);
            unascribe = (uu___104_1199.unascribe)
          }
      | NoDeltaSteps  ->
          let uu___105_1200 = fs in
          {
            beta = (uu___105_1200.beta);
            iota = (uu___105_1200.iota);
            zeta = (uu___105_1200.zeta);
            weak = (uu___105_1200.weak);
            hnf = (uu___105_1200.hnf);
            primops = (uu___105_1200.primops);
            eager_unfolding = (uu___105_1200.eager_unfolding);
            inlining = (uu___105_1200.inlining);
            no_delta_steps = true;
            unfold_until = (uu___105_1200.unfold_until);
            unfold_only = (uu___105_1200.unfold_only);
            unfold_attr = (uu___105_1200.unfold_attr);
            unfold_tac = (uu___105_1200.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1200.pure_subterms_within_computations);
            simplify = (uu___105_1200.simplify);
            erase_universes = (uu___105_1200.erase_universes);
            allow_unbound_universes = (uu___105_1200.allow_unbound_universes);
            reify_ = (uu___105_1200.reify_);
            compress_uvars = (uu___105_1200.compress_uvars);
            no_full_norm = (uu___105_1200.no_full_norm);
            check_no_uvars = (uu___105_1200.check_no_uvars);
            unmeta = (uu___105_1200.unmeta);
            unascribe = (uu___105_1200.unascribe)
          }
      | UnfoldUntil d ->
          let uu___106_1202 = fs in
          {
            beta = (uu___106_1202.beta);
            iota = (uu___106_1202.iota);
            zeta = (uu___106_1202.zeta);
            weak = (uu___106_1202.weak);
            hnf = (uu___106_1202.hnf);
            primops = (uu___106_1202.primops);
            eager_unfolding = (uu___106_1202.eager_unfolding);
            inlining = (uu___106_1202.inlining);
            no_delta_steps = (uu___106_1202.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1202.unfold_only);
            unfold_attr = (uu___106_1202.unfold_attr);
            unfold_tac = (uu___106_1202.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1202.pure_subterms_within_computations);
            simplify = (uu___106_1202.simplify);
            erase_universes = (uu___106_1202.erase_universes);
            allow_unbound_universes = (uu___106_1202.allow_unbound_universes);
            reify_ = (uu___106_1202.reify_);
            compress_uvars = (uu___106_1202.compress_uvars);
            no_full_norm = (uu___106_1202.no_full_norm);
            check_no_uvars = (uu___106_1202.check_no_uvars);
            unmeta = (uu___106_1202.unmeta);
            unascribe = (uu___106_1202.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___107_1206 = fs in
          {
            beta = (uu___107_1206.beta);
            iota = (uu___107_1206.iota);
            zeta = (uu___107_1206.zeta);
            weak = (uu___107_1206.weak);
            hnf = (uu___107_1206.hnf);
            primops = (uu___107_1206.primops);
            eager_unfolding = (uu___107_1206.eager_unfolding);
            inlining = (uu___107_1206.inlining);
            no_delta_steps = (uu___107_1206.no_delta_steps);
            unfold_until = (uu___107_1206.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___107_1206.unfold_attr);
            unfold_tac = (uu___107_1206.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1206.pure_subterms_within_computations);
            simplify = (uu___107_1206.simplify);
            erase_universes = (uu___107_1206.erase_universes);
            allow_unbound_universes = (uu___107_1206.allow_unbound_universes);
            reify_ = (uu___107_1206.reify_);
            compress_uvars = (uu___107_1206.compress_uvars);
            no_full_norm = (uu___107_1206.no_full_norm);
            check_no_uvars = (uu___107_1206.check_no_uvars);
            unmeta = (uu___107_1206.unmeta);
            unascribe = (uu___107_1206.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___108_1210 = fs in
          {
            beta = (uu___108_1210.beta);
            iota = (uu___108_1210.iota);
            zeta = (uu___108_1210.zeta);
            weak = (uu___108_1210.weak);
            hnf = (uu___108_1210.hnf);
            primops = (uu___108_1210.primops);
            eager_unfolding = (uu___108_1210.eager_unfolding);
            inlining = (uu___108_1210.inlining);
            no_delta_steps = (uu___108_1210.no_delta_steps);
            unfold_until = (uu___108_1210.unfold_until);
            unfold_only = (uu___108_1210.unfold_only);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___108_1210.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1210.pure_subterms_within_computations);
            simplify = (uu___108_1210.simplify);
            erase_universes = (uu___108_1210.erase_universes);
            allow_unbound_universes = (uu___108_1210.allow_unbound_universes);
            reify_ = (uu___108_1210.reify_);
            compress_uvars = (uu___108_1210.compress_uvars);
            no_full_norm = (uu___108_1210.no_full_norm);
            check_no_uvars = (uu___108_1210.check_no_uvars);
            unmeta = (uu___108_1210.unmeta);
            unascribe = (uu___108_1210.unascribe)
          }
      | UnfoldTac  ->
          let uu___109_1211 = fs in
          {
            beta = (uu___109_1211.beta);
            iota = (uu___109_1211.iota);
            zeta = (uu___109_1211.zeta);
            weak = (uu___109_1211.weak);
            hnf = (uu___109_1211.hnf);
            primops = (uu___109_1211.primops);
            eager_unfolding = (uu___109_1211.eager_unfolding);
            inlining = (uu___109_1211.inlining);
            no_delta_steps = (uu___109_1211.no_delta_steps);
            unfold_until = (uu___109_1211.unfold_until);
            unfold_only = (uu___109_1211.unfold_only);
            unfold_attr = (uu___109_1211.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___109_1211.pure_subterms_within_computations);
            simplify = (uu___109_1211.simplify);
            erase_universes = (uu___109_1211.erase_universes);
            allow_unbound_universes = (uu___109_1211.allow_unbound_universes);
            reify_ = (uu___109_1211.reify_);
            compress_uvars = (uu___109_1211.compress_uvars);
            no_full_norm = (uu___109_1211.no_full_norm);
            check_no_uvars = (uu___109_1211.check_no_uvars);
            unmeta = (uu___109_1211.unmeta);
            unascribe = (uu___109_1211.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___110_1212 = fs in
          {
            beta = (uu___110_1212.beta);
            iota = (uu___110_1212.iota);
            zeta = (uu___110_1212.zeta);
            weak = (uu___110_1212.weak);
            hnf = (uu___110_1212.hnf);
            primops = (uu___110_1212.primops);
            eager_unfolding = (uu___110_1212.eager_unfolding);
            inlining = (uu___110_1212.inlining);
            no_delta_steps = (uu___110_1212.no_delta_steps);
            unfold_until = (uu___110_1212.unfold_until);
            unfold_only = (uu___110_1212.unfold_only);
            unfold_attr = (uu___110_1212.unfold_attr);
            unfold_tac = (uu___110_1212.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___110_1212.simplify);
            erase_universes = (uu___110_1212.erase_universes);
            allow_unbound_universes = (uu___110_1212.allow_unbound_universes);
            reify_ = (uu___110_1212.reify_);
            compress_uvars = (uu___110_1212.compress_uvars);
            no_full_norm = (uu___110_1212.no_full_norm);
            check_no_uvars = (uu___110_1212.check_no_uvars);
            unmeta = (uu___110_1212.unmeta);
            unascribe = (uu___110_1212.unascribe)
          }
      | Simplify  ->
          let uu___111_1213 = fs in
          {
            beta = (uu___111_1213.beta);
            iota = (uu___111_1213.iota);
            zeta = (uu___111_1213.zeta);
            weak = (uu___111_1213.weak);
            hnf = (uu___111_1213.hnf);
            primops = (uu___111_1213.primops);
            eager_unfolding = (uu___111_1213.eager_unfolding);
            inlining = (uu___111_1213.inlining);
            no_delta_steps = (uu___111_1213.no_delta_steps);
            unfold_until = (uu___111_1213.unfold_until);
            unfold_only = (uu___111_1213.unfold_only);
            unfold_attr = (uu___111_1213.unfold_attr);
            unfold_tac = (uu___111_1213.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1213.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___111_1213.erase_universes);
            allow_unbound_universes = (uu___111_1213.allow_unbound_universes);
            reify_ = (uu___111_1213.reify_);
            compress_uvars = (uu___111_1213.compress_uvars);
            no_full_norm = (uu___111_1213.no_full_norm);
            check_no_uvars = (uu___111_1213.check_no_uvars);
            unmeta = (uu___111_1213.unmeta);
            unascribe = (uu___111_1213.unascribe)
          }
      | EraseUniverses  ->
          let uu___112_1214 = fs in
          {
            beta = (uu___112_1214.beta);
            iota = (uu___112_1214.iota);
            zeta = (uu___112_1214.zeta);
            weak = (uu___112_1214.weak);
            hnf = (uu___112_1214.hnf);
            primops = (uu___112_1214.primops);
            eager_unfolding = (uu___112_1214.eager_unfolding);
            inlining = (uu___112_1214.inlining);
            no_delta_steps = (uu___112_1214.no_delta_steps);
            unfold_until = (uu___112_1214.unfold_until);
            unfold_only = (uu___112_1214.unfold_only);
            unfold_attr = (uu___112_1214.unfold_attr);
            unfold_tac = (uu___112_1214.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1214.pure_subterms_within_computations);
            simplify = (uu___112_1214.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___112_1214.allow_unbound_universes);
            reify_ = (uu___112_1214.reify_);
            compress_uvars = (uu___112_1214.compress_uvars);
            no_full_norm = (uu___112_1214.no_full_norm);
            check_no_uvars = (uu___112_1214.check_no_uvars);
            unmeta = (uu___112_1214.unmeta);
            unascribe = (uu___112_1214.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___113_1215 = fs in
          {
            beta = (uu___113_1215.beta);
            iota = (uu___113_1215.iota);
            zeta = (uu___113_1215.zeta);
            weak = (uu___113_1215.weak);
            hnf = (uu___113_1215.hnf);
            primops = (uu___113_1215.primops);
            eager_unfolding = (uu___113_1215.eager_unfolding);
            inlining = (uu___113_1215.inlining);
            no_delta_steps = (uu___113_1215.no_delta_steps);
            unfold_until = (uu___113_1215.unfold_until);
            unfold_only = (uu___113_1215.unfold_only);
            unfold_attr = (uu___113_1215.unfold_attr);
            unfold_tac = (uu___113_1215.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1215.pure_subterms_within_computations);
            simplify = (uu___113_1215.simplify);
            erase_universes = (uu___113_1215.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___113_1215.reify_);
            compress_uvars = (uu___113_1215.compress_uvars);
            no_full_norm = (uu___113_1215.no_full_norm);
            check_no_uvars = (uu___113_1215.check_no_uvars);
            unmeta = (uu___113_1215.unmeta);
            unascribe = (uu___113_1215.unascribe)
          }
      | Reify  ->
          let uu___114_1216 = fs in
          {
            beta = (uu___114_1216.beta);
            iota = (uu___114_1216.iota);
            zeta = (uu___114_1216.zeta);
            weak = (uu___114_1216.weak);
            hnf = (uu___114_1216.hnf);
            primops = (uu___114_1216.primops);
            eager_unfolding = (uu___114_1216.eager_unfolding);
            inlining = (uu___114_1216.inlining);
            no_delta_steps = (uu___114_1216.no_delta_steps);
            unfold_until = (uu___114_1216.unfold_until);
            unfold_only = (uu___114_1216.unfold_only);
            unfold_attr = (uu___114_1216.unfold_attr);
            unfold_tac = (uu___114_1216.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1216.pure_subterms_within_computations);
            simplify = (uu___114_1216.simplify);
            erase_universes = (uu___114_1216.erase_universes);
            allow_unbound_universes = (uu___114_1216.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___114_1216.compress_uvars);
            no_full_norm = (uu___114_1216.no_full_norm);
            check_no_uvars = (uu___114_1216.check_no_uvars);
            unmeta = (uu___114_1216.unmeta);
            unascribe = (uu___114_1216.unascribe)
          }
      | CompressUvars  ->
          let uu___115_1217 = fs in
          {
            beta = (uu___115_1217.beta);
            iota = (uu___115_1217.iota);
            zeta = (uu___115_1217.zeta);
            weak = (uu___115_1217.weak);
            hnf = (uu___115_1217.hnf);
            primops = (uu___115_1217.primops);
            eager_unfolding = (uu___115_1217.eager_unfolding);
            inlining = (uu___115_1217.inlining);
            no_delta_steps = (uu___115_1217.no_delta_steps);
            unfold_until = (uu___115_1217.unfold_until);
            unfold_only = (uu___115_1217.unfold_only);
            unfold_attr = (uu___115_1217.unfold_attr);
            unfold_tac = (uu___115_1217.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1217.pure_subterms_within_computations);
            simplify = (uu___115_1217.simplify);
            erase_universes = (uu___115_1217.erase_universes);
            allow_unbound_universes = (uu___115_1217.allow_unbound_universes);
            reify_ = (uu___115_1217.reify_);
            compress_uvars = true;
            no_full_norm = (uu___115_1217.no_full_norm);
            check_no_uvars = (uu___115_1217.check_no_uvars);
            unmeta = (uu___115_1217.unmeta);
            unascribe = (uu___115_1217.unascribe)
          }
      | NoFullNorm  ->
          let uu___116_1218 = fs in
          {
            beta = (uu___116_1218.beta);
            iota = (uu___116_1218.iota);
            zeta = (uu___116_1218.zeta);
            weak = (uu___116_1218.weak);
            hnf = (uu___116_1218.hnf);
            primops = (uu___116_1218.primops);
            eager_unfolding = (uu___116_1218.eager_unfolding);
            inlining = (uu___116_1218.inlining);
            no_delta_steps = (uu___116_1218.no_delta_steps);
            unfold_until = (uu___116_1218.unfold_until);
            unfold_only = (uu___116_1218.unfold_only);
            unfold_attr = (uu___116_1218.unfold_attr);
            unfold_tac = (uu___116_1218.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1218.pure_subterms_within_computations);
            simplify = (uu___116_1218.simplify);
            erase_universes = (uu___116_1218.erase_universes);
            allow_unbound_universes = (uu___116_1218.allow_unbound_universes);
            reify_ = (uu___116_1218.reify_);
            compress_uvars = (uu___116_1218.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___116_1218.check_no_uvars);
            unmeta = (uu___116_1218.unmeta);
            unascribe = (uu___116_1218.unascribe)
          }
      | CheckNoUvars  ->
          let uu___117_1219 = fs in
          {
            beta = (uu___117_1219.beta);
            iota = (uu___117_1219.iota);
            zeta = (uu___117_1219.zeta);
            weak = (uu___117_1219.weak);
            hnf = (uu___117_1219.hnf);
            primops = (uu___117_1219.primops);
            eager_unfolding = (uu___117_1219.eager_unfolding);
            inlining = (uu___117_1219.inlining);
            no_delta_steps = (uu___117_1219.no_delta_steps);
            unfold_until = (uu___117_1219.unfold_until);
            unfold_only = (uu___117_1219.unfold_only);
            unfold_attr = (uu___117_1219.unfold_attr);
            unfold_tac = (uu___117_1219.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1219.pure_subterms_within_computations);
            simplify = (uu___117_1219.simplify);
            erase_universes = (uu___117_1219.erase_universes);
            allow_unbound_universes = (uu___117_1219.allow_unbound_universes);
            reify_ = (uu___117_1219.reify_);
            compress_uvars = (uu___117_1219.compress_uvars);
            no_full_norm = (uu___117_1219.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___117_1219.unmeta);
            unascribe = (uu___117_1219.unascribe)
          }
      | Unmeta  ->
          let uu___118_1220 = fs in
          {
            beta = (uu___118_1220.beta);
            iota = (uu___118_1220.iota);
            zeta = (uu___118_1220.zeta);
            weak = (uu___118_1220.weak);
            hnf = (uu___118_1220.hnf);
            primops = (uu___118_1220.primops);
            eager_unfolding = (uu___118_1220.eager_unfolding);
            inlining = (uu___118_1220.inlining);
            no_delta_steps = (uu___118_1220.no_delta_steps);
            unfold_until = (uu___118_1220.unfold_until);
            unfold_only = (uu___118_1220.unfold_only);
            unfold_attr = (uu___118_1220.unfold_attr);
            unfold_tac = (uu___118_1220.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1220.pure_subterms_within_computations);
            simplify = (uu___118_1220.simplify);
            erase_universes = (uu___118_1220.erase_universes);
            allow_unbound_universes = (uu___118_1220.allow_unbound_universes);
            reify_ = (uu___118_1220.reify_);
            compress_uvars = (uu___118_1220.compress_uvars);
            no_full_norm = (uu___118_1220.no_full_norm);
            check_no_uvars = (uu___118_1220.check_no_uvars);
            unmeta = true;
            unascribe = (uu___118_1220.unascribe)
          }
      | Unascribe  ->
          let uu___119_1221 = fs in
          {
            beta = (uu___119_1221.beta);
            iota = (uu___119_1221.iota);
            zeta = (uu___119_1221.zeta);
            weak = (uu___119_1221.weak);
            hnf = (uu___119_1221.hnf);
            primops = (uu___119_1221.primops);
            eager_unfolding = (uu___119_1221.eager_unfolding);
            inlining = (uu___119_1221.inlining);
            no_delta_steps = (uu___119_1221.no_delta_steps);
            unfold_until = (uu___119_1221.unfold_until);
            unfold_only = (uu___119_1221.unfold_only);
            unfold_attr = (uu___119_1221.unfold_attr);
            unfold_tac = (uu___119_1221.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1221.pure_subterms_within_computations);
            simplify = (uu___119_1221.simplify);
            erase_universes = (uu___119_1221.erase_universes);
            allow_unbound_universes = (uu___119_1221.allow_unbound_universes);
            reify_ = (uu___119_1221.reify_);
            compress_uvars = (uu___119_1221.compress_uvars);
            no_full_norm = (uu___119_1221.no_full_norm);
            check_no_uvars = (uu___119_1221.check_no_uvars);
            unmeta = (uu___119_1221.unmeta);
            unascribe = true
          } in
    FStar_List.fold_right add_one1 s default_steps
type psc =
  {
  psc_range: FStar_Range.range;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t;}[@@deriving show]
let __proj__Mkpsc__item__psc_range: psc -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
let __proj__Mkpsc__item__psc_subst:
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
let null_psc: psc =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1253  -> []) }
let psc_range: psc -> FStar_Range.range = fun psc  -> psc.psc_range
let psc_subst: psc -> FStar_Syntax_Syntax.subst_t =
  fun psc  -> psc.psc_subst ()
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  requires_binder_substitution: Prims.bool;
  interpretation:
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option;}[@@deriving
                                                                   show]
let __proj__Mkprimitive_step__item__name: primitive_step -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
let __proj__Mkprimitive_step__item__arity: primitive_step -> Prims.int =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
let __proj__Mkprimitive_step__item__strong_reduction_ok:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
let __proj__Mkprimitive_step__item__requires_binder_substitution:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
let __proj__Mkprimitive_step__item__interpretation:
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
type closure =
  | Clos of
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
  FStar_Pervasives_Native.tuple4
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy[@@deriving show]
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____1454 -> false
let __proj__Clos__item___0:
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1556 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1567 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___77_1586  ->
    match uu___77_1586 with
    | Clos (uu____1587,t,uu____1589,uu____1590) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1635 -> "Univ"
    | Dummy  -> "dummy"
type debug_switches =
  {
  gen: Prims.bool;
  primop: Prims.bool;
  b380: Prims.bool;
  norm_delayed: Prims.bool;
  print_normalized: Prims.bool;}[@@deriving show]
let __proj__Mkdebug_switches__item__gen: debug_switches -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
let __proj__Mkdebug_switches__item__primop: debug_switches -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
let __proj__Mkdebug_switches__item__b380: debug_switches -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
let __proj__Mkdebug_switches__item__norm_delayed:
  debug_switches -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
let __proj__Mkdebug_switches__item__print_normalized:
  debug_switches -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__print_normalized
type cfg =
  {
  steps: fsteps;
  tcenv: FStar_TypeChecker_Env.env;
  debug: debug_switches;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step FStar_Util.psmap;
  strong: Prims.bool;
  memoize_lazy: Prims.bool;
  normalize_pure_lets: Prims.bool;}[@@deriving show]
let __proj__Mkcfg__item__steps: cfg -> fsteps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__tcenv
let __proj__Mkcfg__item__debug: cfg -> debug_switches =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__debug
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__delta_level
let __proj__Mkcfg__item__primitive_steps:
  cfg -> primitive_step FStar_Util.psmap =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__primitive_steps
let __proj__Mkcfg__item__strong: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__strong
let __proj__Mkcfg__item__memoize_lazy: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__memoize_lazy
let __proj__Mkcfg__item__normalize_pure_lets: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__normalize_pure_lets
let add_steps:
  primitive_step FStar_Util.psmap ->
    primitive_step Prims.list -> primitive_step FStar_Util.psmap
  =
  fun m  ->
    fun l  ->
      FStar_List.fold_right
        (fun p  ->
           fun m1  ->
             FStar_Util.psmap_add m1 (FStar_Ident.text_of_lid p.name) p) l m
let prim_from_list:
  primitive_step Prims.list -> primitive_step FStar_Util.psmap =
  fun l  ->
    let uu____1897 = FStar_Util.psmap_empty () in add_steps uu____1897 l
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list[@@deriving show]
type stack_elt =
  | Arg of (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | MemoLazy of (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  FStar_Syntax_Syntax.memo
  | Match of (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Meta of (FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Cfg of cfg
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____2041 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2077 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2113 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2182 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2224 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2280 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2320 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2352 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Cfg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2388 -> false
let __proj__Cfg__item___0: stack_elt -> cfg =
  fun projectee  -> match projectee with | Cfg _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2404 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____2429 .
    'Auu____2429 ->
      FStar_Range.range -> 'Auu____2429 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2483 = FStar_ST.op_Bang r in
          match uu____2483 with
          | FStar_Pervasives_Native.Some uu____2531 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____2585 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____2585 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___78_2592  ->
    match uu___78_2592 with
    | Arg (c,uu____2594,uu____2595) ->
        let uu____2596 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____2596
    | MemoLazy uu____2597 -> "MemoLazy"
    | Abs (uu____2604,bs,uu____2606,uu____2607,uu____2608) ->
        let uu____2613 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____2613
    | UnivArgs uu____2618 -> "UnivArgs"
    | Match uu____2625 -> "Match"
    | App (uu____2632,t,uu____2634,uu____2635) ->
        let uu____2636 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____2636
    | Meta (m,uu____2638) -> "Meta"
    | Let uu____2639 -> "Let"
    | Cfg uu____2648 -> "Cfg"
    | Debug (t,uu____2650) ->
        let uu____2651 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____2651
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____2659 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____2659 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else ()
let is_empty: 'Auu____2690 . 'Auu____2690 Prims.list -> Prims.bool =
  fun uu___79_2696  ->
    match uu___79_2696 with | [] -> true | uu____2699 -> false
let lookup_bvar:
  'Auu____2706 'Auu____2707 .
    ('Auu____2707,'Auu____2706) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2706
  =
  fun env  ->
    fun x  ->
      try
        let uu____2731 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____2731
      with
      | uu____2744 ->
          let uu____2745 =
            let uu____2746 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____2746 in
          failwith uu____2745
let downgrade_ghost_effect_name:
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun l  ->
    if FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid
      then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid
        then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
        else FStar_Pervasives_Native.None
let norm_universe:
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____2783 =
            FStar_List.fold_left
              (fun uu____2809  ->
                 fun u1  ->
                   match uu____2809 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2834 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____2834 with
                        | (k_u,n1) ->
                            let uu____2849 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____2849
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____2783 with
          | (uu____2867,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2892 =
                   let uu____2893 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____2893 in
                 match uu____2892 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2911 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2919 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2925 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2934 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2943 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2950 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2950 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2967 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2967 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2975 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2983 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2983 with
                                  | (uu____2988,m) -> n1 <= m)) in
                        if uu____2975 then rest1 else us1
                    | uu____2993 -> us1)
               | uu____2998 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3002 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3002 in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3006 = aux u in
           match uu____3006 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
let rec closure_as_term:
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____3110  ->
             let uu____3111 = FStar_Syntax_Print.tag_of_term t in
             let uu____3112 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3111
               uu____3112);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3119 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3121 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3146 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3147 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3148 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3149 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3166 =
                      let uu____3167 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____3168 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3167 uu____3168 in
                    failwith uu____3166
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3171 =
                    let uu____3172 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____3172 in
                  mk uu____3171 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3179 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3179
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3181 = lookup_bvar env x in
                  (match uu____3181 with
                   | Univ uu____3184 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3187,uu____3188) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3300 = closures_as_binders_delayed cfg env bs in
                  (match uu____3300 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____3328 =
                         let uu____3329 =
                           let uu____3346 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____3346) in
                         FStar_Syntax_Syntax.Tm_abs uu____3329 in
                       mk uu____3328 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3377 = closures_as_binders_delayed cfg env bs in
                  (match uu____3377 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3419 =
                    let uu____3430 =
                      let uu____3437 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____3437] in
                    closures_as_binders_delayed cfg env uu____3430 in
                  (match uu____3419 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____3455 =
                         let uu____3456 =
                           let uu____3463 =
                             let uu____3464 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____3464
                               FStar_Pervasives_Native.fst in
                           (uu____3463, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____3456 in
                       mk uu____3455 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3555 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____3555
                    | FStar_Util.Inr c ->
                        let uu____3569 = close_comp cfg env c in
                        FStar_Util.Inr uu____3569 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____3585 =
                    let uu____3586 =
                      let uu____3613 = closure_as_term_delayed cfg env t11 in
                      (uu____3613, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3586 in
                  mk uu____3585 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3664 =
                    let uu____3665 =
                      let uu____3672 = closure_as_term_delayed cfg env t' in
                      let uu____3675 =
                        let uu____3676 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____3676 in
                      (uu____3672, uu____3675) in
                    FStar_Syntax_Syntax.Tm_meta uu____3665 in
                  mk uu____3664 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3736 =
                    let uu____3737 =
                      let uu____3744 = closure_as_term_delayed cfg env t' in
                      let uu____3747 =
                        let uu____3748 =
                          let uu____3755 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____3755) in
                        FStar_Syntax_Syntax.Meta_monadic uu____3748 in
                      (uu____3744, uu____3747) in
                    FStar_Syntax_Syntax.Tm_meta uu____3737 in
                  mk uu____3736 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3774 =
                    let uu____3775 =
                      let uu____3782 = closure_as_term_delayed cfg env t' in
                      let uu____3785 =
                        let uu____3786 =
                          let uu____3795 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____3795) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3786 in
                      (uu____3782, uu____3785) in
                    FStar_Syntax_Syntax.Tm_meta uu____3775 in
                  mk uu____3774 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3808 =
                    let uu____3809 =
                      let uu____3816 = closure_as_term_delayed cfg env t' in
                      (uu____3816, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____3809 in
                  mk uu____3808 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3856  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____3875 =
                    let uu____3886 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____3886
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____3905 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___124_3917 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_3917.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_3917.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3905)) in
                  (match uu____3875 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___125_3933 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___125_3933.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___125_3933.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___125_3933.FStar_Syntax_Syntax.lbattrs)
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3944,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____4003  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____4028 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____4028
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4048  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____4070 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____4070
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___126_4082 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___126_4082.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___126_4082.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___127_4083 = lb in
                    let uu____4084 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___127_4083.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___127_4083.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4084;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___127_4083.FStar_Syntax_Syntax.lbattrs)
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4114  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____4203 =
                    match uu____4203 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4258 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4279 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4339  ->
                                        fun uu____4340  ->
                                          match (uu____4339, uu____4340) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4431 =
                                                norm_pat env3 p1 in
                                              (match uu____4431 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____4279 with
                               | (pats1,env3) ->
                                   ((let uu___128_4513 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___128_4513.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___129_4532 = x in
                                let uu____4533 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4532.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4532.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4533
                                } in
                              ((let uu___130_4547 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4547.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___131_4558 = x in
                                let uu____4559 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4558.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4558.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4559
                                } in
                              ((let uu___132_4573 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4573.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___133_4589 = x in
                                let uu____4590 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___133_4589.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___133_4589.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4590
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___134_4597 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___134_4597.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____4600 = norm_pat env1 pat in
                        (match uu____4600 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4629 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____4629 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____4635 =
                    let uu____4636 =
                      let uu____4659 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____4659) in
                    FStar_Syntax_Syntax.Tm_match uu____4636 in
                  mk uu____4635 t1.FStar_Syntax_Syntax.pos))
and closure_as_term_delayed:
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> t
        | uu____4745 -> closure_as_term cfg env t
and closures_as_args_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> args
        | uu____4771 ->
            FStar_List.map
              (fun uu____4788  ->
                 match uu____4788 with
                 | (x,imp) ->
                     let uu____4807 = closure_as_term_delayed cfg env x in
                     (uu____4807, imp)) args
and closures_as_binders_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____4821 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4870  ->
                  fun uu____4871  ->
                    match (uu____4870, uu____4871) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___135_4941 = b in
                          let uu____4942 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___135_4941.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___135_4941.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4942
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____4821 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
and close_comp:
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> c
        | uu____5035 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5048 = closure_as_term_delayed cfg env t in
                 let uu____5049 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____5048 uu____5049
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5062 = closure_as_term_delayed cfg env t in
                 let uu____5063 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5062 uu____5063
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
                        (fun uu___80_5089  ->
                           match uu___80_5089 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5093 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____5093
                           | f -> f)) in
                 let uu____5097 =
                   let uu___136_5098 = c1 in
                   let uu____5099 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5099;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___136_5098.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____5097)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___81_5109  ->
            match uu___81_5109 with
            | FStar_Syntax_Syntax.DECREASES uu____5110 -> false
            | uu____5113 -> true))
and close_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___82_5131  ->
                      match uu___82_5131 with
                      | FStar_Syntax_Syntax.DECREASES uu____5132 -> false
                      | uu____5135 -> true)) in
            let rc1 =
              let uu___137_5137 = rc in
              let uu____5138 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___137_5137.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5138;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____5145 -> lopt
let built_in_primitive_steps: primitive_step FStar_Util.psmap =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_int_safe in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_bool_safe in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_char_safe in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_string_safe in
  let arg_as_list a u a =
    let uu____5230 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5230 in
  let arg_as_bounded_int uu____5258 =
    match uu____5258 with
    | (a,uu____5270) ->
        let uu____5277 =
          let uu____5278 = FStar_Syntax_Subst.compress a in
          uu____5278.FStar_Syntax_Syntax.n in
        (match uu____5277 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5288;
                FStar_Syntax_Syntax.vars = uu____5289;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5291;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5292;_},uu____5293)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5332 =
               let uu____5337 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____5337) in
             FStar_Pervasives_Native.Some uu____5332
         | uu____5342 -> FStar_Pervasives_Native.None) in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5382 = f a in FStar_Pervasives_Native.Some uu____5382
    | uu____5383 -> FStar_Pervasives_Native.None in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5431 = f a0 a1 in FStar_Pervasives_Native.Some uu____5431
    | uu____5432 -> FStar_Pervasives_Native.None in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5474 = FStar_List.map as_a args in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5474)) a416 a417 a418 a419 a420 in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5523 = FStar_List.map as_a args in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5523)) a423 a424 a425 a426 a427 in
  let as_primitive_step uu____5547 =
    match uu____5547 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        } in
  let unary_int_op f =
    unary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5595 = f x in
                   FStar_Syntax_Embeddings.embed_int r uu____5595)) a429 a430) in
  let binary_int_op f =
    binary_op () (fun a431  -> (Obj.magic arg_as_int) a431)
      (fun a432  ->
         fun a433  ->
           fun a434  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5623 = f x y in
                       FStar_Syntax_Embeddings.embed_int r uu____5623)) a432
               a433 a434) in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5644 = f x in
                   FStar_Syntax_Embeddings.embed_bool r uu____5644)) a436
             a437) in
  let binary_bool_op f =
    binary_op () (fun a438  -> (Obj.magic arg_as_bool) a438)
      (fun a439  ->
         fun a440  ->
           fun a441  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5672 = f x y in
                       FStar_Syntax_Embeddings.embed_bool r uu____5672)) a439
               a440 a441) in
  let binary_string_op f =
    binary_op () (fun a442  -> (Obj.magic arg_as_string) a442)
      (fun a443  ->
         fun a444  ->
           fun a445  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5700 = f x y in
                       FStar_Syntax_Embeddings.embed_string r uu____5700))
               a443 a444 a445) in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5808 =
          let uu____5817 = as_a a in
          let uu____5820 = as_b b in (uu____5817, uu____5820) in
        (match uu____5808 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5835 =
               let uu____5836 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____5836 in
             FStar_Pervasives_Native.Some uu____5835
         | uu____5837 -> FStar_Pervasives_Native.None)
    | uu____5846 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____5860 =
        let uu____5861 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5861 in
      mk uu____5860 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5871 =
      let uu____5874 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5874 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5871 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____5906 =
      let uu____5907 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____5907 in
    FStar_Syntax_Embeddings.embed_int rng uu____5906 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5925 = arg_as_string a1 in
        (match uu____5925 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5931 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2) in
             (match uu____5931 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5944 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____5944
              | uu____5945 -> FStar_Pervasives_Native.None)
         | uu____5950 -> FStar_Pervasives_Native.None)
    | uu____5953 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5963 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____5963 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____5987 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5998 =
          let uu____6019 = arg_as_string fn in
          let uu____6022 = arg_as_int from_line in
          let uu____6025 = arg_as_int from_col in
          let uu____6028 = arg_as_int to_line in
          let uu____6031 = arg_as_int to_col in
          (uu____6019, uu____6022, uu____6025, uu____6028, uu____6031) in
        (match uu____5998 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6062 =
                 let uu____6063 = FStar_BigInt.to_int_fs from_l in
                 let uu____6064 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____6063 uu____6064 in
               let uu____6065 =
                 let uu____6066 = FStar_BigInt.to_int_fs to_l in
                 let uu____6067 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____6066 uu____6067 in
               FStar_Range.mk_range fn1 uu____6062 uu____6065 in
             let uu____6068 = term_of_range r in
             FStar_Pervasives_Native.Some uu____6068
         | uu____6073 -> FStar_Pervasives_Native.None)
    | uu____6094 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____6121)::(a1,uu____6123)::(a2,uu____6125)::[] ->
        let uu____6162 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6162 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6175 -> FStar_Pervasives_Native.None)
    | uu____6176 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____6203)::[] -> FStar_Pervasives_Native.Some a1
    | uu____6212 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____6236 =
      let uu____6251 =
        let uu____6266 =
          let uu____6281 =
            let uu____6296 =
              let uu____6311 =
                let uu____6326 =
                  let uu____6341 =
                    let uu____6356 =
                      let uu____6371 =
                        let uu____6386 =
                          let uu____6401 =
                            let uu____6416 =
                              let uu____6431 =
                                let uu____6446 =
                                  let uu____6461 =
                                    let uu____6476 =
                                      let uu____6491 =
                                        let uu____6506 =
                                          let uu____6521 =
                                            let uu____6536 =
                                              let uu____6551 =
                                                let uu____6564 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"] in
                                                (uu____6564,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a446  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a446)
                                                     (fun a447  ->
                                                        fun a448  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a447 a448))) in
                                              let uu____6571 =
                                                let uu____6586 =
                                                  let uu____6599 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"] in
                                                  (uu____6599,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a449  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a449)
                                                       (fun a450  ->
                                                          fun a451  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a450 a451))) in
                                                let uu____6606 =
                                                  let uu____6621 =
                                                    let uu____6636 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"] in
                                                    (uu____6636,
                                                      (Prims.parse_int "2"),
                                                      string_concat') in
                                                  let uu____6645 =
                                                    let uu____6662 =
                                                      let uu____6677 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"] in
                                                      (uu____6677,
                                                        (Prims.parse_int "5"),
                                                        mk_range1) in
                                                    let uu____6686 =
                                                      let uu____6703 =
                                                        let uu____6722 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"] in
                                                        (uu____6722,
                                                          (Prims.parse_int
                                                             "1"), idstep) in
                                                      [uu____6703] in
                                                    uu____6662 :: uu____6686 in
                                                  uu____6621 :: uu____6645 in
                                                uu____6586 :: uu____6606 in
                                              uu____6551 :: uu____6571 in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6536 in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6521 in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a452  ->
                                                (Obj.magic arg_as_string)
                                                  a452)
                                             (fun a453  ->
                                                fun a454  ->
                                                  fun a455  ->
                                                    (Obj.magic
                                                       string_compare') a453
                                                      a454 a455)))
                                          :: uu____6506 in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a456  ->
                                              (Obj.magic arg_as_bool) a456)
                                           (fun a457  ->
                                              fun a458  ->
                                                (Obj.magic string_of_bool1)
                                                  a457 a458)))
                                        :: uu____6491 in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a459  ->
                                            (Obj.magic arg_as_int) a459)
                                         (fun a460  ->
                                            fun a461  ->
                                              (Obj.magic string_of_int1) a460
                                                a461)))
                                      :: uu____6476 in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a462  ->
                                          (Obj.magic arg_as_int) a462)
                                       (fun a463  ->
                                          (Obj.magic arg_as_char) a463)
                                       (fun a464  ->
                                          fun a465  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a464 a465)
                                       (fun a466  ->
                                          fun a467  ->
                                            fun a468  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____6939 =
                                                          FStar_BigInt.to_int_fs
                                                            x in
                                                        FStar_String.make
                                                          uu____6939 y)) a466
                                                a467 a468)))
                                    :: uu____6461 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6446 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6431 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6416 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6401 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6386 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6371 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a469  -> (Obj.magic arg_as_int) a469)
                         (fun a470  ->
                            fun a471  ->
                              fun a472  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____7106 =
                                            FStar_BigInt.ge_big_int x y in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7106)) a470 a471 a472)))
                      :: uu____6356 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a473  -> (Obj.magic arg_as_int) a473)
                       (fun a474  ->
                          fun a475  ->
                            fun a476  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____7132 =
                                          FStar_BigInt.gt_big_int x y in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7132)) a474 a475 a476)))
                    :: uu____6341 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a477  -> (Obj.magic arg_as_int) a477)
                     (fun a478  ->
                        fun a479  ->
                          fun a480  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7158 =
                                        FStar_BigInt.le_big_int x y in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7158)) a478 a479 a480)))
                  :: uu____6326 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a481  -> (Obj.magic arg_as_int) a481)
                   (fun a482  ->
                      fun a483  ->
                        fun a484  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7184 =
                                      FStar_BigInt.lt_big_int x y in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7184)) a482 a483 a484)))
                :: uu____6311 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6296 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6281 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6266 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6251 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6236 in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____7337 =
        let uu____7338 =
          let uu____7339 = FStar_Syntax_Syntax.as_arg c in [uu____7339] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7338 in
      uu____7337 FStar_Pervasives_Native.None r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7389 =
                let uu____7402 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                (uu____7402, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7418  ->
                                    fun uu____7419  ->
                                      match (uu____7418, uu____7419) with
                                      | ((int_to_t1,x),(uu____7438,y)) ->
                                          let uu____7448 =
                                            FStar_BigInt.add_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____7448)) a486 a487 a488))) in
              let uu____7449 =
                let uu____7464 =
                  let uu____7477 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  (uu____7477, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7493  ->
                                      fun uu____7494  ->
                                        match (uu____7493, uu____7494) with
                                        | ((int_to_t1,x),(uu____7513,y)) ->
                                            let uu____7523 =
                                              FStar_BigInt.sub_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____7523)) a490 a491 a492))) in
                let uu____7524 =
                  let uu____7539 =
                    let uu____7552 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    (uu____7552, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7568  ->
                                        fun uu____7569  ->
                                          match (uu____7568, uu____7569) with
                                          | ((int_to_t1,x),(uu____7588,y)) ->
                                              let uu____7598 =
                                                FStar_BigInt.mult_big_int x y in
                                              int_as_bounded r int_to_t1
                                                uu____7598)) a494 a495 a496))) in
                  let uu____7599 =
                    let uu____7614 =
                      let uu____7627 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      (uu____7627, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7639  ->
                                        match uu____7639 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499))) in
                    [uu____7614] in
                  uu____7539 :: uu____7599 in
                uu____7464 :: uu____7524 in
              uu____7389 :: uu____7449)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7753 =
                let uu____7766 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                (uu____7766, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7782  ->
                                    fun uu____7783  ->
                                      match (uu____7782, uu____7783) with
                                      | ((int_to_t1,x),(uu____7802,y)) ->
                                          let uu____7812 =
                                            FStar_BigInt.div_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____7812)) a501 a502 a503))) in
              let uu____7813 =
                let uu____7828 =
                  let uu____7841 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  (uu____7841, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7857  ->
                                      fun uu____7858  ->
                                        match (uu____7857, uu____7858) with
                                        | ((int_to_t1,x),(uu____7877,y)) ->
                                            let uu____7887 =
                                              FStar_BigInt.mod_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____7887)) a505 a506 a507))) in
                [uu____7828] in
              uu____7753 :: uu____7813)) in
    FStar_List.append add_sub_mul_v div_mod_unsigned in
  let uu____7936 =
    FStar_List.map as_primitive_step
      (FStar_List.append basic_ops bounded_arith_ops) in
  FStar_All.pipe_left prim_from_list uu____7936
let equality_ops: primitive_step FStar_Util.psmap =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____7984)::(a1,uu____7986)::(a2,uu____7988)::[] ->
        let uu____8025 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____8025 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___138_8031 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_8031.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___138_8031.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8035 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8035.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8035.FStar_Syntax_Syntax.vars)
                })
         | uu____8036 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8038)::uu____8039::(a1,uu____8041)::(a2,uu____8043)::[] ->
        let uu____8092 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____8092 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___138_8098 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_8098.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___138_8098.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8102 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8102.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8102.FStar_Syntax_Syntax.vars)
                })
         | uu____8103 -> FStar_Pervasives_Native.None)
    | uu____8104 -> failwith "Unexpected number of arguments" in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  prim_from_list [propositional_equality; hetero_propositional_equality]
let unembed_binder:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____8123 =
        let uu____8124 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____8124 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____8123
    with | uu____8130 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____8134 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8134) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8194  ->
           fun subst1  ->
             match uu____8194 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8235,uu____8236)) ->
                      let uu____8295 = b in
                      (match uu____8295 with
                       | (bv,uu____8303) ->
                           let uu____8304 =
                             let uu____8305 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____8305 in
                           if uu____8304
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____8310 = unembed_binder term1 in
                              match uu____8310 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8317 =
                                      let uu___142_8318 = bv in
                                      let uu____8319 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___142_8318.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___142_8318.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8319
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____8317 in
                                  let b_for_x =
                                    let uu____8323 =
                                      let uu____8330 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8330) in
                                    FStar_Syntax_Syntax.NT uu____8323 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___83_8339  ->
                                         match uu___83_8339 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8340,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8342;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8343;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8348 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____8349 -> subst1)) env []
let reduce_primops:
  'Auu____8366 'Auu____8367 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8367) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8366 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8409 = FStar_Syntax_Util.head_and_args tm in
             match uu____8409 with
             | (head1,args) ->
                 let uu____8446 =
                   let uu____8447 = FStar_Syntax_Util.un_uinst head1 in
                   uu____8447.FStar_Syntax_Syntax.n in
                 (match uu____8446 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8451 =
                        FStar_Util.psmap_try_find cfg.primitive_steps
                          (FStar_Ident.text_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                      (match uu____8451 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8466  ->
                                   let uu____8467 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____8468 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____8475 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8467 uu____8468 uu____8475);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8480  ->
                                   let uu____8481 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8481);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8484  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____8486 =
                                 prim_step.interpretation psc args in
                               match uu____8486 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8492  ->
                                         let uu____8493 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8493);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8499  ->
                                         let uu____8500 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____8501 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8500 uu____8501);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8502 ->
                           (log_primops cfg
                              (fun uu____8506  ->
                                 let uu____8507 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8507);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8511  ->
                            let uu____8512 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8512);
                       (match args with
                        | (a1,uu____8514)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8531 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8543  ->
                            let uu____8544 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8544);
                       (match args with
                        | (t,uu____8546)::(r,uu____8548)::[] ->
                            let uu____8575 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____8575 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___143_8579 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___143_8579.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___143_8579.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8582 -> tm))
                  | uu____8591 -> tm))
let reduce_equality:
  'Auu____8596 'Auu____8597 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8597) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8596 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___144_8635 = cfg in
         {
           steps =
             (let uu___145_8638 = default_steps in
              {
                beta = (uu___145_8638.beta);
                iota = (uu___145_8638.iota);
                zeta = (uu___145_8638.zeta);
                weak = (uu___145_8638.weak);
                hnf = (uu___145_8638.hnf);
                primops = true;
                eager_unfolding = (uu___145_8638.eager_unfolding);
                inlining = (uu___145_8638.inlining);
                no_delta_steps = (uu___145_8638.no_delta_steps);
                unfold_until = (uu___145_8638.unfold_until);
                unfold_only = (uu___145_8638.unfold_only);
                unfold_attr = (uu___145_8638.unfold_attr);
                unfold_tac = (uu___145_8638.unfold_tac);
                pure_subterms_within_computations =
                  (uu___145_8638.pure_subterms_within_computations);
                simplify = (uu___145_8638.simplify);
                erase_universes = (uu___145_8638.erase_universes);
                allow_unbound_universes =
                  (uu___145_8638.allow_unbound_universes);
                reify_ = (uu___145_8638.reify_);
                compress_uvars = (uu___145_8638.compress_uvars);
                no_full_norm = (uu___145_8638.no_full_norm);
                check_no_uvars = (uu___145_8638.check_no_uvars);
                unmeta = (uu___145_8638.unmeta);
                unascribe = (uu___145_8638.unascribe)
              });
           tcenv = (uu___144_8635.tcenv);
           debug = (uu___144_8635.debug);
           delta_level = (uu___144_8635.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___144_8635.strong);
           memoize_lazy = (uu___144_8635.memoize_lazy);
           normalize_pure_lets = (uu___144_8635.normalize_pure_lets)
         }) tm
let maybe_simplify_aux:
  'Auu____8645 'Auu____8646 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8646) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8645 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____8688 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify in
          if uu____8688
          then tm1
          else
            (let w t =
               let uu___146_8700 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___146_8700.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___146_8700.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8716;
                      FStar_Syntax_Syntax.vars = uu____8717;_},uu____8718)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8725;
                      FStar_Syntax_Syntax.vars = uu____8726;_},uu____8727)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____8733 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____8738 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____8738
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____8759 =
                 match uu____8759 with
                 | (t1,q) ->
                     let uu____8772 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____8772 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____8800 -> (t1, q)) in
               let uu____8809 = FStar_Syntax_Util.head_and_args t in
               match uu____8809 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____8906;
                         FStar_Syntax_Syntax.vars = uu____8907;_},uu____8908);
                    FStar_Syntax_Syntax.pos = uu____8909;
                    FStar_Syntax_Syntax.vars = uu____8910;_},args)
                 ->
                 let uu____8936 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8936
                 then
                   let uu____8937 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8937 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8992)::
                        (uu____8993,(arg,uu____8995))::[] ->
                        maybe_auto_squash arg
                    | (uu____9060,(arg,uu____9062))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9063)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9128)::uu____9129::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9192::(FStar_Pervasives_Native.Some (false
                                   ),uu____9193)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9256 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9272 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9272
                    then
                      let uu____9273 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9273 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9328)::uu____9329::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9392::(FStar_Pervasives_Native.Some (true
                                     ),uu____9393)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9456)::
                          (uu____9457,(arg,uu____9459))::[] ->
                          maybe_auto_squash arg
                      | (uu____9524,(arg,uu____9526))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9527)::[]
                          -> maybe_auto_squash arg
                      | uu____9592 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9608 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9608
                       then
                         let uu____9609 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9609 with
                         | uu____9664::(FStar_Pervasives_Native.Some (true
                                        ),uu____9665)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9728)::uu____9729::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9792)::
                             (uu____9793,(arg,uu____9795))::[] ->
                             maybe_auto_squash arg
                         | (uu____9860,(p,uu____9862))::(uu____9863,(q,uu____9865))::[]
                             ->
                             let uu____9930 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9930
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9932 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9948 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9948
                          then
                            let uu____9949 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9949 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10004)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10043)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10082 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10098 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10098
                             then
                               match args with
                               | (t,uu____10100)::[] ->
                                   let uu____10117 =
                                     let uu____10118 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10118.FStar_Syntax_Syntax.n in
                                   (match uu____10117 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10121::[],body,uu____10123) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10150 -> tm1)
                                    | uu____10153 -> tm1)
                               | (uu____10154,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10155))::
                                   (t,uu____10157)::[] ->
                                   let uu____10196 =
                                     let uu____10197 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10197.FStar_Syntax_Syntax.n in
                                   (match uu____10196 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10200::[],body,uu____10202) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10229 -> tm1)
                                    | uu____10232 -> tm1)
                               | uu____10233 -> tm1
                             else
                               (let uu____10243 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10243
                                then
                                  match args with
                                  | (t,uu____10245)::[] ->
                                      let uu____10262 =
                                        let uu____10263 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10263.FStar_Syntax_Syntax.n in
                                      (match uu____10262 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10266::[],body,uu____10268)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10295 -> tm1)
                                       | uu____10298 -> tm1)
                                  | (uu____10299,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10300))::(t,uu____10302)::[] ->
                                      let uu____10341 =
                                        let uu____10342 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10342.FStar_Syntax_Syntax.n in
                                      (match uu____10341 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10345::[],body,uu____10347)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10374 -> tm1)
                                       | uu____10377 -> tm1)
                                  | uu____10378 -> tm1
                                else
                                  (let uu____10388 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10388
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10389;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10390;_},uu____10391)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10408;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10409;_},uu____10410)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10427 -> tm1
                                   else
                                     (let uu____10437 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10437 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10457 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____10467;
                    FStar_Syntax_Syntax.vars = uu____10468;_},args)
                 ->
                 let uu____10490 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____10490
                 then
                   let uu____10491 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____10491 with
                    | (FStar_Pervasives_Native.Some (true ),uu____10546)::
                        (uu____10547,(arg,uu____10549))::[] ->
                        maybe_auto_squash arg
                    | (uu____10614,(arg,uu____10616))::(FStar_Pervasives_Native.Some
                                                        (true ),uu____10617)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____10682)::uu____10683::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10746::(FStar_Pervasives_Native.Some (false
                                    ),uu____10747)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10810 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____10826 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____10826
                    then
                      let uu____10827 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____10827 with
                      | (FStar_Pervasives_Native.Some (true ),uu____10882)::uu____10883::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____10946::(FStar_Pervasives_Native.Some (true
                                      ),uu____10947)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____11010)::
                          (uu____11011,(arg,uu____11013))::[] ->
                          maybe_auto_squash arg
                      | (uu____11078,(arg,uu____11080))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____11081)::[]
                          -> maybe_auto_squash arg
                      | uu____11146 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____11162 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____11162
                       then
                         let uu____11163 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____11163 with
                         | uu____11218::(FStar_Pervasives_Native.Some (true
                                         ),uu____11219)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____11282)::uu____11283::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____11346)::
                             (uu____11347,(arg,uu____11349))::[] ->
                             maybe_auto_squash arg
                         | (uu____11414,(p,uu____11416))::(uu____11417,
                                                           (q,uu____11419))::[]
                             ->
                             let uu____11484 = FStar_Syntax_Util.term_eq p q in
                             (if uu____11484
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____11486 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____11502 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____11502
                          then
                            let uu____11503 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____11503 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____11558)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____11597)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____11636 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____11652 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____11652
                             then
                               match args with
                               | (t,uu____11654)::[] ->
                                   let uu____11671 =
                                     let uu____11672 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____11672.FStar_Syntax_Syntax.n in
                                   (match uu____11671 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11675::[],body,uu____11677) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11704 -> tm1)
                                    | uu____11707 -> tm1)
                               | (uu____11708,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____11709))::
                                   (t,uu____11711)::[] ->
                                   let uu____11750 =
                                     let uu____11751 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____11751.FStar_Syntax_Syntax.n in
                                   (match uu____11750 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11754::[],body,uu____11756) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11783 -> tm1)
                                    | uu____11786 -> tm1)
                               | uu____11787 -> tm1
                             else
                               (let uu____11797 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____11797
                                then
                                  match args with
                                  | (t,uu____11799)::[] ->
                                      let uu____11816 =
                                        let uu____11817 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____11817.FStar_Syntax_Syntax.n in
                                      (match uu____11816 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11820::[],body,uu____11822)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11849 -> tm1)
                                       | uu____11852 -> tm1)
                                  | (uu____11853,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____11854))::(t,uu____11856)::[] ->
                                      let uu____11895 =
                                        let uu____11896 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____11896.FStar_Syntax_Syntax.n in
                                      (match uu____11895 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11899::[],body,uu____11901)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11928 -> tm1)
                                       | uu____11931 -> tm1)
                                  | uu____11932 -> tm1
                                else
                                  (let uu____11942 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____11942
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11943;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11944;_},uu____11945)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11962;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11963;_},uu____11964)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____11981 -> tm1
                                   else
                                     (let uu____11991 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____11991 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____12011 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____12026 -> tm1)
let maybe_simplify:
  'Auu____12033 'Auu____12034 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____12034) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____12033 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          if (cfg.debug).b380
          then
            (let uu____12077 = FStar_Syntax_Print.term_to_string tm in
             let uu____12078 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____12077
               uu____12078)
          else ();
          tm'
let is_norm_request:
  'Auu____12084 .
    FStar_Syntax_Syntax.term -> 'Auu____12084 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____12097 =
        let uu____12104 =
          let uu____12105 = FStar_Syntax_Util.un_uinst hd1 in
          uu____12105.FStar_Syntax_Syntax.n in
        (uu____12104, args) in
      match uu____12097 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12111::uu____12112::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12116::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____12121::uu____12122::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____12125 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___84_12136  ->
    match uu___84_12136 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____12142 =
          let uu____12145 =
            let uu____12146 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____12146 in
          [uu____12145] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____12142
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____12162 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____12162) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____12200 =
          let uu____12203 =
            let uu____12208 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____12208 s in
          FStar_All.pipe_right uu____12203 FStar_Util.must in
        FStar_All.pipe_right uu____12200 tr_norm_steps in
      match args with
      | uu____12233::(tm,uu____12235)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____12258)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____12273)::uu____12274::(tm,uu____12276)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____12316 =
              let uu____12319 = full_norm steps in parse_steps uu____12319 in
            Beta :: uu____12316 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____12328 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___85_12345  ->
    match uu___85_12345 with
    | (App
        (uu____12348,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12349;
                       FStar_Syntax_Syntax.vars = uu____12350;_},uu____12351,uu____12352))::uu____12353
        -> true
    | uu____12360 -> false
let firstn:
  'Auu____12366 .
    Prims.int ->
      'Auu____12366 Prims.list ->
        ('Auu____12366 Prims.list,'Auu____12366 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let should_reify: cfg -> stack_elt Prims.list -> Prims.bool =
  fun cfg  ->
    fun stack  ->
      match stack with
      | (App
          (uu____12402,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____12403;
                         FStar_Syntax_Syntax.vars = uu____12404;_},uu____12405,uu____12406))::uu____12407
          -> (cfg.steps).reify_
      | uu____12414 -> false
let attr_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun a  ->
    fun a'  ->
      let r =
        let uu____12424 = FStar_Syntax_Util.eq_tm a a' in
        match uu____12424 with
        | FStar_Syntax_Util.Equal  -> true
        | uu____12425 -> false in
      r
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            if (cfg.debug).norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____12567 ->
                   let uu____12592 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12592
               | uu____12593 -> ())
            else ();
            FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____12601  ->
               let uu____12602 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____12603 = FStar_Syntax_Print.term_to_string t1 in
               let uu____12604 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____12611 =
                 let uu____12612 =
                   let uu____12615 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12615 in
                 stack_to_string uu____12612 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12602 uu____12603 uu____12604 uu____12611);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12638 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12639 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12640;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____12641;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12644;
                 FStar_Syntax_Syntax.fv_delta = uu____12645;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12646;
                 FStar_Syntax_Syntax.fv_delta = uu____12647;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12648);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (cfg.steps).no_delta_steps))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___147_12690 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___147_12690.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___147_12690.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___148_12728 = cfg in
                 {
                   steps =
                     (let uu___149_12731 = cfg.steps in
                      {
                        beta = (uu___149_12731.beta);
                        iota = (uu___149_12731.iota);
                        zeta = (uu___149_12731.zeta);
                        weak = (uu___149_12731.weak);
                        hnf = (uu___149_12731.hnf);
                        primops = (uu___149_12731.primops);
                        eager_unfolding = (uu___149_12731.eager_unfolding);
                        inlining = (uu___149_12731.inlining);
                        no_delta_steps = false;
                        unfold_until = (uu___149_12731.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___149_12731.unfold_attr);
                        unfold_tac = (uu___149_12731.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___149_12731.pure_subterms_within_computations);
                        simplify = (uu___149_12731.simplify);
                        erase_universes = (uu___149_12731.erase_universes);
                        allow_unbound_universes =
                          (uu___149_12731.allow_unbound_universes);
                        reify_ = (uu___149_12731.reify_);
                        compress_uvars = (uu___149_12731.compress_uvars);
                        no_full_norm = (uu___149_12731.no_full_norm);
                        check_no_uvars = (uu___149_12731.check_no_uvars);
                        unmeta = (uu___149_12731.unmeta);
                        unascribe = (uu___149_12731.unascribe)
                      });
                   tcenv = (uu___148_12728.tcenv);
                   debug = (uu___148_12728.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___148_12728.primitive_steps);
                   strong = (uu___148_12728.strong);
                   memoize_lazy = (uu___148_12728.memoize_lazy);
                   normalize_pure_lets = true
                 } in
               let uu____12734 = get_norm_request (norm cfg' env []) args in
               (match uu____12734 with
                | (s,tm) ->
                    let delta_level =
                      let uu____12750 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___86_12755  ->
                                match uu___86_12755 with
                                | UnfoldUntil uu____12756 -> true
                                | UnfoldOnly uu____12757 -> true
                                | uu____12760 -> false)) in
                      if uu____12750
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___150_12765 = cfg in
                      let uu____12766 = to_fsteps s in
                      {
                        steps = uu____12766;
                        tcenv = (uu___150_12765.tcenv);
                        debug = (uu___150_12765.debug);
                        delta_level;
                        primitive_steps = (uu___150_12765.primitive_steps);
                        strong = (uu___150_12765.strong);
                        memoize_lazy = (uu___150_12765.memoize_lazy);
                        normalize_pure_lets = true
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12775 =
                          let uu____12776 =
                            let uu____12781 = FStar_Util.now () in
                            (t1, uu____12781) in
                          Debug uu____12776 in
                        uu____12775 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____12785 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____12785
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12794 =
                      let uu____12801 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____12801, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____12794 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12811 = FStar_Syntax_Syntax.lid_of_fv fv in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12811 in
               let uu____12812 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo in
               if uu____12812
               then
                 let b = should_reify cfg stack in
                 (log cfg
                    (fun uu____12818  ->
                       let uu____12819 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12820 = FStar_Util.string_of_bool b in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12819 uu____12820);
                  if b
                  then
                    (let uu____12821 = FStar_List.tl stack in
                     do_unfold_fv cfg env uu____12821 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    FStar_All.pipe_right cfg.delta_level
                      (FStar_Util.for_some
                         (fun uu___87_12830  ->
                            match uu___87_12830 with
                            | FStar_TypeChecker_Env.UnfoldTac  -> false
                            | FStar_TypeChecker_Env.NoDelta  -> false
                            | FStar_TypeChecker_Env.Inlining  -> true
                            | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                                true
                            | FStar_TypeChecker_Env.Unfold l ->
                                FStar_TypeChecker_Common.delta_depth_greater_than
                                  fv.FStar_Syntax_Syntax.fv_delta l)) in
                  let should_delta1 =
                    if Prims.op_Negation should_delta
                    then false
                    else
                      (let attrs =
                         FStar_TypeChecker_Env.attrs_of_qninfo qninfo in
                       ((Prims.op_Negation (cfg.steps).unfold_tac) ||
                          (let uu____12840 =
                             cases
                               (FStar_Util.for_some
                                  (attr_eq FStar_Syntax_Util.tac_opaque_attr))
                               false attrs in
                           Prims.op_Negation uu____12840))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12859) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some (attr_eq at) ats')
                                   ats
                             | (uu____12894,uu____12895) -> false))) in
                  log cfg
                    (fun uu____12917  ->
                       let uu____12918 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12919 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____12920 =
                         FStar_Util.string_of_bool should_delta1 in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____12918
                         uu____12919 uu____12920);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12923 = lookup_bvar env x in
               (match uu____12923 with
                | Univ uu____12926 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12975 = FStar_ST.op_Bang r in
                      (match uu____12975 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____13093  ->
                                 let uu____13094 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____13095 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____13094
                                   uu____13095);
                            (let uu____13096 =
                               let uu____13097 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____13097.FStar_Syntax_Syntax.n in
                             match uu____13096 with
                             | FStar_Syntax_Syntax.Tm_abs uu____13100 ->
                                 norm cfg env2 stack t'
                             | uu____13117 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____13187)::uu____13188 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____13197)::uu____13198 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____13208,uu____13209))::stack_rest ->
                    (match c with
                     | Univ uu____13213 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____13222 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____13243  ->
                                    let uu____13244 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13244);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____13284  ->
                                    let uu____13285 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13285);
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
                       (fun uu____13363  ->
                          let uu____13364 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13364);
                     norm cfg env stack1 t1)
                | (Debug uu____13365)::uu____13366 ->
                    if (cfg.steps).weak
                    then
                      let uu____13373 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13373
                    else
                      (let uu____13375 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13375 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13417  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13454 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13454)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_13459 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_13459.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_13459.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13460 -> lopt in
                           (log cfg
                              (fun uu____13466  ->
                                 let uu____13467 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13467);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___152_13476 = cfg in
                               {
                                 steps = (uu___152_13476.steps);
                                 tcenv = (uu___152_13476.tcenv);
                                 debug = (uu___152_13476.debug);
                                 delta_level = (uu___152_13476.delta_level);
                                 primitive_steps =
                                   (uu___152_13476.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_13476.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_13476.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13487)::uu____13488 ->
                    if (cfg.steps).weak
                    then
                      let uu____13495 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13495
                    else
                      (let uu____13497 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13497 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13539  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13576 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13576)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_13581 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_13581.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_13581.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13582 -> lopt in
                           (log cfg
                              (fun uu____13588  ->
                                 let uu____13589 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13589);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___152_13598 = cfg in
                               {
                                 steps = (uu___152_13598.steps);
                                 tcenv = (uu___152_13598.tcenv);
                                 debug = (uu___152_13598.debug);
                                 delta_level = (uu___152_13598.delta_level);
                                 primitive_steps =
                                   (uu___152_13598.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_13598.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_13598.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13609)::uu____13610 ->
                    if (cfg.steps).weak
                    then
                      let uu____13621 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13621
                    else
                      (let uu____13623 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13623 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13665  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13702 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13702)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_13707 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_13707.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_13707.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13708 -> lopt in
                           (log cfg
                              (fun uu____13714  ->
                                 let uu____13715 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13715);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___152_13724 = cfg in
                               {
                                 steps = (uu___152_13724.steps);
                                 tcenv = (uu___152_13724.tcenv);
                                 debug = (uu___152_13724.debug);
                                 delta_level = (uu___152_13724.delta_level);
                                 primitive_steps =
                                   (uu___152_13724.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_13724.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_13724.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13735)::uu____13736 ->
                    if (cfg.steps).weak
                    then
                      let uu____13747 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13747
                    else
                      (let uu____13749 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13749 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13791  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13828 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13828)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_13833 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_13833.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_13833.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13834 -> lopt in
                           (log cfg
                              (fun uu____13840  ->
                                 let uu____13841 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13841);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___152_13850 = cfg in
                               {
                                 steps = (uu___152_13850.steps);
                                 tcenv = (uu___152_13850.tcenv);
                                 debug = (uu___152_13850.debug);
                                 delta_level = (uu___152_13850.delta_level);
                                 primitive_steps =
                                   (uu___152_13850.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_13850.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_13850.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13861)::uu____13862 ->
                    if (cfg.steps).weak
                    then
                      let uu____13877 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13877
                    else
                      (let uu____13879 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13879 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13921  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13958 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13958)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_13963 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_13963.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_13963.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13964 -> lopt in
                           (log cfg
                              (fun uu____13970  ->
                                 let uu____13971 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13971);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___152_13980 = cfg in
                               {
                                 steps = (uu___152_13980.steps);
                                 tcenv = (uu___152_13980.tcenv);
                                 debug = (uu___152_13980.debug);
                                 delta_level = (uu___152_13980.delta_level);
                                 primitive_steps =
                                   (uu___152_13980.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_13980.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_13980.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____13991 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13991
                    else
                      (let uu____13993 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13993 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14035  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____14072 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____14072)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_14077 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_14077.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_14077.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14078 -> lopt in
                           (log cfg
                              (fun uu____14084  ->
                                 let uu____14085 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14085);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___152_14094 = cfg in
                               {
                                 steps = (uu___152_14094.steps);
                                 tcenv = (uu___152_14094.tcenv);
                                 debug = (uu___152_14094.debug);
                                 delta_level = (uu___152_14094.delta_level);
                                 primitive_steps =
                                   (uu___152_14094.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_14094.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_14094.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____14143  ->
                         fun stack1  ->
                           match uu____14143 with
                           | (a,aq) ->
                               let uu____14155 =
                                 let uu____14156 =
                                   let uu____14163 =
                                     let uu____14164 =
                                       let uu____14195 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____14195, false) in
                                     Clos uu____14164 in
                                   (uu____14163, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____14156 in
                               uu____14155 :: stack1) args) in
               (log cfg
                  (fun uu____14279  ->
                     let uu____14280 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____14280);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if (cfg.steps).weak
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___153_14316 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___153_14316.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___153_14316.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____14317 ->
                      let uu____14322 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____14322)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____14325 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____14325 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____14356 =
                          let uu____14357 =
                            let uu____14364 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___154_14366 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___154_14366.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___154_14366.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____14364) in
                          FStar_Syntax_Syntax.Tm_refine uu____14357 in
                        mk uu____14356 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14385 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____14385
               else
                 (let uu____14387 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____14387 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14395 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14419  -> dummy :: env1) env) in
                        norm_comp cfg uu____14395 c1 in
                      let t2 =
                        let uu____14441 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____14441 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14552)::uu____14553 ->
                    (log cfg
                       (fun uu____14564  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14565)::uu____14566 ->
                    (log cfg
                       (fun uu____14577  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14578,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14579;
                                   FStar_Syntax_Syntax.vars = uu____14580;_},uu____14581,uu____14582))::uu____14583
                    ->
                    (log cfg
                       (fun uu____14592  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14593)::uu____14594 ->
                    (log cfg
                       (fun uu____14605  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14606 ->
                    (log cfg
                       (fun uu____14609  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____14613  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14630 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____14630
                         | FStar_Util.Inr c ->
                             let uu____14638 = norm_comp cfg env c in
                             FStar_Util.Inr uu____14638 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14651 =
                               let uu____14652 =
                                 let uu____14679 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____14679, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14652 in
                             mk uu____14651 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____14698 ->
                           let uu____14699 =
                             let uu____14700 =
                               let uu____14701 =
                                 let uu____14728 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____14728, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14701 in
                             mk uu____14700 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____14699))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack in
               norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____14838 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____14838 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___155_14858 = cfg in
                               let uu____14859 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___155_14858.steps);
                                 tcenv = uu____14859;
                                 debug = (uu___155_14858.debug);
                                 delta_level = (uu___155_14858.delta_level);
                                 primitive_steps =
                                   (uu___155_14858.primitive_steps);
                                 strong = (uu___155_14858.strong);
                                 memoize_lazy = (uu___155_14858.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___155_14858.normalize_pure_lets)
                               } in
                             let norm1 t2 =
                               let uu____14864 =
                                 let uu____14865 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____14865 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14864 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___156_14868 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___156_14868.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___156_14868.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___156_14868.FStar_Syntax_Syntax.lbattrs)
                             })) in
               let uu____14869 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____14869
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14880,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14881;
                               FStar_Syntax_Syntax.lbunivs = uu____14882;
                               FStar_Syntax_Syntax.lbtyp = uu____14883;
                               FStar_Syntax_Syntax.lbeff = uu____14884;
                               FStar_Syntax_Syntax.lbdef = uu____14885;
                               FStar_Syntax_Syntax.lbattrs = uu____14886;_}::uu____14887),uu____14888)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____14928 =
                 (Prims.op_Negation (cfg.steps).no_delta_steps) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       (cfg.normalize_pure_lets ||
                          (FStar_Util.for_some
                             (FStar_Syntax_Util.is_fvar
                                FStar_Parser_Const.inline_let_attr)
                             lb.FStar_Syntax_Syntax.lbattrs)))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.steps).pure_subterms_within_computations))) in
               if uu____14928
               then
                 let binder =
                   let uu____14930 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____14930 in
                 let env1 =
                   let uu____14940 =
                     let uu____14947 =
                       let uu____14948 =
                         let uu____14979 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14979,
                           false) in
                       Clos uu____14948 in
                     ((FStar_Pervasives_Native.Some binder), uu____14947) in
                   uu____14940 :: env in
                 (log cfg
                    (fun uu____15072  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____15076  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____15077 = closure_as_term cfg env t1 in
                     rebuild cfg env stack uu____15077))
                 else
                   (let uu____15079 =
                      let uu____15084 =
                        let uu____15085 =
                          let uu____15086 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left in
                          FStar_All.pipe_right uu____15086
                            FStar_Syntax_Syntax.mk_binder in
                        [uu____15085] in
                      FStar_Syntax_Subst.open_term uu____15084 body in
                    match uu____15079 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____15095  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type\n");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                          let lbname =
                            let x =
                              let uu____15103 = FStar_List.hd bs in
                              FStar_Pervasives_Native.fst uu____15103 in
                            FStar_Util.Inl
                              (let uu___157_15113 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_15113.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_15113.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }) in
                          log cfg
                            (fun uu____15116  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___158_15118 = lb in
                             let uu____15119 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___158_15118.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___158_15118.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15119;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___158_15118.FStar_Syntax_Syntax.lbattrs)
                             } in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15154  -> dummy :: env1) env) in
                           let stack1 = (Cfg cfg) :: stack in
                           let cfg1 =
                             let uu___159_15177 = cfg in
                             {
                               steps = (uu___159_15177.steps);
                               tcenv = (uu___159_15177.tcenv);
                               debug = (uu___159_15177.debug);
                               delta_level = (uu___159_15177.delta_level);
                               primitive_steps =
                                 (uu___159_15177.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___159_15177.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___159_15177.normalize_pure_lets)
                             } in
                           log cfg1
                             (fun uu____15180  ->
                                FStar_Util.print_string
                                  "+++ Normalizing Tm_let -- body\n");
                           norm cfg1 env'
                             ((Let
                                 (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                             :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (cfg.steps).compress_uvars ||
                 ((Prims.op_Negation (cfg.steps).zeta) &&
                    (cfg.steps).pure_subterms_within_computations)
               ->
               let uu____15197 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____15197 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____15233 =
                               let uu___160_15234 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___160_15234.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___160_15234.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____15233 in
                           let uu____15235 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____15235 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____15261 =
                                   FStar_List.map (fun uu____15277  -> dummy)
                                     lbs1 in
                                 let uu____15278 =
                                   let uu____15287 =
                                     FStar_List.map
                                       (fun uu____15307  -> dummy) xs1 in
                                   FStar_List.append uu____15287 env in
                                 FStar_List.append uu____15261 uu____15278 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15331 =
                                       let uu___161_15332 = rc in
                                       let uu____15333 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___161_15332.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15333;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___161_15332.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____15331
                                 | uu____15340 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___162_15344 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___162_15344.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___162_15344.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___162_15344.FStar_Syntax_Syntax.lbattrs)
                               }) lbs1 in
                    let env' =
                      let uu____15354 =
                        FStar_List.map (fun uu____15370  -> dummy) lbs2 in
                      FStar_List.append uu____15354 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____15378 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____15378 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___163_15394 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___163_15394.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___163_15394.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15421 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____15421
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15440 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15516  ->
                        match uu____15516 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___164_15637 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___164_15637.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___164_15637.FStar_Syntax_Syntax.sort)
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
               (match uu____15440 with
                | (rec_env,memos,uu____15850) ->
                    let uu____15903 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____16214 =
                               let uu____16221 =
                                 let uu____16222 =
                                   let uu____16253 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____16253, false) in
                                 Clos uu____16222 in
                               (FStar_Pervasives_Native.None, uu____16221) in
                             uu____16214 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16363  ->
                     let uu____16364 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16364);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16386 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16388::uu____16389 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16394) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____16395 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____16426 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16440 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16440
                              | uu____16451 -> m in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16455 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16481 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16499 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16516 =
                        let uu____16517 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos in
                        let uu____16518 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16517 uu____16518 in
                      failwith uu____16516
                    else rebuild cfg env stack t2
                | uu____16520 -> norm cfg env stack t2))
and do_unfold_fv:
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun qninfo  ->
            fun f  ->
              let r_env =
                let uu____16530 = FStar_Syntax_Syntax.range_of_fv f in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16530 in
              let uu____16531 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo in
              match uu____16531 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16544  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16555  ->
                        let uu____16556 =
                          FStar_Syntax_Print.term_to_string t0 in
                        let uu____16557 = FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16556 uu____16557);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        FStar_Syntax_Subst.set_use_range
                          (FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                          t in
                    let n1 = FStar_List.length us in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16570))::stack1 ->
                          let env1 =
                            FStar_All.pipe_right us'
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun u  ->
                                      (FStar_Pervasives_Native.None,
                                        (Univ u))
                                      :: env1) env) in
                          norm cfg env1 stack1 t1
                      | uu____16625 when (cfg.steps).erase_universes ->
                          norm cfg env stack t1
                      | uu____16628 ->
                          let uu____16631 =
                            let uu____16632 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16632 in
                          failwith uu____16631
                    else norm cfg env stack t1))
and reduce_impure_comp:
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t in
              let stack1 = (Cfg cfg) :: stack in
              let cfg1 =
                if (cfg.steps).pure_subterms_within_computations
                then
                  let uu___165_16653 = cfg in
                  let uu____16654 =
                    to_fsteps
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps] in
                  {
                    steps = uu____16654;
                    tcenv = (uu___165_16653.tcenv);
                    debug = (uu___165_16653.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___165_16653.primitive_steps);
                    strong = (uu___165_16653.strong);
                    memoize_lazy = (uu___165_16653.memoize_lazy);
                    normalize_pure_lets =
                      (uu___165_16653.normalize_pure_lets)
                  }
                else
                  (let uu___166_16656 = cfg in
                   {
                     steps =
                       (let uu___167_16659 = cfg.steps in
                        {
                          beta = (uu___167_16659.beta);
                          iota = (uu___167_16659.iota);
                          zeta = false;
                          weak = (uu___167_16659.weak);
                          hnf = (uu___167_16659.hnf);
                          primops = (uu___167_16659.primops);
                          eager_unfolding = (uu___167_16659.eager_unfolding);
                          inlining = (uu___167_16659.inlining);
                          no_delta_steps = (uu___167_16659.no_delta_steps);
                          unfold_until = (uu___167_16659.unfold_until);
                          unfold_only = (uu___167_16659.unfold_only);
                          unfold_attr = (uu___167_16659.unfold_attr);
                          unfold_tac = (uu___167_16659.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___167_16659.pure_subterms_within_computations);
                          simplify = (uu___167_16659.simplify);
                          erase_universes = (uu___167_16659.erase_universes);
                          allow_unbound_universes =
                            (uu___167_16659.allow_unbound_universes);
                          reify_ = (uu___167_16659.reify_);
                          compress_uvars = (uu___167_16659.compress_uvars);
                          no_full_norm = (uu___167_16659.no_full_norm);
                          check_no_uvars = (uu___167_16659.check_no_uvars);
                          unmeta = (uu___167_16659.unmeta);
                          unascribe = (uu___167_16659.unascribe)
                        });
                     tcenv = (uu___166_16656.tcenv);
                     debug = (uu___166_16656.debug);
                     delta_level = (uu___166_16656.delta_level);
                     primitive_steps = (uu___166_16656.primitive_steps);
                     strong = (uu___166_16656.strong);
                     memoize_lazy = (uu___166_16656.memoize_lazy);
                     normalize_pure_lets =
                       (uu___166_16656.normalize_pure_lets)
                   }) in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1) in
              norm cfg1 env
                ((Meta (metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1
and do_reify_monadic:
  (Prims.unit -> FStar_Syntax_Syntax.term) ->
    cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                let head0 = head1 in
                let head2 = FStar_Syntax_Util.unascribe head1 in
                log cfg
                  (fun uu____16689  ->
                     let uu____16690 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____16691 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16690
                       uu____16691);
                (let uu____16692 =
                   let uu____16693 = FStar_Syntax_Subst.compress head2 in
                   uu____16693.FStar_Syntax_Syntax.n in
                 match uu____16692 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____16711 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____16711 with
                      | (uu____16712,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16718 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16726 =
                                   let uu____16727 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____16727.FStar_Syntax_Syntax.n in
                                 match uu____16726 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16733,uu____16734))
                                     ->
                                     let uu____16743 =
                                       let uu____16744 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____16744.FStar_Syntax_Syntax.n in
                                     (match uu____16743 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16750,msrc,uu____16752))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16761 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____16761
                                      | uu____16762 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16763 ->
                                     FStar_Pervasives_Native.None in
                               let uu____16764 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____16764 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___168_16769 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___168_16769.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___168_16769.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___168_16769.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___168_16769.FStar_Syntax_Syntax.lbattrs)
                                      } in
                                    let uu____16770 = FStar_List.tl stack in
                                    let uu____16771 =
                                      let uu____16772 =
                                        let uu____16775 =
                                          let uu____16776 =
                                            let uu____16789 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____16789) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16776 in
                                        FStar_Syntax_Syntax.mk uu____16775 in
                                      uu____16772
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____16770 uu____16771
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16805 =
                                      let uu____16806 = is_return body in
                                      match uu____16806 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16810;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16811;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16816 -> false in
                                    if uu____16805
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head2.FStar_Syntax_Syntax.pos in
                                       let head3 =
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
                                         let uu____16839 =
                                           let uu____16842 =
                                             let uu____16843 =
                                               let uu____16860 =
                                                 let uu____16863 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____16863] in
                                               (uu____16860, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16843 in
                                           FStar_Syntax_Syntax.mk uu____16842 in
                                         uu____16839
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____16879 =
                                           let uu____16880 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____16880.FStar_Syntax_Syntax.n in
                                         match uu____16879 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16886::uu____16887::[])
                                             ->
                                             let uu____16894 =
                                               let uu____16897 =
                                                 let uu____16898 =
                                                   let uu____16905 =
                                                     let uu____16908 =
                                                       let uu____16909 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16909 in
                                                     let uu____16910 =
                                                       let uu____16913 =
                                                         let uu____16914 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16914 in
                                                       [uu____16913] in
                                                     uu____16908 ::
                                                       uu____16910 in
                                                   (bind1, uu____16905) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16898 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16897 in
                                             uu____16894
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16922 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____16928 =
                                           let uu____16931 =
                                             let uu____16932 =
                                               let uu____16947 =
                                                 let uu____16950 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____16951 =
                                                   let uu____16954 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____16955 =
                                                     let uu____16958 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____16959 =
                                                       let uu____16962 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____16963 =
                                                         let uu____16966 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____16967 =
                                                           let uu____16970 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____16970] in
                                                         uu____16966 ::
                                                           uu____16967 in
                                                       uu____16962 ::
                                                         uu____16963 in
                                                     uu____16958 ::
                                                       uu____16959 in
                                                   uu____16954 :: uu____16955 in
                                                 uu____16950 :: uu____16951 in
                                               (bind_inst, uu____16947) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16932 in
                                           FStar_Syntax_Syntax.mk uu____16931 in
                                         uu____16928
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____16982  ->
                                            let uu____16983 =
                                              FStar_Syntax_Print.term_to_string
                                                head0 in
                                            let uu____16984 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16983 uu____16984);
                                       (let uu____16985 = FStar_List.tl stack in
                                        norm cfg env uu____16985 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____17009 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____17009 with
                      | (uu____17010,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____17045 =
                                  let uu____17046 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____17046.FStar_Syntax_Syntax.n in
                                match uu____17045 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____17052) -> t2
                                | uu____17057 -> head3 in
                              let uu____17058 =
                                let uu____17059 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____17059.FStar_Syntax_Syntax.n in
                              match uu____17058 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____17065 -> FStar_Pervasives_Native.None in
                            let uu____17066 = maybe_extract_fv head3 in
                            match uu____17066 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____17076 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____17076
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____17081 = maybe_extract_fv head4 in
                                  match uu____17081 with
                                  | FStar_Pervasives_Native.Some uu____17086
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____17087 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____17092 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____17107 =
                              match uu____17107 with
                              | (e,q) ->
                                  let uu____17114 =
                                    let uu____17115 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____17115.FStar_Syntax_Syntax.n in
                                  (match uu____17114 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____17130 -> false) in
                            let uu____17131 =
                              let uu____17132 =
                                let uu____17139 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____17139 :: args in
                              FStar_Util.for_some is_arg_impure uu____17132 in
                            if uu____17131
                            then
                              let uu____17144 =
                                let uu____17145 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____17145 in
                              failwith uu____17144
                            else ());
                           (let uu____17147 = maybe_unfold_action head_app in
                            match uu____17147 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos in
                                let body =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head_app1, args)) in
                                let body1 =
                                  match found_action with
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Syntax_Util.mk_reify body
                                  | FStar_Pervasives_Native.Some (false ) ->
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_meta
                                           (body,
                                             (FStar_Syntax_Syntax.Meta_monadic
                                                (m, t))))
                                  | FStar_Pervasives_Native.Some (true ) ->
                                      body in
                                (log cfg
                                   (fun uu____17188  ->
                                      let uu____17189 =
                                        FStar_Syntax_Print.term_to_string
                                          head0 in
                                      let uu____17190 =
                                        FStar_Syntax_Print.term_to_string
                                          body1 in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17189 uu____17190);
                                 (let uu____17191 = FStar_List.tl stack in
                                  norm cfg env uu____17191 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17193) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17217 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____17217 in
                     (log cfg
                        (fun uu____17221  ->
                           let uu____17222 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17222);
                      (let uu____17223 = FStar_List.tl stack in
                       norm cfg env uu____17223 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____17225) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17350  ->
                               match uu____17350 with
                               | (pat,wopt,tm) ->
                                   let uu____17398 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____17398))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____17430 = FStar_List.tl stack in
                     norm cfg env uu____17430 tm
                 | uu____17431 -> fallback ())
and reify_lift:
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.tcenv in
            log cfg
              (fun uu____17445  ->
                 let uu____17446 = FStar_Ident.string_of_lid msrc in
                 let uu____17447 = FStar_Ident.string_of_lid mtgt in
                 let uu____17448 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17446
                   uu____17447 uu____17448);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____17450 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____17450 with
               | (uu____17451,return_repr) ->
                   let return_inst =
                     let uu____17460 =
                       let uu____17461 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____17461.FStar_Syntax_Syntax.n in
                     match uu____17460 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17467::[]) ->
                         let uu____17474 =
                           let uu____17477 =
                             let uu____17478 =
                               let uu____17485 =
                                 let uu____17488 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____17488] in
                               (return_tm, uu____17485) in
                             FStar_Syntax_Syntax.Tm_uinst uu____17478 in
                           FStar_Syntax_Syntax.mk uu____17477 in
                         uu____17474 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17496 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____17499 =
                     let uu____17502 =
                       let uu____17503 =
                         let uu____17518 =
                           let uu____17521 = FStar_Syntax_Syntax.as_arg t in
                           let uu____17522 =
                             let uu____17525 = FStar_Syntax_Syntax.as_arg e in
                             [uu____17525] in
                           uu____17521 :: uu____17522 in
                         (return_inst, uu____17518) in
                       FStar_Syntax_Syntax.Tm_app uu____17503 in
                     FStar_Syntax_Syntax.mk uu____17502 in
                   uu____17499 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____17534 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____17534 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17537 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____17537
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17538;
                     FStar_TypeChecker_Env.mtarget = uu____17539;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17540;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____17555 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____17555
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17556;
                     FStar_TypeChecker_Env.mtarget = uu____17557;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17558;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____17582 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____17583 = FStar_Syntax_Util.mk_reify e in
                   lift uu____17582 t FStar_Syntax_Syntax.tun uu____17583)
and norm_pattern_args:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____17639  ->
                   match uu____17639 with
                   | (a,imp) ->
                       let uu____17650 = norm cfg env [] a in
                       (uu____17650, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___169_17664 = comp in
            let uu____17665 =
              let uu____17666 =
                let uu____17675 = norm cfg env [] t in
                let uu____17676 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____17675, uu____17676) in
              FStar_Syntax_Syntax.Total uu____17666 in
            {
              FStar_Syntax_Syntax.n = uu____17665;
              FStar_Syntax_Syntax.pos =
                (uu___169_17664.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___169_17664.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___170_17691 = comp in
            let uu____17692 =
              let uu____17693 =
                let uu____17702 = norm cfg env [] t in
                let uu____17703 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____17702, uu____17703) in
              FStar_Syntax_Syntax.GTotal uu____17693 in
            {
              FStar_Syntax_Syntax.n = uu____17692;
              FStar_Syntax_Syntax.pos =
                (uu___170_17691.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___170_17691.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____17755  ->
                      match uu____17755 with
                      | (a,i) ->
                          let uu____17766 = norm cfg env [] a in
                          (uu____17766, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___88_17777  ->
                      match uu___88_17777 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____17781 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____17781
                      | f -> f)) in
            let uu___171_17785 = comp in
            let uu____17786 =
              let uu____17787 =
                let uu___172_17788 = ct in
                let uu____17789 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____17790 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____17793 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____17789;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___172_17788.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____17790;
                  FStar_Syntax_Syntax.effect_args = uu____17793;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____17787 in
            {
              FStar_Syntax_Syntax.n = uu____17786;
              FStar_Syntax_Syntax.pos =
                (uu___171_17785.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___171_17785.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____17804  ->
        match uu____17804 with
        | (x,imp) ->
            let uu____17807 =
              let uu___173_17808 = x in
              let uu____17809 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___173_17808.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___173_17808.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17809
              } in
            (uu____17807, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17815 =
          FStar_List.fold_left
            (fun uu____17833  ->
               fun b  ->
                 match uu____17833 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____17815 with | (nbs,uu____17873) -> FStar_List.rev nbs
and norm_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu____17889 =
              let uu___174_17890 = rc in
              let uu____17891 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___174_17890.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17891;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___174_17890.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____17889
        | uu____17898 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____17911  ->
               let uu____17912 = FStar_Syntax_Print.tag_of_term t in
               let uu____17913 = FStar_Syntax_Print.term_to_string t in
               let uu____17914 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____17921 =
                 let uu____17922 =
                   let uu____17925 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17925 in
                 stack_to_string uu____17922 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____17912 uu____17913 uu____17914 uu____17921);
          (let t1 = maybe_simplify cfg env stack t in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now () in
                   let uu____17956 =
                     let uu____17957 =
                       let uu____17958 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____17958 in
                     FStar_Util.string_of_int uu____17957 in
                   let uu____17963 = FStar_Syntax_Print.term_to_string tm in
                   let uu____17964 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17956 uu____17963 uu____17964)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____18018  ->
                     let uu____18019 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 "\tSet memo %s\n" uu____18019);
                rebuild cfg env stack1 t1)
           | (Let (env',bs,lb,r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t1 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r in
               rebuild cfg env' stack1 t2
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let bs1 = norm_binders cfg env' bs in
               let lopt1 = norm_lcomp_opt cfg env'' lopt in
               let uu____18055 =
                 let uu___175_18056 = FStar_Syntax_Util.abs bs1 t1 lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___175_18056.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___175_18056.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____18055
           | (Arg (Univ uu____18057,uu____18058,uu____18059))::uu____18060 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____18063,uu____18064))::uu____18065 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____18081),aq,r))::stack1 ->
               (log cfg
                  (fun uu____18134  ->
                     let uu____18135 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____18135);
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
                  (let uu____18145 = FStar_ST.op_Bang m in
                   match uu____18145 with
                   | FStar_Pervasives_Native.None  ->
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
                   | FStar_Pervasives_Native.Some (uu____18282,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1 in
               let fallback msg uu____18329 =
                 log cfg
                   (fun uu____18333  ->
                      let uu____18334 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____18334);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t2) in
               let uu____18338 =
                 let uu____18339 = FStar_Syntax_Subst.compress t1 in
                 uu____18339.FStar_Syntax_Syntax.n in
               (match uu____18338 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____18366 = closure_as_term cfg env1 ty in
                      reify_lift cfg t2 msrc mtgt uu____18366 in
                    (log cfg
                       (fun uu____18370  ->
                          let uu____18371 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____18371);
                     (let uu____18372 = FStar_List.tl stack in
                      norm cfg env1 uu____18372 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____18373);
                       FStar_Syntax_Syntax.pos = uu____18374;
                       FStar_Syntax_Syntax.vars = uu____18375;_},(e,uu____18377)::[])
                    -> norm cfg env1 stack' e
                | uu____18406 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____18426  ->
                     let uu____18427 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____18427);
                (let scrutinee = t1 in
                 let norm_and_rebuild_match uu____18432 =
                   log cfg
                     (fun uu____18437  ->
                        let uu____18438 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____18439 =
                          let uu____18440 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____18457  ->
                                    match uu____18457 with
                                    | (p,uu____18467,uu____18468) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____18440
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____18438 uu____18439);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___89_18485  ->
                                match uu___89_18485 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____18486 -> false)) in
                      let uu___176_18487 = cfg in
                      {
                        steps =
                          (let uu___177_18490 = cfg.steps in
                           {
                             beta = (uu___177_18490.beta);
                             iota = (uu___177_18490.iota);
                             zeta = false;
                             weak = (uu___177_18490.weak);
                             hnf = (uu___177_18490.hnf);
                             primops = (uu___177_18490.primops);
                             eager_unfolding =
                               (uu___177_18490.eager_unfolding);
                             inlining = (uu___177_18490.inlining);
                             no_delta_steps = (uu___177_18490.no_delta_steps);
                             unfold_until = (uu___177_18490.unfold_until);
                             unfold_only = (uu___177_18490.unfold_only);
                             unfold_attr = (uu___177_18490.unfold_attr);
                             unfold_tac = (uu___177_18490.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___177_18490.pure_subterms_within_computations);
                             simplify = (uu___177_18490.simplify);
                             erase_universes =
                               (uu___177_18490.erase_universes);
                             allow_unbound_universes =
                               (uu___177_18490.allow_unbound_universes);
                             reify_ = (uu___177_18490.reify_);
                             compress_uvars = (uu___177_18490.compress_uvars);
                             no_full_norm = (uu___177_18490.no_full_norm);
                             check_no_uvars = (uu___177_18490.check_no_uvars);
                             unmeta = (uu___177_18490.unmeta);
                             unascribe = (uu___177_18490.unascribe)
                           });
                        tcenv = (uu___176_18487.tcenv);
                        debug = (uu___176_18487.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___176_18487.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___176_18487.memoize_lazy);
                        normalize_pure_lets =
                          (uu___176_18487.normalize_pure_lets)
                      } in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____18522 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____18543 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____18603  ->
                                    fun uu____18604  ->
                                      match (uu____18603, uu____18604) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____18695 = norm_pat env3 p1 in
                                          (match uu____18695 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____18543 with
                           | (pats1,env3) ->
                               ((let uu___178_18777 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___178_18777.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___179_18796 = x in
                            let uu____18797 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___179_18796.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___179_18796.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18797
                            } in
                          ((let uu___180_18811 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___180_18811.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___181_18822 = x in
                            let uu____18823 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_18822.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_18822.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18823
                            } in
                          ((let uu___182_18837 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___182_18837.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___183_18853 = x in
                            let uu____18854 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___183_18853.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___183_18853.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18854
                            } in
                          let t3 = norm_or_whnf env2 t2 in
                          ((let uu___184_18861 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___184_18861.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____18871 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____18885 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____18885 with
                                  | (p,wopt,e) ->
                                      let uu____18905 = norm_pat env1 p in
                                      (match uu____18905 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____18930 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____18930 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____18936 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____18936) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____18946) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____18951 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18952;
                         FStar_Syntax_Syntax.fv_delta = uu____18953;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18954;
                         FStar_Syntax_Syntax.fv_delta = uu____18955;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____18956);_}
                       -> true
                   | uu____18963 -> false in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig in
                   let uu____19108 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____19108 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____19195 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____19234 ->
                                 let uu____19235 =
                                   let uu____19236 = is_cons head1 in
                                   Prims.op_Negation uu____19236 in
                                 FStar_Util.Inr uu____19235)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____19261 =
                              let uu____19262 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____19262.FStar_Syntax_Syntax.n in
                            (match uu____19261 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____19280 ->
                                 let uu____19281 =
                                   let uu____19282 = is_cons head1 in
                                   Prims.op_Negation uu____19282 in
                                 FStar_Util.Inr uu____19281))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____19351)::rest_a,(p1,uu____19354)::rest_p) ->
                       let uu____19398 = matches_pat t2 p1 in
                       (match uu____19398 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____19447 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____19553 = matches_pat scrutinee1 p1 in
                       (match uu____19553 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____19593  ->
                                  let uu____19594 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____19595 =
                                    let uu____19596 =
                                      FStar_List.map
                                        (fun uu____19606  ->
                                           match uu____19606 with
                                           | (uu____19611,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s in
                                    FStar_All.pipe_right uu____19596
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____19594 uu____19595);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____19642  ->
                                       match uu____19642 with
                                       | (bv,t2) ->
                                           let uu____19665 =
                                             let uu____19672 =
                                               let uu____19675 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____19675 in
                                             let uu____19676 =
                                               let uu____19677 =
                                                 let uu____19708 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2)) in
                                                 ([], t2, uu____19708, false) in
                                               Clos uu____19677 in
                                             (uu____19672, uu____19676) in
                                           uu____19665 :: env2) env1 s in
                              let uu____19825 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____19825))) in
                 if Prims.op_Negation (cfg.steps).iota
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config':
  primitive_step Prims.list ->
    step Prims.list -> FStar_TypeChecker_Env.env -> cfg
  =
  fun psteps  ->
    fun s  ->
      fun e  ->
        let d =
          FStar_All.pipe_right s
            (FStar_List.collect
               (fun uu___90_19853  ->
                  match uu___90_19853 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____19857 -> [])) in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____19863 -> d in
        let uu____19866 = to_fsteps s in
        let uu____19867 =
          let uu____19868 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm") in
          let uu____19869 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops") in
          let uu____19870 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380") in
          let uu____19871 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed") in
          let uu____19872 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms") in
          {
            gen = uu____19868;
            primop = uu____19869;
            b380 = uu____19870;
            norm_delayed = uu____19871;
            print_normalized = uu____19872
          } in
        let uu____19873 = add_steps built_in_primitive_steps psteps in
        let uu____19876 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____19878 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations) in
             Prims.op_Negation uu____19878) in
        {
          steps = uu____19866;
          tcenv = e;
          debug = uu____19867;
          delta_level = d1;
          primitive_steps = uu____19873;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____19876
        }
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  -> fun e  -> config' [] s e
let normalize_with_primitive_steps:
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun s  -> fun e  -> fun t  -> let c = config' ps s e in norm c [] [] t
let normalize:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t
let normalize_comp:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____19936 = config s e in norm_comp uu____19936 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____19949 = config [] env in norm_universe uu____19949 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env in
      let non_info t =
        let uu____19967 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____19967 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____19974 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___185_19993 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___185_19993.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___185_19993.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____20000 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____20000
          then
            let ct1 =
              match downgrade_ghost_effect_name
                      ct.FStar_Syntax_Syntax.effect_name
              with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    if
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags in
                  let uu___186_20009 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___186_20009.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___186_20009.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___186_20009.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___187_20011 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___187_20011.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___187_20011.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___187_20011.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___187_20011.FStar_Syntax_Syntax.flags)
                  } in
            let uu___188_20012 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___188_20012.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___188_20012.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____20014 -> c
let ghost_to_pure_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env in
      let non_info t =
        let uu____20026 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____20026 in
      let uu____20033 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____20033
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____20037  ->
                 let uu____20038 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____20038)
        | FStar_Pervasives_Native.None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____20055 =
                let uu____20060 =
                  let uu____20061 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____20061 in
                (FStar_Errors.Warning_NormalizationFailure, uu____20060) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____20055);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____20072 = config [AllowUnboundUniverses] env in
          norm_comp uu____20072 [] c
        with
        | e ->
            ((let uu____20085 =
                let uu____20090 =
                  let uu____20091 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____20091 in
                (FStar_Errors.Warning_NormalizationFailure, uu____20090) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____20085);
             c) in
      FStar_Syntax_Print.comp_to_string c1
let normalize_refinement:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0 in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1 in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____20128 =
                     let uu____20129 =
                       let uu____20136 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____20136) in
                     FStar_Syntax_Syntax.Tm_refine uu____20129 in
                   mk uu____20128 t01.FStar_Syntax_Syntax.pos
               | uu____20141 -> t2)
          | uu____20142 -> t2 in
        aux t
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize
        [Weak; HNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta] env
        t
let reduce_or_remove_uvar_solutions:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append (if remove then [CheckNoUvars] else [])
             [Beta;
             NoDeltaSteps;
             CompressUvars;
             Exclude Zeta;
             Exclude Iota;
             NoFullNorm]) env t
let reduce_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t
let remove_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t
let eta_expand_with_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____20182 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____20182 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____20211 ->
                 let uu____20218 = FStar_Syntax_Util.abs_formals e in
                 (match uu____20218 with
                  | (actuals,uu____20228,uu____20229) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____20243 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____20243 with
                         | (binders,args) ->
                             let uu____20260 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____20260
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____20268 ->
          let uu____20269 = FStar_Syntax_Util.head_and_args t in
          (match uu____20269 with
           | (head1,args) ->
               let uu____20306 =
                 let uu____20307 = FStar_Syntax_Subst.compress head1 in
                 uu____20307.FStar_Syntax_Syntax.n in
               (match uu____20306 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____20310,thead) ->
                    let uu____20336 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____20336 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____20378 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___193_20386 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___193_20386.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___193_20386.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___193_20386.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___193_20386.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___193_20386.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___193_20386.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___193_20386.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___193_20386.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___193_20386.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___193_20386.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___193_20386.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___193_20386.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___193_20386.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___193_20386.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___193_20386.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___193_20386.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___193_20386.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___193_20386.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___193_20386.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___193_20386.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___193_20386.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___193_20386.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___193_20386.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___193_20386.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___193_20386.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___193_20386.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___193_20386.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___193_20386.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___193_20386.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___193_20386.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___193_20386.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___193_20386.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____20378 with
                            | (uu____20387,ty,uu____20389) ->
                                eta_expand_with_type env t ty))
                | uu____20390 ->
                    let uu____20391 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___194_20399 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___194_20399.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___194_20399.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___194_20399.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___194_20399.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___194_20399.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___194_20399.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___194_20399.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___194_20399.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___194_20399.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___194_20399.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___194_20399.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___194_20399.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___194_20399.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___194_20399.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___194_20399.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___194_20399.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___194_20399.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___194_20399.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___194_20399.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___194_20399.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___194_20399.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___194_20399.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___194_20399.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___194_20399.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___194_20399.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___194_20399.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___194_20399.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___194_20399.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___194_20399.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___194_20399.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___194_20399.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___194_20399.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____20391 with
                     | (uu____20400,ty,uu____20402) ->
                         eta_expand_with_type env t ty)))
let rec elim_delayed_subst_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos in
    let t1 = FStar_Syntax_Subst.compress t in
    let elim_bv x =
      let uu___195_20459 = x in
      let uu____20460 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___195_20459.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___195_20459.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____20460
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____20463 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____20488 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____20489 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____20490 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____20491 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____20498 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____20499 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___196_20527 = rc in
          let uu____20528 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term in
          let uu____20535 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___196_20527.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____20528;
            FStar_Syntax_Syntax.residual_flags = uu____20535
          } in
        let uu____20538 =
          let uu____20539 =
            let uu____20556 = elim_delayed_subst_binders bs in
            let uu____20563 = elim_delayed_subst_term t2 in
            let uu____20564 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____20556, uu____20563, uu____20564) in
          FStar_Syntax_Syntax.Tm_abs uu____20539 in
        mk1 uu____20538
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____20593 =
          let uu____20594 =
            let uu____20607 = elim_delayed_subst_binders bs in
            let uu____20614 = elim_delayed_subst_comp c in
            (uu____20607, uu____20614) in
          FStar_Syntax_Syntax.Tm_arrow uu____20594 in
        mk1 uu____20593
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____20627 =
          let uu____20628 =
            let uu____20635 = elim_bv bv in
            let uu____20636 = elim_delayed_subst_term phi in
            (uu____20635, uu____20636) in
          FStar_Syntax_Syntax.Tm_refine uu____20628 in
        mk1 uu____20627
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____20659 =
          let uu____20660 =
            let uu____20675 = elim_delayed_subst_term t2 in
            let uu____20676 = elim_delayed_subst_args args in
            (uu____20675, uu____20676) in
          FStar_Syntax_Syntax.Tm_app uu____20660 in
        mk1 uu____20659
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___197_20740 = p in
              let uu____20741 =
                let uu____20742 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____20742 in
              {
                FStar_Syntax_Syntax.v = uu____20741;
                FStar_Syntax_Syntax.p =
                  (uu___197_20740.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___198_20744 = p in
              let uu____20745 =
                let uu____20746 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____20746 in
              {
                FStar_Syntax_Syntax.v = uu____20745;
                FStar_Syntax_Syntax.p =
                  (uu___198_20744.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___199_20753 = p in
              let uu____20754 =
                let uu____20755 =
                  let uu____20762 = elim_bv x in
                  let uu____20763 = elim_delayed_subst_term t0 in
                  (uu____20762, uu____20763) in
                FStar_Syntax_Syntax.Pat_dot_term uu____20755 in
              {
                FStar_Syntax_Syntax.v = uu____20754;
                FStar_Syntax_Syntax.p =
                  (uu___199_20753.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___200_20782 = p in
              let uu____20783 =
                let uu____20784 =
                  let uu____20797 =
                    FStar_List.map
                      (fun uu____20820  ->
                         match uu____20820 with
                         | (x,b) ->
                             let uu____20833 = elim_pat x in (uu____20833, b))
                      pats in
                  (fv, uu____20797) in
                FStar_Syntax_Syntax.Pat_cons uu____20784 in
              {
                FStar_Syntax_Syntax.v = uu____20783;
                FStar_Syntax_Syntax.p =
                  (uu___200_20782.FStar_Syntax_Syntax.p)
              }
          | uu____20846 -> p in
        let elim_branch uu____20868 =
          match uu____20868 with
          | (pat,wopt,t3) ->
              let uu____20894 = elim_pat pat in
              let uu____20897 =
                FStar_Util.map_opt wopt elim_delayed_subst_term in
              let uu____20900 = elim_delayed_subst_term t3 in
              (uu____20894, uu____20897, uu____20900) in
        let uu____20905 =
          let uu____20906 =
            let uu____20929 = elim_delayed_subst_term t2 in
            let uu____20930 = FStar_List.map elim_branch branches in
            (uu____20929, uu____20930) in
          FStar_Syntax_Syntax.Tm_match uu____20906 in
        mk1 uu____20905
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____21039 =
          match uu____21039 with
          | (tc,topt) ->
              let uu____21074 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____21084 = elim_delayed_subst_term t3 in
                    FStar_Util.Inl uu____21084
                | FStar_Util.Inr c ->
                    let uu____21086 = elim_delayed_subst_comp c in
                    FStar_Util.Inr uu____21086 in
              let uu____21087 =
                FStar_Util.map_opt topt elim_delayed_subst_term in
              (uu____21074, uu____21087) in
        let uu____21096 =
          let uu____21097 =
            let uu____21124 = elim_delayed_subst_term t2 in
            let uu____21125 = elim_ascription a in
            (uu____21124, uu____21125, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____21097 in
        mk1 uu____21096
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___201_21170 = lb in
          let uu____21171 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp in
          let uu____21174 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___201_21170.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___201_21170.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____21171;
            FStar_Syntax_Syntax.lbeff =
              (uu___201_21170.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____21174;
            FStar_Syntax_Syntax.lbattrs =
              (uu___201_21170.FStar_Syntax_Syntax.lbattrs)
          } in
        let uu____21177 =
          let uu____21178 =
            let uu____21191 =
              let uu____21198 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____21198) in
            let uu____21207 = elim_delayed_subst_term t2 in
            (uu____21191, uu____21207) in
          FStar_Syntax_Syntax.Tm_let uu____21178 in
        mk1 uu____21177
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____21240 =
          let uu____21241 =
            let uu____21258 = elim_delayed_subst_term t2 in (uv, uu____21258) in
          FStar_Syntax_Syntax.Tm_uvar uu____21241 in
        mk1 uu____21240
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____21275 =
          let uu____21276 =
            let uu____21283 = elim_delayed_subst_term t2 in
            let uu____21284 = elim_delayed_subst_meta md in
            (uu____21283, uu____21284) in
          FStar_Syntax_Syntax.Tm_meta uu____21276 in
        mk1 uu____21275
and elim_delayed_subst_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___91_21291  ->
         match uu___91_21291 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____21295 = elim_delayed_subst_term t in
             FStar_Syntax_Syntax.DECREASES uu____21295
         | f -> f) flags1
and elim_delayed_subst_comp:
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____21316 =
          let uu____21317 =
            let uu____21326 = elim_delayed_subst_term t in
            (uu____21326, uopt) in
          FStar_Syntax_Syntax.Total uu____21317 in
        mk1 uu____21316
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____21339 =
          let uu____21340 =
            let uu____21349 = elim_delayed_subst_term t in
            (uu____21349, uopt) in
          FStar_Syntax_Syntax.GTotal uu____21340 in
        mk1 uu____21339
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___202_21354 = ct in
          let uu____21355 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ in
          let uu____21358 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____21367 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___202_21354.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___202_21354.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____21355;
            FStar_Syntax_Syntax.effect_args = uu____21358;
            FStar_Syntax_Syntax.flags = uu____21367
          } in
        mk1 (FStar_Syntax_Syntax.Comp ct1)
and elim_delayed_subst_meta:
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata =
  fun uu___92_21370  ->
    match uu___92_21370 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____21382 = FStar_List.map elim_delayed_subst_args args in
        FStar_Syntax_Syntax.Meta_pattern uu____21382
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____21415 =
          let uu____21422 = elim_delayed_subst_term t in (m, uu____21422) in
        FStar_Syntax_Syntax.Meta_monadic uu____21415
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____21430 =
          let uu____21439 = elim_delayed_subst_term t in
          (m1, m2, uu____21439) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____21430
    | FStar_Syntax_Syntax.Meta_alien (d,s,t) ->
        let uu____21447 =
          let uu____21456 = elim_delayed_subst_term t in (d, s, uu____21456) in
        FStar_Syntax_Syntax.Meta_alien uu____21447
    | m -> m
and elim_delayed_subst_args:
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.map
      (fun uu____21479  ->
         match uu____21479 with
         | (t,q) ->
             let uu____21490 = elim_delayed_subst_term t in (uu____21490, q))
      args
and elim_delayed_subst_binders:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bs  ->
    FStar_List.map
      (fun uu____21510  ->
         match uu____21510 with
         | (x,q) ->
             let uu____21521 =
               let uu___203_21522 = x in
               let uu____21523 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___203_21522.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___203_21522.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____21523
               } in
             (uu____21521, q)) bs
let elim_uvars_aux_tc:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term,
                                                         FStar_Syntax_Syntax.comp'
                                                           FStar_Syntax_Syntax.syntax)
                                                         FStar_Util.either)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____21599,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____21605,FStar_Util.Inl t) ->
                let uu____21611 =
                  let uu____21614 =
                    let uu____21615 =
                      let uu____21628 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____21628) in
                    FStar_Syntax_Syntax.Tm_arrow uu____21615 in
                  FStar_Syntax_Syntax.mk uu____21614 in
                uu____21611 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____21632 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____21632 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = elim_delayed_subst_term t3 in
              let uu____21660 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____21715 ->
                    let uu____21716 =
                      let uu____21725 =
                        let uu____21726 = FStar_Syntax_Subst.compress t4 in
                        uu____21726.FStar_Syntax_Syntax.n in
                      (uu____21725, tc) in
                    (match uu____21716 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____21751) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____21788) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____21827,FStar_Util.Inl uu____21828) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____21851 -> failwith "Impossible") in
              (match uu____21660 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
let elim_uvars_aux_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____21956 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____21956 with
          | (univ_names1,binders1,tc) ->
              let uu____22014 = FStar_Util.left tc in
              (univ_names1, binders1, uu____22014)
let elim_uvars_aux_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____22049 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____22049 with
          | (univ_names1,binders1,tc) ->
              let uu____22109 = FStar_Util.right tc in
              (univ_names1, binders1, uu____22109)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____22142 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____22142 with
           | (univ_names1,binders1,typ1) ->
               let uu___204_22170 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_22170.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_22170.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_22170.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_22170.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___205_22191 = s in
          let uu____22192 =
            let uu____22193 =
              let uu____22202 = FStar_List.map (elim_uvars env) sigs in
              (uu____22202, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____22193 in
          {
            FStar_Syntax_Syntax.sigel = uu____22192;
            FStar_Syntax_Syntax.sigrng =
              (uu___205_22191.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___205_22191.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___205_22191.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___205_22191.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____22219 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____22219 with
           | (univ_names1,uu____22237,typ1) ->
               let uu___206_22251 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___206_22251.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___206_22251.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___206_22251.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___206_22251.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____22257 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____22257 with
           | (univ_names1,uu____22275,typ1) ->
               let uu___207_22289 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___207_22289.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___207_22289.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___207_22289.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___207_22289.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____22323 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____22323 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____22346 =
                            let uu____22347 =
                              let uu____22348 =
                                FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env uu____22348 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____22347 in
                          elim_delayed_subst_term uu____22346 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___208_22351 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___208_22351.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___208_22351.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___208_22351.FStar_Syntax_Syntax.lbattrs)
                        })) in
          let uu___209_22352 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___209_22352.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___209_22352.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___209_22352.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___209_22352.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___210_22364 = s in
          let uu____22365 =
            let uu____22366 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____22366 in
          {
            FStar_Syntax_Syntax.sigel = uu____22365;
            FStar_Syntax_Syntax.sigrng =
              (uu___210_22364.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___210_22364.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___210_22364.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___210_22364.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____22370 = elim_uvars_aux_t env us [] t in
          (match uu____22370 with
           | (us1,uu____22388,t1) ->
               let uu___211_22402 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_22402.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_22402.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_22402.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___211_22402.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22403 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22405 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____22405 with
           | (univs1,binders,signature) ->
               let uu____22433 =
                 let uu____22442 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____22442 with
                 | (univs_opening,univs2) ->
                     let uu____22469 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____22469) in
               (match uu____22433 with
                | (univs_opening,univs_closing) ->
                    let uu____22486 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____22492 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____22493 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____22492, uu____22493) in
                    (match uu____22486 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____22515 =
                           match uu____22515 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____22533 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____22533 with
                                | (us1,t1) ->
                                    let uu____22544 =
                                      let uu____22549 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____22556 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____22549, uu____22556) in
                                    (match uu____22544 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____22569 =
                                           let uu____22574 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____22583 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____22574, uu____22583) in
                                         (match uu____22569 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____22599 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____22599 in
                                              let uu____22600 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____22600 with
                                               | (uu____22621,uu____22622,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____22637 =
                                                       let uu____22638 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____22638 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____22637 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____22643 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____22643 with
                           | (uu____22656,uu____22657,t1) -> t1 in
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
                             | uu____22717 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____22734 =
                               let uu____22735 =
                                 FStar_Syntax_Subst.compress body in
                               uu____22735.FStar_Syntax_Syntax.n in
                             match uu____22734 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____22794 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____22823 =
                               let uu____22824 =
                                 FStar_Syntax_Subst.compress t in
                               uu____22824.FStar_Syntax_Syntax.n in
                             match uu____22823 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____22845) ->
                                 let uu____22866 = destruct_action_body body in
                                 (match uu____22866 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____22911 ->
                                 let uu____22912 = destruct_action_body t in
                                 (match uu____22912 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____22961 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____22961 with
                           | (action_univs,t) ->
                               let uu____22970 = destruct_action_typ_templ t in
                               (match uu____22970 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___212_23011 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___212_23011.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___212_23011.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___213_23013 = ed in
                           let uu____23014 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____23015 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____23016 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____23017 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____23018 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____23019 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____23020 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____23021 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____23022 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____23023 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____23024 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____23025 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____23026 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____23027 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___213_23013.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___213_23013.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____23014;
                             FStar_Syntax_Syntax.bind_wp = uu____23015;
                             FStar_Syntax_Syntax.if_then_else = uu____23016;
                             FStar_Syntax_Syntax.ite_wp = uu____23017;
                             FStar_Syntax_Syntax.stronger = uu____23018;
                             FStar_Syntax_Syntax.close_wp = uu____23019;
                             FStar_Syntax_Syntax.assert_p = uu____23020;
                             FStar_Syntax_Syntax.assume_p = uu____23021;
                             FStar_Syntax_Syntax.null_wp = uu____23022;
                             FStar_Syntax_Syntax.trivial = uu____23023;
                             FStar_Syntax_Syntax.repr = uu____23024;
                             FStar_Syntax_Syntax.return_repr = uu____23025;
                             FStar_Syntax_Syntax.bind_repr = uu____23026;
                             FStar_Syntax_Syntax.actions = uu____23027
                           } in
                         let uu___214_23030 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___214_23030.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___214_23030.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___214_23030.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___214_23030.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___93_23047 =
            match uu___93_23047 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____23074 = elim_uvars_aux_t env us [] t in
                (match uu____23074 with
                 | (us1,uu____23098,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___215_23117 = sub_eff in
            let uu____23118 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____23121 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___215_23117.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___215_23117.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____23118;
              FStar_Syntax_Syntax.lift = uu____23121
            } in
          let uu___216_23124 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___216_23124.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_23124.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_23124.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_23124.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____23134 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____23134 with
           | (univ_names1,binders1,comp1) ->
               let uu___217_23168 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___217_23168.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___217_23168.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___217_23168.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___217_23168.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____23179 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t