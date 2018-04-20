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
      fun uu___78_180 ->
        match uu___78_180 with
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
      let add_opt x uu___79_1038 =
        match uu___79_1038 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs) in
      match s with
      | Beta ->
          let uu___97_1058 = fs in
          {
            beta = true;
            iota = (uu___97_1058.iota);
            zeta = (uu___97_1058.zeta);
            weak = (uu___97_1058.weak);
            hnf = (uu___97_1058.hnf);
            primops = (uu___97_1058.primops);
            no_delta_steps = (uu___97_1058.no_delta_steps);
            unfold_until = (uu___97_1058.unfold_until);
            unfold_only = (uu___97_1058.unfold_only);
            unfold_attr = (uu___97_1058.unfold_attr);
            unfold_tac = (uu___97_1058.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1058.pure_subterms_within_computations);
            simplify = (uu___97_1058.simplify);
            erase_universes = (uu___97_1058.erase_universes);
            allow_unbound_universes = (uu___97_1058.allow_unbound_universes);
            reify_ = (uu___97_1058.reify_);
            compress_uvars = (uu___97_1058.compress_uvars);
            no_full_norm = (uu___97_1058.no_full_norm);
            check_no_uvars = (uu___97_1058.check_no_uvars);
            unmeta = (uu___97_1058.unmeta);
            unascribe = (uu___97_1058.unascribe)
          }
      | Iota ->
          let uu___98_1059 = fs in
          {
            beta = (uu___98_1059.beta);
            iota = true;
            zeta = (uu___98_1059.zeta);
            weak = (uu___98_1059.weak);
            hnf = (uu___98_1059.hnf);
            primops = (uu___98_1059.primops);
            no_delta_steps = (uu___98_1059.no_delta_steps);
            unfold_until = (uu___98_1059.unfold_until);
            unfold_only = (uu___98_1059.unfold_only);
            unfold_attr = (uu___98_1059.unfold_attr);
            unfold_tac = (uu___98_1059.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1059.pure_subterms_within_computations);
            simplify = (uu___98_1059.simplify);
            erase_universes = (uu___98_1059.erase_universes);
            allow_unbound_universes = (uu___98_1059.allow_unbound_universes);
            reify_ = (uu___98_1059.reify_);
            compress_uvars = (uu___98_1059.compress_uvars);
            no_full_norm = (uu___98_1059.no_full_norm);
            check_no_uvars = (uu___98_1059.check_no_uvars);
            unmeta = (uu___98_1059.unmeta);
            unascribe = (uu___98_1059.unascribe)
          }
      | Zeta ->
          let uu___99_1060 = fs in
          {
            beta = (uu___99_1060.beta);
            iota = (uu___99_1060.iota);
            zeta = true;
            weak = (uu___99_1060.weak);
            hnf = (uu___99_1060.hnf);
            primops = (uu___99_1060.primops);
            no_delta_steps = (uu___99_1060.no_delta_steps);
            unfold_until = (uu___99_1060.unfold_until);
            unfold_only = (uu___99_1060.unfold_only);
            unfold_attr = (uu___99_1060.unfold_attr);
            unfold_tac = (uu___99_1060.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1060.pure_subterms_within_computations);
            simplify = (uu___99_1060.simplify);
            erase_universes = (uu___99_1060.erase_universes);
            allow_unbound_universes = (uu___99_1060.allow_unbound_universes);
            reify_ = (uu___99_1060.reify_);
            compress_uvars = (uu___99_1060.compress_uvars);
            no_full_norm = (uu___99_1060.no_full_norm);
            check_no_uvars = (uu___99_1060.check_no_uvars);
            unmeta = (uu___99_1060.unmeta);
            unascribe = (uu___99_1060.unascribe)
          }
      | Exclude (Beta) ->
          let uu___100_1061 = fs in
          {
            beta = false;
            iota = (uu___100_1061.iota);
            zeta = (uu___100_1061.zeta);
            weak = (uu___100_1061.weak);
            hnf = (uu___100_1061.hnf);
            primops = (uu___100_1061.primops);
            no_delta_steps = (uu___100_1061.no_delta_steps);
            unfold_until = (uu___100_1061.unfold_until);
            unfold_only = (uu___100_1061.unfold_only);
            unfold_attr = (uu___100_1061.unfold_attr);
            unfold_tac = (uu___100_1061.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1061.pure_subterms_within_computations);
            simplify = (uu___100_1061.simplify);
            erase_universes = (uu___100_1061.erase_universes);
            allow_unbound_universes = (uu___100_1061.allow_unbound_universes);
            reify_ = (uu___100_1061.reify_);
            compress_uvars = (uu___100_1061.compress_uvars);
            no_full_norm = (uu___100_1061.no_full_norm);
            check_no_uvars = (uu___100_1061.check_no_uvars);
            unmeta = (uu___100_1061.unmeta);
            unascribe = (uu___100_1061.unascribe)
          }
      | Exclude (Iota) ->
          let uu___101_1062 = fs in
          {
            beta = (uu___101_1062.beta);
            iota = false;
            zeta = (uu___101_1062.zeta);
            weak = (uu___101_1062.weak);
            hnf = (uu___101_1062.hnf);
            primops = (uu___101_1062.primops);
            no_delta_steps = (uu___101_1062.no_delta_steps);
            unfold_until = (uu___101_1062.unfold_until);
            unfold_only = (uu___101_1062.unfold_only);
            unfold_attr = (uu___101_1062.unfold_attr);
            unfold_tac = (uu___101_1062.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1062.pure_subterms_within_computations);
            simplify = (uu___101_1062.simplify);
            erase_universes = (uu___101_1062.erase_universes);
            allow_unbound_universes = (uu___101_1062.allow_unbound_universes);
            reify_ = (uu___101_1062.reify_);
            compress_uvars = (uu___101_1062.compress_uvars);
            no_full_norm = (uu___101_1062.no_full_norm);
            check_no_uvars = (uu___101_1062.check_no_uvars);
            unmeta = (uu___101_1062.unmeta);
            unascribe = (uu___101_1062.unascribe)
          }
      | Exclude (Zeta) ->
          let uu___102_1063 = fs in
          {
            beta = (uu___102_1063.beta);
            iota = (uu___102_1063.iota);
            zeta = false;
            weak = (uu___102_1063.weak);
            hnf = (uu___102_1063.hnf);
            primops = (uu___102_1063.primops);
            no_delta_steps = (uu___102_1063.no_delta_steps);
            unfold_until = (uu___102_1063.unfold_until);
            unfold_only = (uu___102_1063.unfold_only);
            unfold_attr = (uu___102_1063.unfold_attr);
            unfold_tac = (uu___102_1063.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1063.pure_subterms_within_computations);
            simplify = (uu___102_1063.simplify);
            erase_universes = (uu___102_1063.erase_universes);
            allow_unbound_universes = (uu___102_1063.allow_unbound_universes);
            reify_ = (uu___102_1063.reify_);
            compress_uvars = (uu___102_1063.compress_uvars);
            no_full_norm = (uu___102_1063.no_full_norm);
            check_no_uvars = (uu___102_1063.check_no_uvars);
            unmeta = (uu___102_1063.unmeta);
            unascribe = (uu___102_1063.unascribe)
          }
      | Exclude uu____1064 -> failwith "Bad exclude"
      | Weak ->
          let uu___103_1065 = fs in
          {
            beta = (uu___103_1065.beta);
            iota = (uu___103_1065.iota);
            zeta = (uu___103_1065.zeta);
            weak = true;
            hnf = (uu___103_1065.hnf);
            primops = (uu___103_1065.primops);
            no_delta_steps = (uu___103_1065.no_delta_steps);
            unfold_until = (uu___103_1065.unfold_until);
            unfold_only = (uu___103_1065.unfold_only);
            unfold_attr = (uu___103_1065.unfold_attr);
            unfold_tac = (uu___103_1065.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1065.pure_subterms_within_computations);
            simplify = (uu___103_1065.simplify);
            erase_universes = (uu___103_1065.erase_universes);
            allow_unbound_universes = (uu___103_1065.allow_unbound_universes);
            reify_ = (uu___103_1065.reify_);
            compress_uvars = (uu___103_1065.compress_uvars);
            no_full_norm = (uu___103_1065.no_full_norm);
            check_no_uvars = (uu___103_1065.check_no_uvars);
            unmeta = (uu___103_1065.unmeta);
            unascribe = (uu___103_1065.unascribe)
          }
      | HNF ->
          let uu___104_1066 = fs in
          {
            beta = (uu___104_1066.beta);
            iota = (uu___104_1066.iota);
            zeta = (uu___104_1066.zeta);
            weak = (uu___104_1066.weak);
            hnf = true;
            primops = (uu___104_1066.primops);
            no_delta_steps = (uu___104_1066.no_delta_steps);
            unfold_until = (uu___104_1066.unfold_until);
            unfold_only = (uu___104_1066.unfold_only);
            unfold_attr = (uu___104_1066.unfold_attr);
            unfold_tac = (uu___104_1066.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1066.pure_subterms_within_computations);
            simplify = (uu___104_1066.simplify);
            erase_universes = (uu___104_1066.erase_universes);
            allow_unbound_universes = (uu___104_1066.allow_unbound_universes);
            reify_ = (uu___104_1066.reify_);
            compress_uvars = (uu___104_1066.compress_uvars);
            no_full_norm = (uu___104_1066.no_full_norm);
            check_no_uvars = (uu___104_1066.check_no_uvars);
            unmeta = (uu___104_1066.unmeta);
            unascribe = (uu___104_1066.unascribe)
          }
      | Primops ->
          let uu___105_1067 = fs in
          {
            beta = (uu___105_1067.beta);
            iota = (uu___105_1067.iota);
            zeta = (uu___105_1067.zeta);
            weak = (uu___105_1067.weak);
            hnf = (uu___105_1067.hnf);
            primops = true;
            no_delta_steps = (uu___105_1067.no_delta_steps);
            unfold_until = (uu___105_1067.unfold_until);
            unfold_only = (uu___105_1067.unfold_only);
            unfold_attr = (uu___105_1067.unfold_attr);
            unfold_tac = (uu___105_1067.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1067.pure_subterms_within_computations);
            simplify = (uu___105_1067.simplify);
            erase_universes = (uu___105_1067.erase_universes);
            allow_unbound_universes = (uu___105_1067.allow_unbound_universes);
            reify_ = (uu___105_1067.reify_);
            compress_uvars = (uu___105_1067.compress_uvars);
            no_full_norm = (uu___105_1067.no_full_norm);
            check_no_uvars = (uu___105_1067.check_no_uvars);
            unmeta = (uu___105_1067.unmeta);
            unascribe = (uu___105_1067.unascribe)
          }
      | Eager_unfolding -> fs
      | Inlining -> fs
      | NoDeltaSteps ->
          let uu___106_1068 = fs in
          {
            beta = (uu___106_1068.beta);
            iota = (uu___106_1068.iota);
            zeta = (uu___106_1068.zeta);
            weak = (uu___106_1068.weak);
            hnf = (uu___106_1068.hnf);
            primops = (uu___106_1068.primops);
            no_delta_steps = true;
            unfold_until = (uu___106_1068.unfold_until);
            unfold_only = (uu___106_1068.unfold_only);
            unfold_attr = (uu___106_1068.unfold_attr);
            unfold_tac = (uu___106_1068.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1068.pure_subterms_within_computations);
            simplify = (uu___106_1068.simplify);
            erase_universes = (uu___106_1068.erase_universes);
            allow_unbound_universes = (uu___106_1068.allow_unbound_universes);
            reify_ = (uu___106_1068.reify_);
            compress_uvars = (uu___106_1068.compress_uvars);
            no_full_norm = (uu___106_1068.no_full_norm);
            check_no_uvars = (uu___106_1068.check_no_uvars);
            unmeta = (uu___106_1068.unmeta);
            unascribe = (uu___106_1068.unascribe)
          }
      | UnfoldUntil d ->
          let uu___107_1070 = fs in
          {
            beta = (uu___107_1070.beta);
            iota = (uu___107_1070.iota);
            zeta = (uu___107_1070.zeta);
            weak = (uu___107_1070.weak);
            hnf = (uu___107_1070.hnf);
            primops = (uu___107_1070.primops);
            no_delta_steps = (uu___107_1070.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___107_1070.unfold_only);
            unfold_attr = (uu___107_1070.unfold_attr);
            unfold_tac = (uu___107_1070.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1070.pure_subterms_within_computations);
            simplify = (uu___107_1070.simplify);
            erase_universes = (uu___107_1070.erase_universes);
            allow_unbound_universes = (uu___107_1070.allow_unbound_universes);
            reify_ = (uu___107_1070.reify_);
            compress_uvars = (uu___107_1070.compress_uvars);
            no_full_norm = (uu___107_1070.no_full_norm);
            check_no_uvars = (uu___107_1070.check_no_uvars);
            unmeta = (uu___107_1070.unmeta);
            unascribe = (uu___107_1070.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___108_1074 = fs in
          {
            beta = (uu___108_1074.beta);
            iota = (uu___108_1074.iota);
            zeta = (uu___108_1074.zeta);
            weak = (uu___108_1074.weak);
            hnf = (uu___108_1074.hnf);
            primops = (uu___108_1074.primops);
            no_delta_steps = (uu___108_1074.no_delta_steps);
            unfold_until = (uu___108_1074.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___108_1074.unfold_attr);
            unfold_tac = (uu___108_1074.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1074.pure_subterms_within_computations);
            simplify = (uu___108_1074.simplify);
            erase_universes = (uu___108_1074.erase_universes);
            allow_unbound_universes = (uu___108_1074.allow_unbound_universes);
            reify_ = (uu___108_1074.reify_);
            compress_uvars = (uu___108_1074.compress_uvars);
            no_full_norm = (uu___108_1074.no_full_norm);
            check_no_uvars = (uu___108_1074.check_no_uvars);
            unmeta = (uu___108_1074.unmeta);
            unascribe = (uu___108_1074.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___109_1078 = fs in
          {
            beta = (uu___109_1078.beta);
            iota = (uu___109_1078.iota);
            zeta = (uu___109_1078.zeta);
            weak = (uu___109_1078.weak);
            hnf = (uu___109_1078.hnf);
            primops = (uu___109_1078.primops);
            no_delta_steps = (uu___109_1078.no_delta_steps);
            unfold_until = (uu___109_1078.unfold_until);
            unfold_only = (uu___109_1078.unfold_only);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___109_1078.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1078.pure_subterms_within_computations);
            simplify = (uu___109_1078.simplify);
            erase_universes = (uu___109_1078.erase_universes);
            allow_unbound_universes = (uu___109_1078.allow_unbound_universes);
            reify_ = (uu___109_1078.reify_);
            compress_uvars = (uu___109_1078.compress_uvars);
            no_full_norm = (uu___109_1078.no_full_norm);
            check_no_uvars = (uu___109_1078.check_no_uvars);
            unmeta = (uu___109_1078.unmeta);
            unascribe = (uu___109_1078.unascribe)
          }
      | UnfoldTac ->
          let uu___110_1079 = fs in
          {
            beta = (uu___110_1079.beta);
            iota = (uu___110_1079.iota);
            zeta = (uu___110_1079.zeta);
            weak = (uu___110_1079.weak);
            hnf = (uu___110_1079.hnf);
            primops = (uu___110_1079.primops);
            no_delta_steps = (uu___110_1079.no_delta_steps);
            unfold_until = (uu___110_1079.unfold_until);
            unfold_only = (uu___110_1079.unfold_only);
            unfold_attr = (uu___110_1079.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___110_1079.pure_subterms_within_computations);
            simplify = (uu___110_1079.simplify);
            erase_universes = (uu___110_1079.erase_universes);
            allow_unbound_universes = (uu___110_1079.allow_unbound_universes);
            reify_ = (uu___110_1079.reify_);
            compress_uvars = (uu___110_1079.compress_uvars);
            no_full_norm = (uu___110_1079.no_full_norm);
            check_no_uvars = (uu___110_1079.check_no_uvars);
            unmeta = (uu___110_1079.unmeta);
            unascribe = (uu___110_1079.unascribe)
          }
      | PureSubtermsWithinComputations ->
          let uu___111_1080 = fs in
          {
            beta = (uu___111_1080.beta);
            iota = (uu___111_1080.iota);
            zeta = (uu___111_1080.zeta);
            weak = (uu___111_1080.weak);
            hnf = (uu___111_1080.hnf);
            primops = (uu___111_1080.primops);
            no_delta_steps = (uu___111_1080.no_delta_steps);
            unfold_until = (uu___111_1080.unfold_until);
            unfold_only = (uu___111_1080.unfold_only);
            unfold_attr = (uu___111_1080.unfold_attr);
            unfold_tac = (uu___111_1080.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___111_1080.simplify);
            erase_universes = (uu___111_1080.erase_universes);
            allow_unbound_universes = (uu___111_1080.allow_unbound_universes);
            reify_ = (uu___111_1080.reify_);
            compress_uvars = (uu___111_1080.compress_uvars);
            no_full_norm = (uu___111_1080.no_full_norm);
            check_no_uvars = (uu___111_1080.check_no_uvars);
            unmeta = (uu___111_1080.unmeta);
            unascribe = (uu___111_1080.unascribe)
          }
      | Simplify ->
          let uu___112_1081 = fs in
          {
            beta = (uu___112_1081.beta);
            iota = (uu___112_1081.iota);
            zeta = (uu___112_1081.zeta);
            weak = (uu___112_1081.weak);
            hnf = (uu___112_1081.hnf);
            primops = (uu___112_1081.primops);
            no_delta_steps = (uu___112_1081.no_delta_steps);
            unfold_until = (uu___112_1081.unfold_until);
            unfold_only = (uu___112_1081.unfold_only);
            unfold_attr = (uu___112_1081.unfold_attr);
            unfold_tac = (uu___112_1081.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1081.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___112_1081.erase_universes);
            allow_unbound_universes = (uu___112_1081.allow_unbound_universes);
            reify_ = (uu___112_1081.reify_);
            compress_uvars = (uu___112_1081.compress_uvars);
            no_full_norm = (uu___112_1081.no_full_norm);
            check_no_uvars = (uu___112_1081.check_no_uvars);
            unmeta = (uu___112_1081.unmeta);
            unascribe = (uu___112_1081.unascribe)
          }
      | EraseUniverses ->
          let uu___113_1082 = fs in
          {
            beta = (uu___113_1082.beta);
            iota = (uu___113_1082.iota);
            zeta = (uu___113_1082.zeta);
            weak = (uu___113_1082.weak);
            hnf = (uu___113_1082.hnf);
            primops = (uu___113_1082.primops);
            no_delta_steps = (uu___113_1082.no_delta_steps);
            unfold_until = (uu___113_1082.unfold_until);
            unfold_only = (uu___113_1082.unfold_only);
            unfold_attr = (uu___113_1082.unfold_attr);
            unfold_tac = (uu___113_1082.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1082.pure_subterms_within_computations);
            simplify = (uu___113_1082.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___113_1082.allow_unbound_universes);
            reify_ = (uu___113_1082.reify_);
            compress_uvars = (uu___113_1082.compress_uvars);
            no_full_norm = (uu___113_1082.no_full_norm);
            check_no_uvars = (uu___113_1082.check_no_uvars);
            unmeta = (uu___113_1082.unmeta);
            unascribe = (uu___113_1082.unascribe)
          }
      | AllowUnboundUniverses ->
          let uu___114_1083 = fs in
          {
            beta = (uu___114_1083.beta);
            iota = (uu___114_1083.iota);
            zeta = (uu___114_1083.zeta);
            weak = (uu___114_1083.weak);
            hnf = (uu___114_1083.hnf);
            primops = (uu___114_1083.primops);
            no_delta_steps = (uu___114_1083.no_delta_steps);
            unfold_until = (uu___114_1083.unfold_until);
            unfold_only = (uu___114_1083.unfold_only);
            unfold_attr = (uu___114_1083.unfold_attr);
            unfold_tac = (uu___114_1083.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1083.pure_subterms_within_computations);
            simplify = (uu___114_1083.simplify);
            erase_universes = (uu___114_1083.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___114_1083.reify_);
            compress_uvars = (uu___114_1083.compress_uvars);
            no_full_norm = (uu___114_1083.no_full_norm);
            check_no_uvars = (uu___114_1083.check_no_uvars);
            unmeta = (uu___114_1083.unmeta);
            unascribe = (uu___114_1083.unascribe)
          }
      | Reify ->
          let uu___115_1084 = fs in
          {
            beta = (uu___115_1084.beta);
            iota = (uu___115_1084.iota);
            zeta = (uu___115_1084.zeta);
            weak = (uu___115_1084.weak);
            hnf = (uu___115_1084.hnf);
            primops = (uu___115_1084.primops);
            no_delta_steps = (uu___115_1084.no_delta_steps);
            unfold_until = (uu___115_1084.unfold_until);
            unfold_only = (uu___115_1084.unfold_only);
            unfold_attr = (uu___115_1084.unfold_attr);
            unfold_tac = (uu___115_1084.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1084.pure_subterms_within_computations);
            simplify = (uu___115_1084.simplify);
            erase_universes = (uu___115_1084.erase_universes);
            allow_unbound_universes = (uu___115_1084.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___115_1084.compress_uvars);
            no_full_norm = (uu___115_1084.no_full_norm);
            check_no_uvars = (uu___115_1084.check_no_uvars);
            unmeta = (uu___115_1084.unmeta);
            unascribe = (uu___115_1084.unascribe)
          }
      | CompressUvars ->
          let uu___116_1085 = fs in
          {
            beta = (uu___116_1085.beta);
            iota = (uu___116_1085.iota);
            zeta = (uu___116_1085.zeta);
            weak = (uu___116_1085.weak);
            hnf = (uu___116_1085.hnf);
            primops = (uu___116_1085.primops);
            no_delta_steps = (uu___116_1085.no_delta_steps);
            unfold_until = (uu___116_1085.unfold_until);
            unfold_only = (uu___116_1085.unfold_only);
            unfold_attr = (uu___116_1085.unfold_attr);
            unfold_tac = (uu___116_1085.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1085.pure_subterms_within_computations);
            simplify = (uu___116_1085.simplify);
            erase_universes = (uu___116_1085.erase_universes);
            allow_unbound_universes = (uu___116_1085.allow_unbound_universes);
            reify_ = (uu___116_1085.reify_);
            compress_uvars = true;
            no_full_norm = (uu___116_1085.no_full_norm);
            check_no_uvars = (uu___116_1085.check_no_uvars);
            unmeta = (uu___116_1085.unmeta);
            unascribe = (uu___116_1085.unascribe)
          }
      | NoFullNorm ->
          let uu___117_1086 = fs in
          {
            beta = (uu___117_1086.beta);
            iota = (uu___117_1086.iota);
            zeta = (uu___117_1086.zeta);
            weak = (uu___117_1086.weak);
            hnf = (uu___117_1086.hnf);
            primops = (uu___117_1086.primops);
            no_delta_steps = (uu___117_1086.no_delta_steps);
            unfold_until = (uu___117_1086.unfold_until);
            unfold_only = (uu___117_1086.unfold_only);
            unfold_attr = (uu___117_1086.unfold_attr);
            unfold_tac = (uu___117_1086.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1086.pure_subterms_within_computations);
            simplify = (uu___117_1086.simplify);
            erase_universes = (uu___117_1086.erase_universes);
            allow_unbound_universes = (uu___117_1086.allow_unbound_universes);
            reify_ = (uu___117_1086.reify_);
            compress_uvars = (uu___117_1086.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___117_1086.check_no_uvars);
            unmeta = (uu___117_1086.unmeta);
            unascribe = (uu___117_1086.unascribe)
          }
      | CheckNoUvars ->
          let uu___118_1087 = fs in
          {
            beta = (uu___118_1087.beta);
            iota = (uu___118_1087.iota);
            zeta = (uu___118_1087.zeta);
            weak = (uu___118_1087.weak);
            hnf = (uu___118_1087.hnf);
            primops = (uu___118_1087.primops);
            no_delta_steps = (uu___118_1087.no_delta_steps);
            unfold_until = (uu___118_1087.unfold_until);
            unfold_only = (uu___118_1087.unfold_only);
            unfold_attr = (uu___118_1087.unfold_attr);
            unfold_tac = (uu___118_1087.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1087.pure_subterms_within_computations);
            simplify = (uu___118_1087.simplify);
            erase_universes = (uu___118_1087.erase_universes);
            allow_unbound_universes = (uu___118_1087.allow_unbound_universes);
            reify_ = (uu___118_1087.reify_);
            compress_uvars = (uu___118_1087.compress_uvars);
            no_full_norm = (uu___118_1087.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___118_1087.unmeta);
            unascribe = (uu___118_1087.unascribe)
          }
      | Unmeta ->
          let uu___119_1088 = fs in
          {
            beta = (uu___119_1088.beta);
            iota = (uu___119_1088.iota);
            zeta = (uu___119_1088.zeta);
            weak = (uu___119_1088.weak);
            hnf = (uu___119_1088.hnf);
            primops = (uu___119_1088.primops);
            no_delta_steps = (uu___119_1088.no_delta_steps);
            unfold_until = (uu___119_1088.unfold_until);
            unfold_only = (uu___119_1088.unfold_only);
            unfold_attr = (uu___119_1088.unfold_attr);
            unfold_tac = (uu___119_1088.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1088.pure_subterms_within_computations);
            simplify = (uu___119_1088.simplify);
            erase_universes = (uu___119_1088.erase_universes);
            allow_unbound_universes = (uu___119_1088.allow_unbound_universes);
            reify_ = (uu___119_1088.reify_);
            compress_uvars = (uu___119_1088.compress_uvars);
            no_full_norm = (uu___119_1088.no_full_norm);
            check_no_uvars = (uu___119_1088.check_no_uvars);
            unmeta = true;
            unascribe = (uu___119_1088.unascribe)
          }
      | Unascribe ->
          let uu___120_1089 = fs in
          {
            beta = (uu___120_1089.beta);
            iota = (uu___120_1089.iota);
            zeta = (uu___120_1089.zeta);
            weak = (uu___120_1089.weak);
            hnf = (uu___120_1089.hnf);
            primops = (uu___120_1089.primops);
            no_delta_steps = (uu___120_1089.no_delta_steps);
            unfold_until = (uu___120_1089.unfold_until);
            unfold_only = (uu___120_1089.unfold_only);
            unfold_attr = (uu___120_1089.unfold_attr);
            unfold_tac = (uu___120_1089.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1089.pure_subterms_within_computations);
            simplify = (uu___120_1089.simplify);
            erase_universes = (uu___120_1089.erase_universes);
            allow_unbound_universes = (uu___120_1089.allow_unbound_universes);
            reify_ = (uu___120_1089.reify_);
            compress_uvars = (uu___120_1089.compress_uvars);
            no_full_norm = (uu___120_1089.no_full_norm);
            check_no_uvars = (uu___120_1089.check_no_uvars);
            unmeta = (uu___120_1089.unmeta);
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
    match projectee with | Clos _0 -> true | uu____1395 -> false
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
    match projectee with | Univ _0 -> true | uu____1497 -> false
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Univ _0 -> _0
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee -> match projectee with | Dummy -> true | uu____1508 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option, closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option, closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy)
let (closure_to_string : closure -> Prims.string) =
  fun uu___80_1527 ->
    match uu___80_1527 with
    | Clos (uu____1528, t, uu____1530, uu____1531) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1576 -> "Univ"
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
             FStar_Util.psmap_add m1 (FStar_Ident.text_of_lid p.name) p) l m
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l ->
    let uu____1838 = FStar_Util.psmap_empty () in add_steps uu____1838 l
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun fv ->
      FStar_Util.psmap_try_find cfg.primitive_steps
        (FStar_Ident.text_of_lid
           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
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
    match projectee with | Arg _0 -> true | uu____2038 -> false
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure, FStar_Syntax_Syntax.aqual, FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee -> match projectee with | Arg _0 -> _0
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | UnivArgs _0 -> true | uu____2074 -> false
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list, FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | UnivArgs _0 -> _0
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | MemoLazy _0 -> true | uu____2110 -> false
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env, FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee -> match projectee with | MemoLazy _0 -> _0
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Match _0 -> true | uu____2251 -> false
let (__proj__Match__item___0 :
  stack_elt ->
    (env, branches, FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Abs _0 -> true | uu____2293 -> false
let (__proj__Abs__item___0 :
  stack_elt ->
    (env, FStar_Syntax_Syntax.binders, env,
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee -> match projectee with | Abs _0 -> _0
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | App _0 -> true | uu____2349 -> false
let (__proj__App__item___0 :
  stack_elt ->
    (env, FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.aqual,
      FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee -> match projectee with | App _0 -> _0
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta _0 -> true | uu____2389 -> false
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata, FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Let _0 -> true | uu____2421 -> false
let (__proj__Let__item___0 :
  stack_elt ->
    (env, FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.letbinding,
      FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Cfg _0 -> true | uu____2457 -> false
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee -> match projectee with | Cfg _0 -> _0
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Debug _0 -> true | uu____2473 -> false
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term, FStar_Util.time)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____2498 = FStar_Syntax_Util.head_and_args' t in
    match uu____2498 with | (hd1, uu____2512) -> hd1
let mk :
  'Auu____2532 .
    'Auu____2532 ->
      FStar_Range.range -> 'Auu____2532 FStar_Syntax_Syntax.syntax
  = fun t -> fun r -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg ->
    fun r ->
      fun t ->
        if cfg.memoize_lazy
        then
          let uu____2634 = FStar_ST.op_Bang r in
          match uu____2634 with
          | FStar_Pervasives_Native.Some uu____2736 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env ->
    let uu____2844 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____2844 (FStar_String.concat "; ")
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___81_2851 ->
    match uu___81_2851 with
    | Arg (c, uu____2853, uu____2854) ->
        let uu____2855 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____2855
    | MemoLazy uu____2856 -> "MemoLazy"
    | Abs (uu____2863, bs, uu____2865, uu____2866, uu____2867) ->
        let uu____2872 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____2872
    | UnivArgs uu____2877 -> "UnivArgs"
    | Match uu____2884 -> "Match"
    | App (uu____2891, t, uu____2893, uu____2894) ->
        let uu____2895 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____2895
    | Meta (m, uu____2897) -> "Meta"
    | Let uu____2898 -> "Let"
    | Cfg uu____2907 -> "Cfg"
    | Debug (t, uu____2909) ->
        let uu____2910 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____2910
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s ->
    let uu____2918 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____2918 (FStar_String.concat "; ")
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg -> fun f -> if (cfg.debug).gen then f () else ()
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg -> fun f -> if (cfg.debug).primop then f () else ()
let is_empty : 'Auu____2949 . 'Auu____2949 Prims.list -> Prims.bool =
  fun uu___82_2955 ->
    match uu___82_2955 with | [] -> true | uu____2958 -> false
let lookup_bvar :
  'Auu____2965 'Auu____2966 .
    ('Auu____2965, 'Auu____2966) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2966
  =
  fun env ->
    fun x ->
      try
        let uu____2990 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____2990
      with
      | uu____3003 ->
          let uu____3004 =
            let uu____3005 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____3005 in
          failwith uu____3004
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l ->
    if FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid
      then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid
        then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
        else FStar_Pervasives_Native.None
let (norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg ->
    fun env ->
      fun u ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____3042 =
            FStar_List.fold_left
              (fun uu____3068 ->
                 fun u1 ->
                   match uu____3068 with
                   | (cur_kernel, cur_max, out) ->
                       let uu____3093 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____3093 with
                        | (k_u, n1) ->
                            let uu____3108 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____3108
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____3042 with
          | (uu____3126, u1, out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3151 =
                   let uu____3152 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____3152 in
                 match uu____3151 with
                 | Univ u3 -> aux u3
                 | Dummy -> [u2]
                 | uu____3170 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3178 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3184 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3193 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3202 -> [u2]
          | FStar_Syntax_Syntax.U_unknown -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3209 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____3209 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____3226 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____3226 with
                    | (FStar_Syntax_Syntax.U_zero, n1) ->
                        let uu____3234 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3 ->
                                  let uu____3242 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____3242 with
                                  | (uu____3247, m) -> n1 <= m)) in
                        if uu____3234 then rest1 else us1
                    | uu____3252 -> us1)
               | uu____3257 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3261 = aux u3 in
              FStar_List.map (fun _0_40 -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3261 in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3265 = aux u in
           match uu____3265 with
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
          (fun uu____3369 ->
             let uu____3370 = FStar_Syntax_Print.tag_of_term t in
             let uu____3371 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3370
               uu____3371);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3378 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3380 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3405 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3406 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3407 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3408 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3409 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3426 =
                      let uu____3427 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____3428 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3427 uu____3428 in
                    failwith uu____3426
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3431 =
                    let uu____3432 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____3432 in
                  mk uu____3431 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
                  let uu____3439 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3439
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3441 = lookup_bvar env x in
                  (match uu____3441 with
                   | Univ uu____3444 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy -> t1
                   | Clos (env1, t0, uu____3447, uu____3448) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1, args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
                  let uu____3560 = closures_as_binders_delayed cfg env bs in
                  (match uu____3560 with
                   | (bs1, env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____3588 =
                         let uu____3589 =
                           let uu____3606 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____3606) in
                         FStar_Syntax_Syntax.Tm_abs uu____3589 in
                       mk uu____3588 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                  let uu____3637 = closures_as_binders_delayed cfg env bs in
                  (match uu____3637 with
                   | (bs1, env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
                  let uu____3679 =
                    let uu____3690 =
                      let uu____3697 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____3697] in
                    closures_as_binders_delayed cfg env uu____3690 in
                  (match uu____3679 with
                   | (x1, env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____3715 =
                         let uu____3716 =
                           let uu____3723 =
                             let uu____3724 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____3724
                               FStar_Pervasives_Native.fst in
                           (uu____3723, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____3716 in
                       mk uu____3715 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11, (annot, tacopt), lopt)
                  ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3815 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____3815
                    | FStar_Util.Inr c ->
                        let uu____3829 = close_comp cfg env c in
                        FStar_Util.Inr uu____3829 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____3845 =
                    let uu____3846 =
                      let uu____3873 = closure_as_term_delayed cfg env t11 in
                      (uu____3873, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3846 in
                  mk uu____3845 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_quoted (t', qi) ->
                  (match qi.FStar_Syntax_Syntax.qkind with
                   | FStar_Syntax_Syntax.Quote_dynamic ->
                       let uu____3914 =
                         let uu____3915 =
                           let uu____3922 =
                             closure_as_term_delayed cfg env t' in
                           (uu____3922, qi) in
                         FStar_Syntax_Syntax.Tm_quoted uu____3915 in
                       mk uu____3914 t1.FStar_Syntax_Syntax.pos
                   | FStar_Syntax_Syntax.Quote_static ->
                       let qi1 =
                         FStar_Syntax_Syntax.on_antiquoted
                           (closure_as_term_delayed cfg env) qi in
                       mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta
                  (t', FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3946 =
                    let uu____3947 =
                      let uu____3954 = closure_as_term_delayed cfg env t' in
                      let uu____3957 =
                        let uu____3958 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____3958 in
                      (uu____3954, uu____3957) in
                    FStar_Syntax_Syntax.Tm_meta uu____3947 in
                  mk uu____3946 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) ->
                  let uu____4018 =
                    let uu____4019 =
                      let uu____4026 = closure_as_term_delayed cfg env t' in
                      let uu____4029 =
                        let uu____4030 =
                          let uu____4037 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____4037) in
                        FStar_Syntax_Syntax.Meta_monadic uu____4030 in
                      (uu____4026, uu____4029) in
                    FStar_Syntax_Syntax.Tm_meta uu____4019 in
                  mk uu____4018 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t', FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody))
                  ->
                  let uu____4056 =
                    let uu____4057 =
                      let uu____4064 = closure_as_term_delayed cfg env t' in
                      let uu____4067 =
                        let uu____4068 =
                          let uu____4077 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____4077) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____4068 in
                      (uu____4064, uu____4067) in
                    FStar_Syntax_Syntax.Tm_meta uu____4057 in
                  mk uu____4056 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t', m) ->
                  let uu____4090 =
                    let uu____4091 =
                      let uu____4098 = closure_as_term_delayed cfg env t' in
                      (uu____4098, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____4091 in
                  mk uu____4090 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1 -> fun uu____4138 -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____4157 =
                    let uu____4168 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____4168
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____4187 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___125_4199 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_4199.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_4199.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____4187)) in
                  (match uu____4157 with
                   | (nm, body1) ->
                       let lb1 =
                         let uu___126_4215 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___126_4215.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___126_4215.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___126_4215.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___126_4215.FStar_Syntax_Syntax.lbpos)
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____4226, lbs), body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____4285 -> fun env2 -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____4310 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____4310
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4330 -> fun env2 -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____4352 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____4352
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___127_4364 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_4364.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_4364.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41 -> FStar_Util.Inl _0_41)) in
                    let uu___128_4365 = lb in
                    let uu____4366 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___128_4365.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___128_4365.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4366;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___128_4365.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___128_4365.FStar_Syntax_Syntax.lbpos)
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4396 -> fun env1 -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1, branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____4485 =
                    match uu____4485 with
                    | (pat, w_opt, tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4540 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                              let uu____4561 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4621 ->
                                        fun uu____4622 ->
                                          match (uu____4621, uu____4622) with
                                          | ((pats1, env3), (p1, b)) ->
                                              let uu____4713 =
                                                norm_pat env3 p1 in
                                              (match uu____4713 with
                                               | (p2, env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____4561 with
                               | (pats1, env3) ->
                                   ((let uu___129_4795 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___129_4795.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___130_4814 = x in
                                let uu____4815 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___130_4814.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___130_4814.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4815
                                } in
                              ((let uu___131_4829 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___131_4829.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___132_4840 = x in
                                let uu____4841 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___132_4840.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___132_4840.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4841
                                } in
                              ((let uu___133_4855 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___133_4855.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x, t2) ->
                              let x1 =
                                let uu___134_4871 = x in
                                let uu____4872 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___134_4871.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___134_4871.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4872
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___135_4879 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___135_4879.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____4882 = norm_pat env1 pat in
                        (match uu____4882 with
                         | (pat1, env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4911 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____4911 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____4917 =
                    let uu____4918 =
                      let uu____4941 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____4941) in
                    FStar_Syntax_Syntax.Tm_match uu____4918 in
                  mk uu____4917 t1.FStar_Syntax_Syntax.pos))
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
        | uu____5027 -> closure_as_term cfg env t
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
        | uu____5053 ->
            FStar_List.map
              (fun uu____5070 ->
                 match uu____5070 with
                 | (x, imp) ->
                     let uu____5089 = closure_as_term_delayed cfg env x in
                     (uu____5089, imp)) args
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
        let uu____5103 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5152 ->
                  fun uu____5153 ->
                    match (uu____5152, uu____5153) with
                    | ((env1, out), (b, imp)) ->
                        let b1 =
                          let uu___136_5223 = b in
                          let uu____5224 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___136_5223.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___136_5223.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5224
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____5103 with | (env1, bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____5317 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t, uopt) ->
                 let uu____5330 = closure_as_term_delayed cfg env t in
                 let uu____5331 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____5330 uu____5331
             | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                 let uu____5344 = closure_as_term_delayed cfg env t in
                 let uu____5345 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5344 uu____5345
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
                        (fun uu___83_5371 ->
                           match uu___83_5371 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5375 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____5375
                           | f -> f)) in
                 let uu____5379 =
                   let uu___137_5380 = c1 in
                   let uu____5381 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5381;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___137_5380.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____5379)
and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1 ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___84_5391 ->
            match uu___84_5391 with
            | FStar_Syntax_Syntax.DECREASES uu____5392 -> false
            | uu____5395 -> true))
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
                   (fun uu___85_5413 ->
                      match uu___85_5413 with
                      | FStar_Syntax_Syntax.DECREASES uu____5414 -> false
                      | uu____5417 -> true)) in
            let rc1 =
              let uu___138_5419 = rc in
              let uu____5420 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___138_5419.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5420;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____5427 -> lopt
let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
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
    let uu____5512 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5512 in
  let arg_as_bounded_int uu____5540 =
    match uu____5540 with
    | (a, uu____5552) ->
        let uu____5559 =
          let uu____5560 = FStar_Syntax_Subst.compress a in
          uu____5560.FStar_Syntax_Syntax.n in
        (match uu____5559 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5570;
                FStar_Syntax_Syntax.vars = uu____5571;_},
              ({
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_int (i, FStar_Pervasives_Native.None));
                 FStar_Syntax_Syntax.pos = uu____5573;
                 FStar_Syntax_Syntax.vars = uu____5574;_},
               uu____5575)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5614 =
               let uu____5619 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____5619) in
             FStar_Pervasives_Native.Some uu____5614
         | uu____5624 -> FStar_Pervasives_Native.None) in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5664 = f a in FStar_Pervasives_Native.Some uu____5664
    | uu____5665 -> FStar_Pervasives_Native.None in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5713 = f a0 a1 in FStar_Pervasives_Native.Some uu____5713
    | uu____5714 -> FStar_Pervasives_Native.None in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a ->
          fun as_a ->
            fun f ->
              fun res ->
                fun args ->
                  let uu____5756 = FStar_List.map as_a args in
                  lift_unary () ()
                    (fun a415 -> (Obj.magic (f res.psc_range)) a415)
                    uu____5756)) a416 a417 a418 a419 a420 in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a ->
          fun as_a ->
            fun f ->
              fun res ->
                fun args ->
                  let uu____5805 = FStar_List.map as_a args in
                  lift_binary () ()
                    (fun a421 ->
                       fun a422 -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5805)) a423 a424 a425 a426 a427 in
  let as_primitive_step is_strong uu____5832 =
    match uu____5832 with
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
    unary_op () (fun a428 -> (Obj.magic arg_as_int) a428)
      (fun a429 ->
         fun a430 ->
           (Obj.magic
              (fun r ->
                 fun x ->
                   let uu____5880 = f x in
                   FStar_Syntax_Embeddings.embed_int r uu____5880)) a429 a430) in
  let binary_int_op f =
    binary_op () (fun a431 -> (Obj.magic arg_as_int) a431)
      (fun a432 ->
         fun a433 ->
           fun a434 ->
             (Obj.magic
                (fun r ->
                   fun x ->
                     fun y ->
                       let uu____5908 = f x y in
                       FStar_Syntax_Embeddings.embed_int r uu____5908)) a432
               a433 a434) in
  let unary_bool_op f =
    unary_op () (fun a435 -> (Obj.magic arg_as_bool) a435)
      (fun a436 ->
         fun a437 ->
           (Obj.magic
              (fun r ->
                 fun x ->
                   let uu____5929 = f x in
                   FStar_Syntax_Embeddings.embed_bool r uu____5929)) a436
             a437) in
  let binary_bool_op f =
    binary_op () (fun a438 -> (Obj.magic arg_as_bool) a438)
      (fun a439 ->
         fun a440 ->
           fun a441 ->
             (Obj.magic
                (fun r ->
                   fun x ->
                     fun y ->
                       let uu____5957 = f x y in
                       FStar_Syntax_Embeddings.embed_bool r uu____5957)) a439
               a440 a441) in
  let binary_string_op f =
    binary_op () (fun a442 -> (Obj.magic arg_as_string) a442)
      (fun a443 ->
         fun a444 ->
           fun a445 ->
             (Obj.magic
                (fun r ->
                   fun x ->
                     fun y ->
                       let uu____5985 = f x y in
                       FStar_Syntax_Embeddings.embed_string r uu____5985))
               a443 a444 a445) in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____6093 =
          let uu____6102 = as_a a in
          let uu____6105 = as_b b in (uu____6102, uu____6105) in
        (match uu____6093 with
         | (FStar_Pervasives_Native.Some a1, FStar_Pervasives_Native.Some b1)
             ->
             let uu____6120 =
               let uu____6121 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____6121 in
             FStar_Pervasives_Native.Some uu____6120
         | uu____6122 -> FStar_Pervasives_Native.None)
    | uu____6131 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____6145 =
        let uu____6146 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____6146 in
      mk uu____6145 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____6156 =
      let uu____6159 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____6159 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____6156 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____6191 =
      let uu____6192 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____6192 in
    FStar_Syntax_Embeddings.embed_int rng uu____6191 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____6210 = arg_as_string a1 in
        (match uu____6210 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6216 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2) in
             (match uu____6216 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____6229 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____6229
              | uu____6230 -> FStar_Pervasives_Native.None)
         | uu____6235 -> FStar_Pervasives_Native.None)
    | uu____6238 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____6248 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____6248 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6277 =
          let uu____6298 = arg_as_string fn in
          let uu____6301 = arg_as_int from_line in
          let uu____6304 = arg_as_int from_col in
          let uu____6307 = arg_as_int to_line in
          let uu____6310 = arg_as_int to_col in
          (uu____6298, uu____6301, uu____6304, uu____6307, uu____6310) in
        (match uu____6277 with
         | (FStar_Pervasives_Native.Some fn1, FStar_Pervasives_Native.Some
            from_l, FStar_Pervasives_Native.Some from_c,
            FStar_Pervasives_Native.Some to_l, FStar_Pervasives_Native.Some
            to_c) ->
             let r =
               let uu____6341 =
                 let uu____6342 = FStar_BigInt.to_int_fs from_l in
                 let uu____6343 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____6342 uu____6343 in
               let uu____6344 =
                 let uu____6345 = FStar_BigInt.to_int_fs to_l in
                 let uu____6346 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____6345 uu____6346 in
               FStar_Range.mk_range fn1 uu____6341 uu____6344 in
             let uu____6347 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r in
             FStar_Pervasives_Native.Some uu____6347
         | uu____6348 -> FStar_Pervasives_Native.None)
    | uu____6369 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ, uu____6396)::(a1, uu____6398)::(a2, uu____6400)::[] ->
        let uu____6437 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6437 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6450 -> FStar_Pervasives_Native.None)
    | uu____6451 -> failwith "Unexpected number of arguments" in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1, uu____6478)::[] ->
        let uu____6487 = FStar_Syntax_Embeddings.unembed_range_safe a1 in
        (match uu____6487 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6493 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r in
             FStar_Pervasives_Native.Some uu____6493
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    | uu____6494 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____6518 =
      let uu____6533 =
        let uu____6548 =
          let uu____6563 =
            let uu____6578 =
              let uu____6593 =
                let uu____6608 =
                  let uu____6623 =
                    let uu____6638 =
                      let uu____6653 =
                        let uu____6668 =
                          let uu____6683 =
                            let uu____6698 =
                              let uu____6713 =
                                let uu____6728 =
                                  let uu____6743 =
                                    let uu____6758 =
                                      let uu____6773 =
                                        let uu____6788 =
                                          let uu____6803 =
                                            let uu____6818 =
                                              let uu____6833 =
                                                let uu____6846 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"] in
                                                (uu____6846,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a446 ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a446)
                                                     (fun a447 ->
                                                        fun a448 ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a447 a448))) in
                                              let uu____6853 =
                                                let uu____6868 =
                                                  let uu____6881 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"] in
                                                  (uu____6881,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a449 ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a449)
                                                       (fun a450 ->
                                                          fun a451 ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a450 a451))) in
                                                let uu____6888 =
                                                  let uu____6903 =
                                                    let uu____6918 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"] in
                                                    (uu____6918,
                                                      (Prims.parse_int "2"),
                                                      string_concat') in
                                                  let uu____6927 =
                                                    let uu____6944 =
                                                      let uu____6959 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"] in
                                                      (uu____6959,
                                                        (Prims.parse_int "5"),
                                                        mk_range1) in
                                                    [uu____6944] in
                                                  uu____6903 :: uu____6927 in
                                                uu____6868 :: uu____6888 in
                                              uu____6833 :: uu____6853 in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6818 in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6803 in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a452 ->
                                                (Obj.magic arg_as_string)
                                                  a452)
                                             (fun a453 ->
                                                fun a454 ->
                                                  fun a455 ->
                                                    (Obj.magic
                                                       string_compare') a453
                                                      a454 a455)))
                                          :: uu____6788 in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a456 ->
                                              (Obj.magic arg_as_bool) a456)
                                           (fun a457 ->
                                              fun a458 ->
                                                (Obj.magic string_of_bool1)
                                                  a457 a458)))
                                        :: uu____6773 in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a459 ->
                                            (Obj.magic arg_as_int) a459)
                                         (fun a460 ->
                                            fun a461 ->
                                              (Obj.magic string_of_int1) a460
                                                a461)))
                                      :: uu____6758 in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a462 ->
                                          (Obj.magic arg_as_int) a462)
                                       (fun a463 ->
                                          (Obj.magic arg_as_char) a463)
                                       (fun a464 ->
                                          fun a465 ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a464 a465)
                                       (fun a466 ->
                                          fun a467 ->
                                            fun a468 ->
                                              (Obj.magic
                                                 (fun r ->
                                                    fun x ->
                                                      fun y ->
                                                        let uu____7150 =
                                                          FStar_BigInt.to_int_fs
                                                            x in
                                                        FStar_String.make
                                                          uu____7150 y)) a466
                                                a467 a468)))
                                    :: uu____6743 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x -> fun y -> Prims.strcat x y)))
                                  :: uu____6728 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x -> fun y -> Prims.strcat x y)))
                                :: uu____6713 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x -> fun y -> x || y))) ::
                              uu____6698 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x -> fun y -> x && y))) ::
                            uu____6683 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x -> Prims.op_Negation x))) ::
                          uu____6668 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x -> fun y -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6653 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op () (fun a469 -> (Obj.magic arg_as_int) a469)
                         (fun a470 ->
                            fun a471 ->
                              fun a472 ->
                                (Obj.magic
                                   (fun r ->
                                      fun x ->
                                        fun y ->
                                          let uu____7317 =
                                            FStar_BigInt.ge_big_int x y in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7317)) a470 a471 a472)))
                      :: uu____6638 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a473 -> (Obj.magic arg_as_int) a473)
                       (fun a474 ->
                          fun a475 ->
                            fun a476 ->
                              (Obj.magic
                                 (fun r ->
                                    fun x ->
                                      fun y ->
                                        let uu____7343 =
                                          FStar_BigInt.gt_big_int x y in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7343)) a474 a475 a476)))
                    :: uu____6623 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a477 -> (Obj.magic arg_as_int) a477)
                     (fun a478 ->
                        fun a479 ->
                          fun a480 ->
                            (Obj.magic
                               (fun r ->
                                  fun x ->
                                    fun y ->
                                      let uu____7369 =
                                        FStar_BigInt.le_big_int x y in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7369)) a478 a479 a480)))
                  :: uu____6608 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a481 -> (Obj.magic arg_as_int) a481)
                   (fun a482 ->
                      fun a483 ->
                        fun a484 ->
                          (Obj.magic
                             (fun r ->
                                fun x ->
                                  fun y ->
                                    let uu____7395 =
                                      FStar_BigInt.lt_big_int x y in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7395)) a482 a483 a484)))
                :: uu____6593 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x -> fun y -> FStar_BigInt.div_big_int x y)))
              :: uu____6578 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x -> fun y -> FStar_BigInt.mult_big_int x y)))
            :: uu____6563 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x -> fun y -> FStar_BigInt.sub_big_int x y)))
          :: uu____6548 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x -> fun y -> FStar_BigInt.add_big_int x y))) ::
        uu____6533 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x -> FStar_BigInt.minus_big_int x))) :: uu____6518 in
  let weak_ops =
    let uu____7534 =
      let uu____7553 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"] in
      (uu____7553, (Prims.parse_int "1"), prims_to_fstar_range_step) in
    [uu____7534] in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____7637 =
        let uu____7638 =
          let uu____7639 = FStar_Syntax_Syntax.as_arg c in [uu____7639] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7638 in
      uu____7637 FStar_Pervasives_Native.None r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m ->
              let uu____7689 =
                let uu____7702 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                (uu____7702, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485 -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486 ->
                        fun a487 ->
                          fun a488 ->
                            (Obj.magic
                               (fun r ->
                                  fun uu____7718 ->
                                    fun uu____7719 ->
                                      match (uu____7718, uu____7719) with
                                      | ((int_to_t1, x), (uu____7738, y)) ->
                                          let uu____7748 =
                                            FStar_BigInt.add_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____7748)) a486 a487 a488))) in
              let uu____7749 =
                let uu____7764 =
                  let uu____7777 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  (uu____7777, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489 -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490 ->
                          fun a491 ->
                            fun a492 ->
                              (Obj.magic
                                 (fun r ->
                                    fun uu____7793 ->
                                      fun uu____7794 ->
                                        match (uu____7793, uu____7794) with
                                        | ((int_to_t1, x), (uu____7813, y))
                                            ->
                                            let uu____7823 =
                                              FStar_BigInt.sub_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____7823)) a490 a491 a492))) in
                let uu____7824 =
                  let uu____7839 =
                    let uu____7852 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    (uu____7852, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493 -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494 ->
                            fun a495 ->
                              fun a496 ->
                                (Obj.magic
                                   (fun r ->
                                      fun uu____7868 ->
                                        fun uu____7869 ->
                                          match (uu____7868, uu____7869) with
                                          | ((int_to_t1, x), (uu____7888, y))
                                              ->
                                              let uu____7898 =
                                                FStar_BigInt.mult_big_int x y in
                                              int_as_bounded r int_to_t1
                                                uu____7898)) a494 a495 a496))) in
                  let uu____7899 =
                    let uu____7914 =
                      let uu____7927 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      (uu____7927, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497 -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498 ->
                              fun a499 ->
                                (Obj.magic
                                   (fun r ->
                                      fun uu____7939 ->
                                        match uu____7939 with
                                        | (int_to_t1, x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499))) in
                    [uu____7914] in
                  uu____7839 :: uu____7899 in
                uu____7764 :: uu____7824 in
              uu____7689 :: uu____7749)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m ->
              let uu____8053 =
                let uu____8066 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                (uu____8066, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500 -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501 ->
                        fun a502 ->
                          fun a503 ->
                            (Obj.magic
                               (fun r ->
                                  fun uu____8082 ->
                                    fun uu____8083 ->
                                      match (uu____8082, uu____8083) with
                                      | ((int_to_t1, x), (uu____8102, y)) ->
                                          let uu____8112 =
                                            FStar_BigInt.div_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____8112)) a501 a502 a503))) in
              let uu____8113 =
                let uu____8128 =
                  let uu____8141 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  (uu____8141, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504 -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505 ->
                          fun a506 ->
                            fun a507 ->
                              (Obj.magic
                                 (fun r ->
                                    fun uu____8157 ->
                                      fun uu____8158 ->
                                        match (uu____8157, uu____8158) with
                                        | ((int_to_t1, x), (uu____8177, y))
                                            ->
                                            let uu____8187 =
                                              FStar_BigInt.mod_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____8187)) a505 a506 a507))) in
                [uu____8128] in
              uu____8053 :: uu____8113)) in
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
    | (_typ, uu____8299)::(a1, uu____8301)::(a2, uu____8303)::[] ->
        let uu____8340 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____8340 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___139_8346 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8346.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8346.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___140_8350 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8350.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8350.FStar_Syntax_Syntax.vars)
                })
         | uu____8351 -> FStar_Pervasives_Native.None)
    | (_typ, uu____8353)::uu____8354::(a1, uu____8356)::(a2, uu____8358)::[]
        ->
        let uu____8407 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____8407 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___139_8413 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8413.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8413.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___140_8417 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8417.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8417.FStar_Syntax_Syntax.vars)
                })
         | uu____8418 -> FStar_Pervasives_Native.None)
    | uu____8419 -> failwith "Unexpected number of arguments" in
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
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.unembedder
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____8519 = FStar_ST.op_Bang unembed_binder_knot in
    match uu____8519 with
    | FStar_Pervasives_Native.Some f -> f t
    | FStar_Pervasives_Native.None ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
let mk_psc_subst :
  'Auu____8572 .
    cfg ->
      ((FStar_Syntax_Syntax.bv, 'Auu____8572) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,
        closure) FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg ->
    fun env ->
      FStar_List.fold_right
        (fun uu____8632 ->
           fun subst1 ->
             match uu____8632 with
             | (binder_opt, closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b, Clos
                     (env1, term, uu____8673, uu____8674)) ->
                      let uu____8733 = b in
                      (match uu____8733 with
                       | (bv, uu____8741) ->
                           let uu____8742 =
                             let uu____8743 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid in
                             Prims.op_Negation uu____8743 in
                           if uu____8742
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____8748 = unembed_binder term1 in
                              match uu____8748 with
                              | FStar_Pervasives_Native.None -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8755 =
                                      let uu___141_8756 = bv in
                                      let uu____8757 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___141_8756.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___141_8756.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8757
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____8755 in
                                  let b_for_x =
                                    let uu____8761 =
                                      let uu____8768 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8768) in
                                    FStar_Syntax_Syntax.NT uu____8761 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___86_8777 ->
                                         match uu___86_8777 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8778,
                                              {
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_name
                                                  b';
                                                FStar_Syntax_Syntax.pos =
                                                  uu____8780;
                                                FStar_Syntax_Syntax.vars =
                                                  uu____8781;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8786 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____8787 -> subst1)) env []
let reduce_primops :
  'Auu____8804 'Auu____8805 .
    cfg ->
      ((FStar_Syntax_Syntax.bv, 'Auu____8804) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,
        closure) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8805 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg ->
    fun env ->
      fun stack ->
        fun tm ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8847 = FStar_Syntax_Util.head_and_args tm in
             match uu____8847 with
             | (head1, args) ->
                 let uu____8884 =
                   let uu____8885 = FStar_Syntax_Util.un_uinst head1 in
                   uu____8885.FStar_Syntax_Syntax.n in
                 (match uu____8884 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8889 = find_prim_step cfg fv in
                      (match uu____8889 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8904 ->
                                   let uu____8905 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____8906 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____8913 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8905 uu____8906 uu____8913);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8918 ->
                                   let uu____8919 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8919);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8922 ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____8924 =
                                 prim_step.interpretation psc args in
                               match uu____8924 with
                               | FStar_Pervasives_Native.None ->
                                   (log_primops cfg
                                      (fun uu____8930 ->
                                         let uu____8931 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8931);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8937 ->
                                         let uu____8938 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____8939 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8938 uu____8939);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8940 ->
                           (log_primops cfg
                              (fun uu____8944 ->
                                 let uu____8945 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8945);
                            tm)
                       | FStar_Pervasives_Native.None -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8949 ->
                            let uu____8950 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8950);
                       (match args with
                        | (a1, uu____8952)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8969 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8981 ->
                            let uu____8982 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8982);
                       (match args with
                        | (t, uu____8984)::(r, uu____8986)::[] ->
                            let uu____9013 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____9013 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___142_9017 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___142_9017.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___142_9017.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None -> tm)
                        | uu____9020 -> tm))
                  | uu____9029 -> tm))
let reduce_equality :
  'Auu____9034 'Auu____9035 .
    cfg ->
      ((FStar_Syntax_Syntax.bv, 'Auu____9034) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,
        closure) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9035 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg ->
    fun tm ->
      reduce_primops
        (let uu___143_9073 = cfg in
         {
           steps =
             (let uu___144_9076 = default_steps in
              {
                beta = (uu___144_9076.beta);
                iota = (uu___144_9076.iota);
                zeta = (uu___144_9076.zeta);
                weak = (uu___144_9076.weak);
                hnf = (uu___144_9076.hnf);
                primops = true;
                no_delta_steps = (uu___144_9076.no_delta_steps);
                unfold_until = (uu___144_9076.unfold_until);
                unfold_only = (uu___144_9076.unfold_only);
                unfold_attr = (uu___144_9076.unfold_attr);
                unfold_tac = (uu___144_9076.unfold_tac);
                pure_subterms_within_computations =
                  (uu___144_9076.pure_subterms_within_computations);
                simplify = (uu___144_9076.simplify);
                erase_universes = (uu___144_9076.erase_universes);
                allow_unbound_universes =
                  (uu___144_9076.allow_unbound_universes);
                reify_ = (uu___144_9076.reify_);
                compress_uvars = (uu___144_9076.compress_uvars);
                no_full_norm = (uu___144_9076.no_full_norm);
                check_no_uvars = (uu___144_9076.check_no_uvars);
                unmeta = (uu___144_9076.unmeta);
                unascribe = (uu___144_9076.unascribe)
              });
           tcenv = (uu___143_9073.tcenv);
           debug = (uu___143_9073.debug);
           delta_level = (uu___143_9073.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___143_9073.strong);
           memoize_lazy = (uu___143_9073.memoize_lazy);
           normalize_pure_lets = (uu___143_9073.normalize_pure_lets)
         }) tm
let is_norm_request :
  'Auu____9080 .
    FStar_Syntax_Syntax.term -> 'Auu____9080 Prims.list -> Prims.bool
  =
  fun hd1 ->
    fun args ->
      let uu____9093 =
        let uu____9100 =
          let uu____9101 = FStar_Syntax_Util.un_uinst hd1 in
          uu____9101.FStar_Syntax_Syntax.n in
        (uu____9100, args) in
      match uu____9093 with
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____9107::uu____9108::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____9112::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv, steps::uu____9117::uu____9118::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____9121 -> false
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___87_9132 ->
    match uu___87_9132 with
    | FStar_Syntax_Embeddings.Zeta -> [Zeta]
    | FStar_Syntax_Embeddings.Iota -> [Iota]
    | FStar_Syntax_Embeddings.Delta ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl -> [Simplify]
    | FStar_Syntax_Embeddings.Weak -> [Weak]
    | FStar_Syntax_Embeddings.HNF -> [HNF]
    | FStar_Syntax_Embeddings.Primops -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____9138 =
          let uu____9141 =
            let uu____9142 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____9142 in
          [uu____9141] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9138
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s -> FStar_List.concatMap tr_norm_step s
let get_norm_request :
  'Auu____9158 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term, 'Auu____9158) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list, FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm ->
    fun args ->
      let parse_steps s =
        try
          let uu____9211 =
            let uu____9214 =
              let uu____9217 =
                let uu____9222 =
                  FStar_Syntax_Embeddings.unembed_list_safe
                    FStar_Syntax_Embeddings.unembed_norm_step in
                uu____9222 s in
              FStar_All.pipe_right uu____9217 FStar_Util.must in
            FStar_All.pipe_right uu____9214 tr_norm_steps in
          FStar_Pervasives_Native.Some uu____9211
        with | uu____9250 -> FStar_Pervasives_Native.None in
      match args with
      | uu____9261::(tm, uu____9263)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm, uu____9292)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps, uu____9313)::uu____9314::(tm, uu____9316)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s in
          let uu____9353 =
            let uu____9358 = full_norm steps in parse_steps uu____9358 in
          (match uu____9353 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s in
               let s2 = add_exclude s1 Zeta in
               let s3 = add_exclude s2 Iota in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9397 -> FStar_Pervasives_Native.None
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___88_9414 ->
    match uu___88_9414 with
    | (App
        (uu____9417,
         {
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify);
           FStar_Syntax_Syntax.pos = uu____9418;
           FStar_Syntax_Syntax.vars = uu____9419;_},
         uu____9420, uu____9421))::uu____9422
        -> true
    | uu____9429 -> false
let firstn :
  'Auu____9435 .
    Prims.int ->
      'Auu____9435 Prims.list ->
        ('Auu____9435 Prims.list, 'Auu____9435 Prims.list)
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
          (uu____9471,
           {
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify);
             FStar_Syntax_Syntax.pos = uu____9472;
             FStar_Syntax_Syntax.vars = uu____9473;_},
           uu____9474, uu____9475))::uu____9476
          -> (cfg.steps).reify_
      | uu____9483 -> false
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9667 ->
                   let uu____9692 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9692
               | uu____9693 -> ())
            else ();
            FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____9701 ->
               let uu____9702 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____9703 = FStar_Syntax_Print.term_to_string t1 in
               let uu____9704 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____9711 =
                 let uu____9712 =
                   let uu____9715 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9715 in
                 stack_to_string uu____9712 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____9702 uu____9703 uu____9704 uu____9711);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____9738 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____9739 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____9740 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9741;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant;
                 FStar_Syntax_Syntax.fv_qual = uu____9742;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9745;
                 FStar_Syntax_Syntax.fv_delta = uu____9746;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9747;
                 FStar_Syntax_Syntax.fv_delta = uu____9748;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9749);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____9756 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1, args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___147_9792 = cfg in
                 {
                   steps =
                     (let uu___148_9795 = cfg.steps in
                      {
                        beta = (uu___148_9795.beta);
                        iota = (uu___148_9795.iota);
                        zeta = (uu___148_9795.zeta);
                        weak = (uu___148_9795.weak);
                        hnf = (uu___148_9795.hnf);
                        primops = (uu___148_9795.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___148_9795.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___148_9795.unfold_attr);
                        unfold_tac = (uu___148_9795.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___148_9795.pure_subterms_within_computations);
                        simplify = (uu___148_9795.simplify);
                        erase_universes = (uu___148_9795.erase_universes);
                        allow_unbound_universes =
                          (uu___148_9795.allow_unbound_universes);
                        reify_ = (uu___148_9795.reify_);
                        compress_uvars = (uu___148_9795.compress_uvars);
                        no_full_norm = (uu___148_9795.no_full_norm);
                        check_no_uvars = (uu___148_9795.check_no_uvars);
                        unmeta = (uu___148_9795.unmeta);
                        unascribe = (uu___148_9795.unascribe)
                      });
                   tcenv = (uu___147_9792.tcenv);
                   debug = (uu___147_9792.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___147_9792.primitive_steps);
                   strong = (uu___147_9792.strong);
                   memoize_lazy = (uu___147_9792.memoize_lazy);
                   normalize_pure_lets = true
                 } in
               let uu____9798 = get_norm_request (norm cfg' env []) args in
               (match uu____9798 with
                | FStar_Pervasives_Native.None ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____9829 ->
                              fun stack1 ->
                                match uu____9829 with
                                | (a, aq) ->
                                    let uu____9841 =
                                      let uu____9842 =
                                        let uu____9849 =
                                          let uu____9850 =
                                            let uu____9881 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None in
                                            (env, a, uu____9881, false) in
                                          Clos uu____9850 in
                                        (uu____9849, aq,
                                          (t1.FStar_Syntax_Syntax.pos)) in
                                      Arg uu____9842 in
                                    uu____9841 :: stack1) args) in
                    (log cfg
                       (fun uu____10013 ->
                          let uu____10014 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args) in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10014);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s, tm) ->
                    let delta_level =
                      let uu____10036 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___89_10041 ->
                                match uu___89_10041 with
                                | UnfoldUntil uu____10042 -> true
                                | UnfoldOnly uu____10043 -> true
                                | uu____10046 -> false)) in
                      if uu____10036
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___149_10051 = cfg in
                      let uu____10052 = to_fsteps s in
                      {
                        steps = uu____10052;
                        tcenv = (uu___149_10051.tcenv);
                        debug = (uu___149_10051.debug);
                        delta_level;
                        primitive_steps = (uu___149_10051.primitive_steps);
                        strong = (uu___149_10051.strong);
                        memoize_lazy = (uu___149_10051.memoize_lazy);
                        normalize_pure_lets = true
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      if (cfg.debug).print_normalized
                      then
                        let uu____10061 =
                          let uu____10062 =
                            let uu____10067 = FStar_Util.now () in
                            (t1, uu____10067) in
                          Debug uu____10062 in
                        uu____10061 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____10071 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____10071
           | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10080 =
                      let uu____10087 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____10087, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____10080 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____10097 = FStar_Syntax_Syntax.lid_of_fv fv in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____10097 in
               let uu____10098 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo in
               if uu____10098
               then
                 let b = should_reify cfg stack in
                 (log cfg
                    (fun uu____10104 ->
                       let uu____10105 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10106 = FStar_Util.string_of_bool b in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____10105 uu____10106);
                  if b
                  then
                    (let uu____10107 = FStar_List.tl stack in
                     do_unfold_fv cfg env uu____10107 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____10115 = find_prim_step cfg fv in
                     FStar_Option.isNone uu____10115) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___90_10121 ->
                               match uu___90_10121 with
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
                          (let uu____10131 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs in
                           Prims.op_Negation uu____10131))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None,
                                FStar_Pervasives_Native.Some uu____10150) ->
                                 false
                             | (FStar_Pervasives_Native.Some ats,
                                FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____10185, uu____10186) -> false))) in
                  log cfg
                    (fun uu____10208 ->
                       let uu____10209 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10210 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____10211 =
                         FStar_Util.string_of_bool should_delta1 in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____10209
                         uu____10210 uu____10211);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10214 = lookup_bvar env x in
               (match uu____10214 with
                | Univ uu____10217 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy -> failwith "Term variable not found"
                | Clos (env1, t0, r, fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____10266 = FStar_ST.op_Bang r in
                      (match uu____10266 with
                       | FStar_Pervasives_Native.Some (env2, t') ->
                           (log cfg
                              (fun uu____10438 ->
                                 let uu____10439 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____10440 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10439
                                   uu____10440);
                            (let uu____10441 =
                               let uu____10442 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____10442.FStar_Syntax_Syntax.n in
                             match uu____10441 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10445 ->
                                 norm cfg env2 stack t'
                             | uu____10462 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
               (match stack with
                | (UnivArgs uu____10604)::uu____10605 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10614)::uu____10615 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c, uu____10625, uu____10626))::stack_rest ->
                    (match c with
                     | Univ uu____10630 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10639 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____10660 ->
                                    let uu____10661 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10661);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____10701 ->
                                    let uu____10702 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10702);
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
                       (fun uu____10828 ->
                          let uu____10829 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10829);
                     norm cfg env stack1 t1)
                | (Debug uu____10830)::uu____10831 ->
                    if (cfg.steps).weak
                    then
                      let uu____10838 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____10838
                    else
                      (let uu____10840 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10840 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____10882 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10919 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10919)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_10924 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_10924.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_10924.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10925 -> lopt in
                           (log cfg
                              (fun uu____10931 ->
                                 let uu____10932 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10932);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___151_10941 = cfg in
                               {
                                 steps = (uu___151_10941.steps);
                                 tcenv = (uu___151_10941.tcenv);
                                 debug = (uu___151_10941.debug);
                                 delta_level = (uu___151_10941.delta_level);
                                 primitive_steps =
                                   (uu___151_10941.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_10941.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_10941.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10952)::uu____10953 ->
                    if (cfg.steps).weak
                    then
                      let uu____10960 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____10960
                    else
                      (let uu____10962 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10962 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____11004 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____11041 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11041)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11046 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11046.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11046.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11047 -> lopt in
                           (log cfg
                              (fun uu____11053 ->
                                 let uu____11054 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11054);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___151_11063 = cfg in
                               {
                                 steps = (uu___151_11063.steps);
                                 tcenv = (uu___151_11063.tcenv);
                                 debug = (uu___151_11063.debug);
                                 delta_level = (uu___151_11063.delta_level);
                                 primitive_steps =
                                   (uu___151_11063.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11063.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11063.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11074)::uu____11075 ->
                    if (cfg.steps).weak
                    then
                      let uu____11086 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11086
                    else
                      (let uu____11088 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11088 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____11130 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____11167 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11167)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11172 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11172.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11172.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11173 -> lopt in
                           (log cfg
                              (fun uu____11179 ->
                                 let uu____11180 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11180);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___151_11189 = cfg in
                               {
                                 steps = (uu___151_11189.steps);
                                 tcenv = (uu___151_11189.tcenv);
                                 debug = (uu___151_11189.debug);
                                 delta_level = (uu___151_11189.delta_level);
                                 primitive_steps =
                                   (uu___151_11189.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11189.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11189.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11200)::uu____11201 ->
                    if (cfg.steps).weak
                    then
                      let uu____11212 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11212
                    else
                      (let uu____11214 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11214 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____11256 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____11293 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11293)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11298 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11298.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11298.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11299 -> lopt in
                           (log cfg
                              (fun uu____11305 ->
                                 let uu____11306 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11306);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___151_11315 = cfg in
                               {
                                 steps = (uu___151_11315.steps);
                                 tcenv = (uu___151_11315.tcenv);
                                 debug = (uu___151_11315.debug);
                                 delta_level = (uu___151_11315.delta_level);
                                 primitive_steps =
                                   (uu___151_11315.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11315.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11315.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11326)::uu____11327 ->
                    if (cfg.steps).weak
                    then
                      let uu____11342 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11342
                    else
                      (let uu____11344 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11344 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____11386 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____11423 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11423)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11428 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11428.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11428.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11429 -> lopt in
                           (log cfg
                              (fun uu____11435 ->
                                 let uu____11436 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11436);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___151_11445 = cfg in
                               {
                                 steps = (uu___151_11445.steps);
                                 tcenv = (uu___151_11445.tcenv);
                                 debug = (uu___151_11445.debug);
                                 delta_level = (uu___151_11445.delta_level);
                                 primitive_steps =
                                   (uu___151_11445.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11445.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11445.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____11456 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11456
                    else
                      (let uu____11458 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11458 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____11500 -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____11537 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11537)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11542 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11542.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11542.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11543 -> lopt in
                           (log cfg
                              (fun uu____11549 ->
                                 let uu____11550 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11550);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___151_11559 = cfg in
                               {
                                 steps = (uu___151_11559.steps);
                                 tcenv = (uu___151_11559.tcenv);
                                 debug = (uu___151_11559.debug);
                                 delta_level = (uu___151_11559.delta_level);
                                 primitive_steps =
                                   (uu___151_11559.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11559.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11559.normalize_pure_lets)
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
                      (fun uu____11608 ->
                         fun stack1 ->
                           match uu____11608 with
                           | (a, aq) ->
                               let uu____11620 =
                                 let uu____11621 =
                                   let uu____11628 =
                                     let uu____11629 =
                                       let uu____11660 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____11660, false) in
                                     Clos uu____11629 in
                                   (uu____11628, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____11621 in
                               uu____11620 :: stack1) args) in
               (log cfg
                  (fun uu____11792 ->
                     let uu____11793 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11793);
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
                             ((let uu___152_11829 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___152_11829.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___152_11829.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____11830 ->
                      let uu____11835 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11835)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____11838 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____11838 with
                  | (closing, f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____11869 =
                          let uu____11870 =
                            let uu____11877 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___153_11879 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___153_11879.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___153_11879.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11877) in
                          FStar_Syntax_Syntax.Tm_refine uu____11870 in
                        mk uu____11869 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
               if (cfg.steps).weak
               then
                 let uu____11898 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____11898
               else
                 (let uu____11900 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____11900 with
                  | (bs1, c1) ->
                      let c2 =
                        let uu____11908 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1 -> fun uu____11932 -> dummy :: env1)
                               env) in
                        norm_comp cfg uu____11908 c1 in
                      let t2 =
                        let uu____11954 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____11954 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) ->
               (match stack with
                | (Match uu____12065)::uu____12066 ->
                    (log cfg
                       (fun uu____12077 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12078)::uu____12079 ->
                    (log cfg
                       (fun uu____12090 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12091,
                     {
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify);
                       FStar_Syntax_Syntax.pos = uu____12092;
                       FStar_Syntax_Syntax.vars = uu____12093;_},
                     uu____12094, uu____12095))::uu____12096
                    ->
                    (log cfg
                       (fun uu____12105 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12106)::uu____12107 ->
                    (log cfg
                       (fun uu____12118 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12119 ->
                    (log cfg
                       (fun uu____12122 ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____12126 ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12143 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____12143
                         | FStar_Util.Inr c ->
                             let uu____12151 = norm_comp cfg env c in
                             FStar_Util.Inr uu____12151 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12164 =
                               let uu____12165 =
                                 let uu____12192 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____12192, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12165 in
                             mk uu____12164 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____12211 ->
                           let uu____12212 =
                             let uu____12213 =
                               let uu____12214 =
                                 let uu____12241 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____12241, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12214 in
                             mk uu____12213 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____12212))))
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
                         let uu____12351 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____12351 with
                         | (openings, lbunivs) ->
                             let cfg1 =
                               let uu___154_12371 = cfg in
                               let uu____12372 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___154_12371.steps);
                                 tcenv = uu____12372;
                                 debug = (uu___154_12371.debug);
                                 delta_level = (uu___154_12371.delta_level);
                                 primitive_steps =
                                   (uu___154_12371.primitive_steps);
                                 strong = (uu___154_12371.strong);
                                 memoize_lazy = (uu___154_12371.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_12371.normalize_pure_lets)
                               } in
                             let norm1 t2 =
                               let uu____12377 =
                                 let uu____12378 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____12378 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12377 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___155_12381 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___155_12381.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___155_12381.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___155_12381.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___155_12381.FStar_Syntax_Syntax.lbpos)
                             })) in
               let uu____12382 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____12382
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12393,
                 { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____12394;
                   FStar_Syntax_Syntax.lbunivs = uu____12395;
                   FStar_Syntax_Syntax.lbtyp = uu____12396;
                   FStar_Syntax_Syntax.lbeff = uu____12397;
                   FStar_Syntax_Syntax.lbdef = uu____12398;
                   FStar_Syntax_Syntax.lbattrs = uu____12399;
                   FStar_Syntax_Syntax.lbpos = uu____12400;_}::uu____12401),
                uu____12402)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12442 =
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
               if uu____12442
               then
                 let binder =
                   let uu____12444 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____12444 in
                 let env1 =
                   let uu____12454 =
                     let uu____12461 =
                       let uu____12462 =
                         let uu____12493 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12493,
                           false) in
                       Clos uu____12462 in
                     ((FStar_Pervasives_Native.Some binder), uu____12461) in
                   uu____12454 :: env in
                 (log cfg
                    (fun uu____12634 ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____12638 ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12639 = closure_as_term cfg env t1 in
                     rebuild cfg env stack uu____12639))
                 else
                   (let uu____12641 =
                      let uu____12646 =
                        let uu____12647 =
                          let uu____12648 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left in
                          FStar_All.pipe_right uu____12648
                            FStar_Syntax_Syntax.mk_binder in
                        [uu____12647] in
                      FStar_Syntax_Subst.open_term uu____12646 body in
                    match uu____12641 with
                    | (bs, body1) ->
                        (log cfg
                           (fun uu____12657 ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                          let lbname =
                            let x =
                              let uu____12665 = FStar_List.hd bs in
                              FStar_Pervasives_Native.fst uu____12665 in
                            FStar_Util.Inl
                              (let uu___156_12675 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___156_12675.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___156_12675.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }) in
                          log cfg
                            (fun uu____12678 ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___157_12680 = lb in
                             let uu____12681 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___157_12680.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___157_12680.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12681;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___157_12680.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___157_12680.FStar_Syntax_Syntax.lbpos)
                             } in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1 ->
                                     fun uu____12716 -> dummy :: env1) env) in
                           let stack1 = (Cfg cfg) :: stack in
                           let cfg1 =
                             let uu___158_12739 = cfg in
                             {
                               steps = (uu___158_12739.steps);
                               tcenv = (uu___158_12739.tcenv);
                               debug = (uu___158_12739.debug);
                               delta_level = (uu___158_12739.delta_level);
                               primitive_steps =
                                 (uu___158_12739.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___158_12739.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___158_12739.normalize_pure_lets)
                             } in
                           log cfg1
                             (fun uu____12742 ->
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
               let uu____12759 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____12759 with
                | (lbs1, body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____12795 =
                               let uu___159_12796 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___159_12796.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___159_12796.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____12795 in
                           let uu____12797 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____12797 with
                           | (xs, def_body, lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____12823 =
                                   FStar_List.map (fun uu____12839 -> dummy)
                                     lbs1 in
                                 let uu____12840 =
                                   let uu____12849 =
                                     FStar_List.map
                                       (fun uu____12869 -> dummy) xs1 in
                                   FStar_List.append uu____12849 env in
                                 FStar_List.append uu____12823 uu____12840 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12893 =
                                       let uu___160_12894 = rc in
                                       let uu____12895 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___160_12894.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12895;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___160_12894.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____12893
                                 | uu____12902 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___161_12906 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___161_12906.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___161_12906.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___161_12906.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___161_12906.FStar_Syntax_Syntax.lbpos)
                               }) lbs1 in
                    let env' =
                      let uu____12916 =
                        FStar_List.map (fun uu____12932 -> dummy) lbs2 in
                      FStar_List.append uu____12916 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____12940 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____12940 with
                     | (lbs3, body3) ->
                         let t2 =
                           let uu___162_12956 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___162_12956.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___162_12956.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs, body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____12983 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____12983
           | FStar_Syntax_Syntax.Tm_let (lbs, body) ->
               let uu____13002 =
                 FStar_List.fold_right
                   (fun lb ->
                      fun uu____13078 ->
                        match uu____13078 with
                        | (rec_env, memos, i) ->
                            let bv =
                              let uu___163_13199 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___163_13199.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___163_13199.FStar_Syntax_Syntax.sort)
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
               (match uu____13002 with
                | (rec_env, memos, uu____13508) ->
                    let uu____13561 =
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
                             let uu____13938 =
                               let uu____13945 =
                                 let uu____13946 =
                                   let uu____13977 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13977, false) in
                                 Clos uu____13946 in
                               (FStar_Pervasives_Native.None, uu____13945) in
                             uu____13938 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1, m) ->
               (log cfg
                  (fun uu____14135 ->
                     let uu____14136 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14136);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1, t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14158 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14160::uu____14161 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l, r, uu____14166) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____14189 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14203 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14203
                              | uu____14214 -> m in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14218 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14244 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14262 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____14279 =
                        let uu____14280 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos in
                        let uu____14281 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14280 uu____14281 in
                      failwith uu____14279
                    else rebuild cfg env stack t2
                | uu____14283 -> norm cfg env stack t2))
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
                let uu____14293 = FStar_Syntax_Syntax.range_of_fv f in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____14293 in
              let uu____14294 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo in
              match uu____14294 with
              | FStar_Pervasives_Native.None ->
                  (log cfg
                     (fun uu____14307 ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us, t) ->
                  (log cfg
                     (fun uu____14318 ->
                        let uu____14319 =
                          FStar_Syntax_Print.term_to_string t0 in
                        let uu____14320 = FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____14319 uu____14320);
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
                      | (UnivArgs (us', uu____14333))::stack1 ->
                          let env1 =
                            FStar_All.pipe_right us'
                              (FStar_List.fold_left
                                 (fun env1 ->
                                    fun u ->
                                      (FStar_Pervasives_Native.None,
                                        (Univ u))
                                      :: env1) env) in
                          norm cfg env1 stack1 t1
                      | uu____14388 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14391 ->
                          let uu____14394 =
                            let uu____14395 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14395 in
                          failwith uu____14394
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
                  let uu___164_14419 = cfg in
                  let uu____14420 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps in
                  {
                    steps = uu____14420;
                    tcenv = (uu___164_14419.tcenv);
                    debug = (uu___164_14419.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___164_14419.primitive_steps);
                    strong = (uu___164_14419.strong);
                    memoize_lazy = (uu___164_14419.memoize_lazy);
                    normalize_pure_lets =
                      (uu___164_14419.normalize_pure_lets)
                  }
                else
                  (let uu___165_14422 = cfg in
                   {
                     steps =
                       (let uu___166_14425 = cfg.steps in
                        {
                          beta = (uu___166_14425.beta);
                          iota = (uu___166_14425.iota);
                          zeta = false;
                          weak = (uu___166_14425.weak);
                          hnf = (uu___166_14425.hnf);
                          primops = (uu___166_14425.primops);
                          no_delta_steps = (uu___166_14425.no_delta_steps);
                          unfold_until = (uu___166_14425.unfold_until);
                          unfold_only = (uu___166_14425.unfold_only);
                          unfold_attr = (uu___166_14425.unfold_attr);
                          unfold_tac = (uu___166_14425.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___166_14425.pure_subterms_within_computations);
                          simplify = (uu___166_14425.simplify);
                          erase_universes = (uu___166_14425.erase_universes);
                          allow_unbound_universes =
                            (uu___166_14425.allow_unbound_universes);
                          reify_ = (uu___166_14425.reify_);
                          compress_uvars = (uu___166_14425.compress_uvars);
                          no_full_norm = (uu___166_14425.no_full_norm);
                          check_no_uvars = (uu___166_14425.check_no_uvars);
                          unmeta = (uu___166_14425.unmeta);
                          unascribe = (uu___166_14425.unascribe)
                        });
                     tcenv = (uu___165_14422.tcenv);
                     debug = (uu___165_14422.debug);
                     delta_level = (uu___165_14422.delta_level);
                     primitive_steps = (uu___165_14422.primitive_steps);
                     strong = (uu___165_14422.strong);
                     memoize_lazy = (uu___165_14422.memoize_lazy);
                     normalize_pure_lets =
                       (uu___165_14422.normalize_pure_lets)
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
                  (fun uu____14455 ->
                     let uu____14456 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____14457 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____14456
                       uu____14457);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2 in
                 let uu____14459 =
                   let uu____14460 = FStar_Syntax_Subst.compress head3 in
                   uu____14460.FStar_Syntax_Syntax.n in
                 match uu____14459 with
                 | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                     let ed =
                       let uu____14478 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14478 in
                     let uu____14479 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____14479 with
                      | (uu____14480, bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____14486 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____14494 =
                                   let uu____14495 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____14495.FStar_Syntax_Syntax.n in
                                 match uu____14494 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1, FStar_Syntax_Syntax.Meta_monadic
                                      (uu____14501, uu____14502))
                                     ->
                                     let uu____14511 =
                                       let uu____14512 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____14512.FStar_Syntax_Syntax.n in
                                     (match uu____14511 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,
                                           FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____14518, msrc, uu____14520))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____14529 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____14529
                                      | uu____14530 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____14531 ->
                                     FStar_Pervasives_Native.None in
                               let uu____14532 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____14532 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___167_14537 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___167_14537.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___167_14537.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___167_14537.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___167_14537.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___167_14537.FStar_Syntax_Syntax.lbpos)
                                      } in
                                    let uu____14538 = FStar_List.tl stack in
                                    let uu____14539 =
                                      let uu____14540 =
                                        let uu____14543 =
                                          let uu____14544 =
                                            let uu____14557 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____14557) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____14544 in
                                        FStar_Syntax_Syntax.mk uu____14543 in
                                      uu____14540
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____14538 uu____14539
                                | FStar_Pervasives_Native.None ->
                                    let uu____14573 =
                                      let uu____14574 = is_return body in
                                      match uu____14574 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____14578;
                                            FStar_Syntax_Syntax.vars =
                                              uu____14579;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____14584 -> false in
                                    if uu____14573
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
                                         let uu____14607 =
                                           let uu____14610 =
                                             let uu____14611 =
                                               let uu____14628 =
                                                 let uu____14631 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____14631] in
                                               (uu____14628, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____14611 in
                                           FStar_Syntax_Syntax.mk uu____14610 in
                                         uu____14607
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____14647 =
                                           let uu____14648 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____14648.FStar_Syntax_Syntax.n in
                                         match uu____14647 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,
                                              uu____14654::uu____14655::[])
                                             ->
                                             let uu____14662 =
                                               let uu____14665 =
                                                 let uu____14666 =
                                                   let uu____14673 =
                                                     let uu____14676 =
                                                       let uu____14677 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____14677 in
                                                     let uu____14678 =
                                                       let uu____14681 =
                                                         let uu____14682 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____14682 in
                                                       [uu____14681] in
                                                     uu____14676 ::
                                                       uu____14678 in
                                                   (bind1, uu____14673) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____14666 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____14665 in
                                             uu____14662
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____14690 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let maybe_range_arg =
                                         let uu____14696 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs in
                                         if uu____14696
                                         then
                                           let uu____14699 =
                                             let uu____14700 =
                                               FStar_Syntax_Embeddings.embed_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14700 in
                                           let uu____14701 =
                                             let uu____14704 =
                                               let uu____14705 =
                                                 FStar_Syntax_Embeddings.embed_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____14705 in
                                             [uu____14704] in
                                           uu____14699 :: uu____14701
                                         else [] in
                                       let reified =
                                         let uu____14710 =
                                           let uu____14713 =
                                             let uu____14714 =
                                               let uu____14729 =
                                                 let uu____14732 =
                                                   let uu____14735 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp in
                                                   let uu____14736 =
                                                     let uu____14739 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t in
                                                     [uu____14739] in
                                                   uu____14735 :: uu____14736 in
                                                 let uu____14740 =
                                                   let uu____14743 =
                                                     let uu____14746 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____14747 =
                                                       let uu____14750 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4 in
                                                       let uu____14751 =
                                                         let uu____14754 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____14755 =
                                                           let uu____14758 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____14758] in
                                                         uu____14754 ::
                                                           uu____14755 in
                                                       uu____14750 ::
                                                         uu____14751 in
                                                     uu____14746 ::
                                                       uu____14747 in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____14743 in
                                                 FStar_List.append
                                                   uu____14732 uu____14740 in
                                               (bind_inst, uu____14729) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____14714 in
                                           FStar_Syntax_Syntax.mk uu____14713 in
                                         uu____14710
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____14770 ->
                                            let uu____14771 =
                                              FStar_Syntax_Print.term_to_string
                                                head0 in
                                            let uu____14772 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____14771 uu____14772);
                                       (let uu____14773 = FStar_List.tl stack in
                                        norm cfg env uu____14773 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app, args) ->
                     let ed =
                       let uu____14797 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14797 in
                     let uu____14798 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____14798 with
                      | (uu____14799, bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____14834 =
                                  let uu____14835 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____14835.FStar_Syntax_Syntax.n in
                                match uu____14834 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2, uu____14841) -> t2
                                | uu____14846 -> head4 in
                              let uu____14847 =
                                let uu____14848 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____14848.FStar_Syntax_Syntax.n in
                              match uu____14847 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____14854 -> FStar_Pervasives_Native.None in
                            let uu____14855 = maybe_extract_fv head4 in
                            match uu____14855 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____14865 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____14865
                                ->
                                let head5 = norm cfg env [] head4 in
                                let action_unfolded =
                                  let uu____14870 = maybe_extract_fv head5 in
                                  match uu____14870 with
                                  | FStar_Pervasives_Native.Some uu____14875
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____14876 ->
                                      FStar_Pervasives_Native.Some false in
                                (head5, action_unfolded)
                            | uu____14881 ->
                                (head4, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____14896 =
                              match uu____14896 with
                              | (e, q) ->
                                  let uu____14903 =
                                    let uu____14904 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____14904.FStar_Syntax_Syntax.n in
                                  (match uu____14903 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,
                                        FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1, m2, t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____14919 -> false) in
                            let uu____14920 =
                              let uu____14921 =
                                let uu____14928 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____14928 :: args in
                              FStar_Util.for_some is_arg_impure uu____14921 in
                            if uu____14920
                            then
                              let uu____14933 =
                                let uu____14934 =
                                  FStar_Syntax_Print.term_to_string head3 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____14934 in
                              failwith uu____14933
                            else ());
                           (let uu____14936 = maybe_unfold_action head_app in
                            match uu____14936 with
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
                                   (fun uu____14977 ->
                                      let uu____14978 =
                                        FStar_Syntax_Print.term_to_string
                                          head0 in
                                      let uu____14979 =
                                        FStar_Syntax_Print.term_to_string
                                          body1 in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____14978 uu____14979);
                                 (let uu____14980 = FStar_List.tl stack in
                                  norm cfg env uu____14980 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e, FStar_Syntax_Syntax.Meta_monadic uu____14982) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e, FStar_Syntax_Syntax.Meta_monadic_lift
                      (msrc, mtgt, t'))
                     ->
                     let lifted =
                       let uu____15006 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15006 in
                     (log cfg
                        (fun uu____15010 ->
                           let uu____15011 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15011);
                      (let uu____15012 = FStar_List.tl stack in
                       norm cfg env uu____15012 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e, branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15133 ->
                               match uu____15133 with
                               | (pat, wopt, tm) ->
                                   let uu____15181 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____15181))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos in
                     let uu____15213 = FStar_List.tl stack in
                     norm cfg env uu____15213 tm
                 | uu____15214 -> fallback ())
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
              (fun uu____15228 ->
                 let uu____15229 = FStar_Ident.string_of_lid msrc in
                 let uu____15230 = FStar_Ident.string_of_lid mtgt in
                 let uu____15231 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15229
                   uu____15230 uu____15231);
            if
              (FStar_Syntax_Util.is_pure_effect msrc) ||
                (FStar_Syntax_Util.is_div_effect msrc)
            then
              (let ed =
                 let uu____15233 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15233 in
               let uu____15234 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____15234 with
               | (uu____15235, return_repr) ->
                   let return_inst =
                     let uu____15244 =
                       let uu____15245 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____15245.FStar_Syntax_Syntax.n in
                     match uu____15244 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm, uu____15251::[]) ->
                         let uu____15258 =
                           let uu____15261 =
                             let uu____15262 =
                               let uu____15269 =
                                 let uu____15272 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____15272] in
                               (return_tm, uu____15269) in
                             FStar_Syntax_Syntax.Tm_uinst uu____15262 in
                           FStar_Syntax_Syntax.mk uu____15261 in
                         uu____15258 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15280 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____15283 =
                     let uu____15286 =
                       let uu____15287 =
                         let uu____15302 =
                           let uu____15305 = FStar_Syntax_Syntax.as_arg t in
                           let uu____15306 =
                             let uu____15309 = FStar_Syntax_Syntax.as_arg e in
                             [uu____15309] in
                           uu____15305 :: uu____15306 in
                         (return_inst, uu____15302) in
                       FStar_Syntax_Syntax.Tm_app uu____15287 in
                     FStar_Syntax_Syntax.mk uu____15286 in
                   uu____15283 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____15318 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15318 with
               | FStar_Pervasives_Native.None ->
                   let uu____15321 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15321
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15322;
                     FStar_TypeChecker_Env.mtarget = uu____15323;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15324;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None;_};_}
                   ->
                   let uu____15339 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15339
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15340;
                     FStar_TypeChecker_Env.mtarget = uu____15341;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15342;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15366 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____15367 = FStar_Syntax_Util.mk_reify e in
                   lift uu____15366 t FStar_Syntax_Syntax.tun uu____15367)
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
                (fun uu____15423 ->
                   match uu____15423 with
                   | (a, imp) ->
                       let uu____15434 = norm cfg env [] a in
                       (uu____15434, imp))))
and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg ->
    fun env ->
      fun comp ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t, uopt) ->
            let uu___168_15448 = comp in
            let uu____15449 =
              let uu____15450 =
                let uu____15459 = norm cfg env [] t in
                let uu____15460 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15459, uu____15460) in
              FStar_Syntax_Syntax.Total uu____15450 in
            {
              FStar_Syntax_Syntax.n = uu____15449;
              FStar_Syntax_Syntax.pos =
                (uu___168_15448.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___168_15448.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
            let uu___169_15475 = comp in
            let uu____15476 =
              let uu____15477 =
                let uu____15486 = norm cfg env [] t in
                let uu____15487 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15486, uu____15487) in
              FStar_Syntax_Syntax.GTotal uu____15477 in
            {
              FStar_Syntax_Syntax.n = uu____15476;
              FStar_Syntax_Syntax.pos =
                (uu___169_15475.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___169_15475.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15539 ->
                      match uu____15539 with
                      | (a, i) ->
                          let uu____15550 = norm cfg env [] a in
                          (uu____15550, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___91_15561 ->
                      match uu___91_15561 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15565 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15565
                      | f -> f)) in
            let uu___170_15569 = comp in
            let uu____15570 =
              let uu____15571 =
                let uu___171_15572 = ct in
                let uu____15573 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15574 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15577 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15573;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___171_15572.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15574;
                  FStar_Syntax_Syntax.effect_args = uu____15577;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____15571 in
            {
              FStar_Syntax_Syntax.n = uu____15570;
              FStar_Syntax_Syntax.pos =
                (uu___170_15569.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___170_15569.FStar_Syntax_Syntax.vars)
            }
and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg ->
    fun env ->
      fun uu____15588 ->
        match uu____15588 with
        | (x, imp) ->
            let uu____15591 =
              let uu___172_15592 = x in
              let uu____15593 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___172_15592.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___172_15592.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15593
              } in
            (uu____15591, imp)
and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg ->
    fun env ->
      fun bs ->
        let uu____15599 =
          FStar_List.fold_left
            (fun uu____15617 ->
               fun b ->
                 match uu____15617 with
                 | (nbs', env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____15599 with | (nbs, uu____15657) -> FStar_List.rev nbs
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
            let uu____15673 =
              let uu___173_15674 = rc in
              let uu____15675 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___173_15674.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15675;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___173_15674.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15673
        | uu____15682 -> lopt
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
            (let uu____15703 = FStar_Syntax_Print.term_to_string tm in
             let uu____15704 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____15703
               uu____15704)
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
          let uu____15724 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify in
          if uu____15724
          then tm1
          else
            (let w t =
               let uu___174_15736 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___174_15736.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___174_15736.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               let uu____15745 =
                 let uu____15746 = FStar_Syntax_Util.unmeta t in
                 uu____15746.FStar_Syntax_Syntax.n in
               match uu____15745 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____15753 -> FStar_Pervasives_Native.None in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t, uu____15798)::args1, (bv, uu____15801)::bs1) ->
                   let uu____15835 =
                     let uu____15836 = FStar_Syntax_Subst.compress t in
                     uu____15836.FStar_Syntax_Syntax.n in
                   (match uu____15835 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____15840 -> false)
               | ([], []) -> true
               | (uu____15861, uu____15862) -> false in
             let is_applied bs t =
               let uu____15898 = FStar_Syntax_Util.head_and_args' t in
               match uu____15898 with
               | (hd1, args) ->
                   let uu____15931 =
                     let uu____15932 = FStar_Syntax_Subst.compress hd1 in
                     uu____15932.FStar_Syntax_Syntax.n in
                   (match uu____15931 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____15938 -> FStar_Pervasives_Native.None) in
             let is_applied_maybe_squashed bs t =
               let uu____15950 = FStar_Syntax_Util.is_squash t in
               match uu____15950 with
               | FStar_Pervasives_Native.Some (uu____15961, t') ->
                   is_applied bs t'
               | uu____15973 ->
                   let uu____15982 = FStar_Syntax_Util.is_auto_squash t in
                   (match uu____15982 with
                    | FStar_Pervasives_Native.Some (uu____15993, t') ->
                        is_applied bs t'
                    | uu____16005 -> is_applied bs t) in
             let is_quantified_const phi =
               let uu____16022 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu____16022 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid, (p, uu____16029)::(q, uu____16031)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____16066 =
                     FStar_Syntax_Util.destruct_typ_as_formula p in
                   (match uu____16066 with
                    | FStar_Pervasives_Native.None ->
                        let uu____16071 =
                          let uu____16072 = FStar_Syntax_Subst.compress p in
                          uu____16072.FStar_Syntax_Syntax.n in
                        (match uu____16071 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16078 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q in
                             FStar_Pervasives_Native.Some uu____16078
                         | uu____16079 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1, (p1, uu____16082)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____16107 =
                          let uu____16108 = FStar_Syntax_Subst.compress p1 in
                          uu____16108.FStar_Syntax_Syntax.n in
                        (match uu____16107 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16114 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q in
                             FStar_Pervasives_Native.Some uu____16114
                         | uu____16115 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs, pats, phi1)) ->
                        let uu____16119 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1 in
                        (match uu____16119 with
                         | FStar_Pervasives_Native.None ->
                             let uu____16124 =
                               is_applied_maybe_squashed bs phi1 in
                             (match uu____16124 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.kprop)) in
                                  let uu____16131 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q in
                                  FStar_Pervasives_Native.Some uu____16131
                              | FStar_Pervasives_Native.None ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1, (p1, uu____16134)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____16159 =
                               is_applied_maybe_squashed bs p1 in
                             (match uu____16159 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.kprop)) in
                                  let uu____16166 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q in
                                  FStar_Pervasives_Native.Some uu____16166
                              | uu____16167 -> FStar_Pervasives_Native.None)
                         | uu____16170 -> FStar_Pervasives_Native.None)
                    | uu____16173 -> FStar_Pervasives_Native.None)
               | uu____16176 -> FStar_Pervasives_Native.None in
             let is_const_match phi =
               let uu____16187 =
                 let uu____16188 = FStar_Syntax_Subst.compress phi in
                 uu____16188.FStar_Syntax_Syntax.n in
               match uu____16187 with
               | FStar_Syntax_Syntax.Tm_match (uu____16193, br::brs) ->
                   let uu____16260 = br in
                   (match uu____16260 with
                    | (uu____16277, uu____16278, e) ->
                        let r =
                          let uu____16299 = simp_t e in
                          match uu____16299 with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____16305 =
                                FStar_List.for_all
                                  (fun uu____16323 ->
                                     match uu____16323 with
                                     | (uu____16336, uu____16337, e') ->
                                         let uu____16351 = simp_t e' in
                                         uu____16351 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs in
                              if uu____16305
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None in
                        r)
               | uu____16359 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____16364 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____16364
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____16385 =
                 match uu____16385 with
                 | (t1, q) ->
                     let uu____16398 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____16398 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
                      | uu____16426 -> (t1, q)) in
               let uu____16435 = FStar_Syntax_Util.head_and_args t in
               match uu____16435 with
               | (head1, args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
             let rec clearly_inhabited ty =
               let uu____16497 =
                 let uu____16498 = FStar_Syntax_Util.unmeta ty in
                 uu____16498.FStar_Syntax_Syntax.n in
               match uu____16497 with
               | FStar_Syntax_Syntax.Tm_uinst (t, uu____16502) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____16507, c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____16527 -> false in
             let simplify1 arg =
               let uu____16550 = simp_t (FStar_Pervasives_Native.fst arg) in
               (uu____16550, arg) in
             let uu____16559 = is_quantified_const tm1 in
             match uu____16559 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____16563 = norm cfg env [] tm2 in
                 maybe_simplify_aux cfg env stack uu____16563
             | FStar_Pervasives_Native.None ->
                 let uu____16564 =
                   let uu____16565 = FStar_Syntax_Subst.compress tm1 in
                   uu____16565.FStar_Syntax_Syntax.n in
                 (match uu____16564 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____16569;
                              FStar_Syntax_Syntax.vars = uu____16570;_},
                            uu____16571);
                         FStar_Syntax_Syntax.pos = uu____16572;
                         FStar_Syntax_Syntax.vars = uu____16573;_},
                       args)
                      ->
                      let uu____16599 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____16599
                      then
                        let uu____16600 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        (match uu____16600 with
                         | (FStar_Pervasives_Native.Some (true), uu____16647)::
                             (uu____16648, (arg, uu____16650))::[] ->
                             maybe_auto_squash arg
                         | (uu____16699, (arg, uu____16701))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____16702)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____16751)::uu____16752::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16803::(FStar_Pervasives_Native.Some
                                         (false), uu____16804)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16855 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16869 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____16869
                         then
                           let uu____16870 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1) in
                           match uu____16870 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____16917)::uu____16918::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16969::(FStar_Pervasives_Native.Some
                                           (true), uu____16970)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____17021)::(uu____17022, (arg, uu____17024))::[]
                               -> maybe_auto_squash arg
                           | (uu____17073, (arg, uu____17075))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____17076)::[]
                               -> maybe_auto_squash arg
                           | uu____17125 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17139 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____17139
                            then
                              let uu____17140 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1) in
                              match uu____17140 with
                              | uu____17187::(FStar_Pervasives_Native.Some
                                              (true), uu____17188)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____17239)::uu____17240::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____17291)::(uu____17292,
                                                (arg, uu____17294))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17343, (p, uu____17345))::(uu____17346,
                                                                  (q,
                                                                   uu____17348))::[]
                                  ->
                                  let uu____17395 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____17395
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____17397 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____17411 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____17411
                               then
                                 let uu____17412 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1) in
                                 match uu____17412 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____17459)::(FStar_Pervasives_Native.Some
                                                   (true), uu____17460)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____17511)::(FStar_Pervasives_Native.Some
                                                   (false), uu____17512)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____17563)::(FStar_Pervasives_Native.Some
                                                   (false), uu____17564)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____17615)::(FStar_Pervasives_Native.Some
                                                   (true), uu____17616)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17667, (arg, uu____17669))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____17670)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____17719)::(uu____17720,
                                                   (arg, uu____17722))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17771, (arg, uu____17773))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____17774)::[]
                                     ->
                                     let uu____17823 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____17823
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____17824)::(uu____17825,
                                                   (arg, uu____17827))::[]
                                     ->
                                     let uu____17876 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____17876
                                 | (uu____17877, (p, uu____17879))::(uu____17880,
                                                                    (q,
                                                                    uu____17882))::[]
                                     ->
                                     let uu____17929 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____17929
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17931 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17945 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____17945
                                  then
                                    let uu____17946 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1) in
                                    match uu____17946 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____17993)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____18024)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____18055 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____18069 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____18069
                                     then
                                       match args with
                                       | (t, uu____18071)::[] ->
                                           let uu____18088 =
                                             let uu____18089 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____18089.FStar_Syntax_Syntax.n in
                                           (match uu____18088 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18092::[], body,
                                                 uu____18094)
                                                ->
                                                let uu____18121 = simp_t body in
                                                (match uu____18121 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____18124 -> tm1)
                                            | uu____18127 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____18129))::(t, uu____18131)::[]
                                           ->
                                           let uu____18170 =
                                             let uu____18171 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____18171.FStar_Syntax_Syntax.n in
                                           (match uu____18170 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18174::[], body,
                                                 uu____18176)
                                                ->
                                                let uu____18203 = simp_t body in
                                                (match uu____18203 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____18206 -> tm1)
                                            | uu____18209 -> tm1)
                                       | uu____18210 -> tm1
                                     else
                                       (let uu____18220 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____18220
                                        then
                                          match args with
                                          | (t, uu____18222)::[] ->
                                              let uu____18239 =
                                                let uu____18240 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____18240.FStar_Syntax_Syntax.n in
                                              (match uu____18239 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18243::[], body,
                                                    uu____18245)
                                                   ->
                                                   let uu____18272 =
                                                     simp_t body in
                                                   (match uu____18272 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____18275 -> tm1)
                                               | uu____18278 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18280))::(t, uu____18282)::[]
                                              ->
                                              let uu____18321 =
                                                let uu____18322 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____18322.FStar_Syntax_Syntax.n in
                                              (match uu____18321 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18325::[], body,
                                                    uu____18327)
                                                   ->
                                                   let uu____18354 =
                                                     simp_t body in
                                                   (match uu____18354 with
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
                                                    | uu____18357 -> tm1)
                                               | uu____18360 -> tm1)
                                          | uu____18361 -> tm1
                                        else
                                          (let uu____18371 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2p_lid in
                                           if uu____18371
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18372;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18373;_},
                                                uu____18374)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18391;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18392;_},
                                                uu____18393)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18410 -> tm1
                                           else
                                             (let uu____18420 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1 in
                                              match uu____18420 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero,
                                                   t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18440 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18450;
                         FStar_Syntax_Syntax.vars = uu____18451;_},
                       args)
                      ->
                      let uu____18473 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____18473
                      then
                        let uu____18474 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        (match uu____18474 with
                         | (FStar_Pervasives_Native.Some (true), uu____18521)::
                             (uu____18522, (arg, uu____18524))::[] ->
                             maybe_auto_squash arg
                         | (uu____18573, (arg, uu____18575))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____18576)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____18625)::uu____18626::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18677::(FStar_Pervasives_Native.Some
                                         (false), uu____18678)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18729 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18743 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____18743
                         then
                           let uu____18744 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1) in
                           match uu____18744 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____18791)::uu____18792::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18843::(FStar_Pervasives_Native.Some
                                           (true), uu____18844)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____18895)::(uu____18896, (arg, uu____18898))::[]
                               -> maybe_auto_squash arg
                           | (uu____18947, (arg, uu____18949))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____18950)::[]
                               -> maybe_auto_squash arg
                           | uu____18999 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19013 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____19013
                            then
                              let uu____19014 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1) in
                              match uu____19014 with
                              | uu____19061::(FStar_Pervasives_Native.Some
                                              (true), uu____19062)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____19113)::uu____19114::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____19165)::(uu____19166,
                                                (arg, uu____19168))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19217, (p, uu____19219))::(uu____19220,
                                                                  (q,
                                                                   uu____19222))::[]
                                  ->
                                  let uu____19269 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____19269
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19271 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19285 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____19285
                               then
                                 let uu____19286 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1) in
                                 match uu____19286 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____19333)::(FStar_Pervasives_Native.Some
                                                   (true), uu____19334)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____19385)::(FStar_Pervasives_Native.Some
                                                   (false), uu____19386)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____19437)::(FStar_Pervasives_Native.Some
                                                   (false), uu____19438)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____19489)::(FStar_Pervasives_Native.Some
                                                   (true), uu____19490)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19541, (arg, uu____19543))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____19544)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____19593)::(uu____19594,
                                                   (arg, uu____19596))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19645, (arg, uu____19647))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____19648)::[]
                                     ->
                                     let uu____19697 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____19697
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____19698)::(uu____19699,
                                                   (arg, uu____19701))::[]
                                     ->
                                     let uu____19750 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____19750
                                 | (uu____19751, (p, uu____19753))::(uu____19754,
                                                                    (q,
                                                                    uu____19756))::[]
                                     ->
                                     let uu____19803 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____19803
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19805 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19819 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____19819
                                  then
                                    let uu____19820 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1) in
                                    match uu____19820 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____19867)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____19898)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19929 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19943 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____19943
                                     then
                                       match args with
                                       | (t, uu____19945)::[] ->
                                           let uu____19962 =
                                             let uu____19963 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____19963.FStar_Syntax_Syntax.n in
                                           (match uu____19962 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19966::[], body,
                                                 uu____19968)
                                                ->
                                                let uu____19995 = simp_t body in
                                                (match uu____19995 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19998 -> tm1)
                                            | uu____20001 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20003))::(t, uu____20005)::[]
                                           ->
                                           let uu____20044 =
                                             let uu____20045 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____20045.FStar_Syntax_Syntax.n in
                                           (match uu____20044 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20048::[], body,
                                                 uu____20050)
                                                ->
                                                let uu____20077 = simp_t body in
                                                (match uu____20077 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20080 -> tm1)
                                            | uu____20083 -> tm1)
                                       | uu____20084 -> tm1
                                     else
                                       (let uu____20094 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____20094
                                        then
                                          match args with
                                          | (t, uu____20096)::[] ->
                                              let uu____20113 =
                                                let uu____20114 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____20114.FStar_Syntax_Syntax.n in
                                              (match uu____20113 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20117::[], body,
                                                    uu____20119)
                                                   ->
                                                   let uu____20146 =
                                                     simp_t body in
                                                   (match uu____20146 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20149 -> tm1)
                                               | uu____20152 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20154))::(t, uu____20156)::[]
                                              ->
                                              let uu____20195 =
                                                let uu____20196 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____20196.FStar_Syntax_Syntax.n in
                                              (match uu____20195 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20199::[], body,
                                                    uu____20201)
                                                   ->
                                                   let uu____20228 =
                                                     simp_t body in
                                                   (match uu____20228 with
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
                                                    | uu____20231 -> tm1)
                                               | uu____20234 -> tm1)
                                          | uu____20235 -> tm1
                                        else
                                          (let uu____20245 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2p_lid in
                                           if uu____20245
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20246;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20247;_},
                                                uu____20248)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20265;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20266;_},
                                                uu____20267)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20284 -> tm1
                                           else
                                             (let uu____20294 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1 in
                                              match uu____20294 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero,
                                                   t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20314 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
                      let uu____20329 = simp_t t in
                      (match uu____20329 with
                       | FStar_Pervasives_Native.Some (true) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false) -> tm1
                       | FStar_Pervasives_Native.None -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20332 ->
                      let uu____20355 = is_const_match tm1 in
                      (match uu____20355 with
                       | FStar_Pervasives_Native.Some (true) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None -> tm1)
                  | uu____20358 -> tm1))
and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env ->
      fun stack ->
        fun t ->
          log cfg
            (fun uu____20369 ->
               let uu____20370 = FStar_Syntax_Print.tag_of_term t in
               let uu____20371 = FStar_Syntax_Print.term_to_string t in
               let uu____20372 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____20379 =
                 let uu____20380 =
                   let uu____20383 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____20383 in
                 stack_to_string uu____20380 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____20370 uu____20371 uu____20372 uu____20379);
          (let t1 = maybe_simplify cfg env stack t in
           match stack with
           | [] -> t1
           | (Debug (tm, time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now () in
                   let uu____20414 =
                     let uu____20415 =
                       let uu____20416 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____20416 in
                     FStar_Util.string_of_int uu____20415 in
                   let uu____20421 = FStar_Syntax_Print.term_to_string tm in
                   let uu____20422 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20414 uu____20421 uu____20422)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m, r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____20524 ->
                     let uu____20525 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20525);
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
               let uu____20561 =
                 let uu___175_20562 = FStar_Syntax_Util.abs bs1 t1 lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___175_20562.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___175_20562.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____20561
           | (Arg (Univ uu____20563, uu____20564, uu____20565))::uu____20566
               -> failwith "Impossible"
           | (Arg (Dummy, uu____20569, uu____20570))::uu____20571 ->
               failwith "Impossible"
           | (UnivArgs (us, r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us in
               rebuild cfg env stack1 t2
           | (Arg
               (Clos (env_arg, tm, uu____20586, uu____20587), aq, r))::stack1
               when
               let uu____20637 = head_of t1 in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20637 ->
               let t2 =
                 let uu____20641 =
                   let uu____20642 =
                     let uu____20643 = closure_as_term cfg env_arg tm in
                     (uu____20643, aq) in
                   FStar_Syntax_Syntax.extend_app t1 uu____20642 in
                 uu____20641 FStar_Pervasives_Native.None r in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg, tm, m, uu____20649), aq, r))::stack1 ->
               (log cfg
                  (fun uu____20702 ->
                     let uu____20703 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20703);
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
                  (let uu____20713 = FStar_ST.op_Bang m in
                   match uu____20713 with
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
                   | FStar_Pervasives_Native.Some (uu____20976, a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1, head1, aq, r))::stack' when should_reify cfg stack
               ->
               let t0 = t1 in
               let fallback msg uu____21023 =
                 log cfg
                   (fun uu____21027 ->
                      let uu____21028 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21028);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t2) in
               let uu____21032 =
                 let uu____21033 = FStar_Syntax_Subst.compress t1 in
                 uu____21033.FStar_Syntax_Syntax.n in
               (match uu____21032 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2, FStar_Syntax_Syntax.Meta_monadic_lift
                     (msrc, mtgt, ty))
                    ->
                    let lifted =
                      let uu____21060 = closure_as_term cfg env1 ty in
                      reify_lift cfg t2 msrc mtgt uu____21060 in
                    (log cfg
                       (fun uu____21064 ->
                          let uu____21065 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21065);
                     (let uu____21066 = FStar_List.tl stack in
                      norm cfg env1 uu____21066 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21067);
                       FStar_Syntax_Syntax.pos = uu____21068;
                       FStar_Syntax_Syntax.vars = uu____21069;_},
                     (e, uu____21071)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21100 when
                    (cfg.steps).primops ->
                    let uu____21115 = FStar_Syntax_Util.head_and_args t1 in
                    (match uu____21115 with
                     | (hd1, args) ->
                         let uu____21152 =
                           let uu____21153 = FStar_Syntax_Util.un_uinst hd1 in
                           uu____21153.FStar_Syntax_Syntax.n in
                         (match uu____21152 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21157 = find_prim_step cfg fv in
                              (match uu____21157 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____21160; arity = uu____21161;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____21163;
                                     requires_binder_substitution =
                                       uu____21164;
                                     interpretation = uu____21165;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21178 -> fallback " (3)" ())
                          | uu____21181 -> fallback " (4)" ()))
                | uu____21182 -> fallback " (2)" ())
           | (App (env1, head1, aq, r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r in
               rebuild cfg env1 stack1 t2
           | (Match (env1, branches, r))::stack1 ->
               (log cfg
                  (fun uu____21202 ->
                     let uu____21203 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21203);
                (let scrutinee = t1 in
                 let norm_and_rebuild_match uu____21208 =
                   log cfg
                     (fun uu____21213 ->
                        let uu____21214 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____21215 =
                          let uu____21216 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21233 ->
                                    match uu____21233 with
                                    | (p, uu____21243, uu____21244) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____21216
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21214 uu____21215);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___92_21261 ->
                                match uu___92_21261 with
                                | FStar_TypeChecker_Env.Inlining -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only
                                    -> true
                                | uu____21262 -> false)) in
                      let uu___176_21263 = cfg in
                      {
                        steps =
                          (let uu___177_21266 = cfg.steps in
                           {
                             beta = (uu___177_21266.beta);
                             iota = (uu___177_21266.iota);
                             zeta = false;
                             weak = (uu___177_21266.weak);
                             hnf = (uu___177_21266.hnf);
                             primops = (uu___177_21266.primops);
                             no_delta_steps = (uu___177_21266.no_delta_steps);
                             unfold_until = (uu___177_21266.unfold_until);
                             unfold_only = (uu___177_21266.unfold_only);
                             unfold_attr = (uu___177_21266.unfold_attr);
                             unfold_tac = (uu___177_21266.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___177_21266.pure_subterms_within_computations);
                             simplify = (uu___177_21266.simplify);
                             erase_universes =
                               (uu___177_21266.erase_universes);
                             allow_unbound_universes =
                               (uu___177_21266.allow_unbound_universes);
                             reify_ = (uu___177_21266.reify_);
                             compress_uvars = (uu___177_21266.compress_uvars);
                             no_full_norm = (uu___177_21266.no_full_norm);
                             check_no_uvars = (uu___177_21266.check_no_uvars);
                             unmeta = (uu___177_21266.unmeta);
                             unascribe = (uu___177_21266.unascribe)
                           });
                        tcenv = (uu___176_21263.tcenv);
                        debug = (uu___176_21263.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___176_21263.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___176_21263.memoize_lazy);
                        normalize_pure_lets =
                          (uu___176_21263.normalize_pure_lets)
                      } in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21298 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                          let uu____21319 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21379 ->
                                    fun uu____21380 ->
                                      match (uu____21379, uu____21380) with
                                      | ((pats1, env3), (p1, b)) ->
                                          let uu____21471 = norm_pat env3 p1 in
                                          (match uu____21471 with
                                           | (p2, env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____21319 with
                           | (pats1, env3) ->
                               ((let uu___178_21553 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___178_21553.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___179_21572 = x in
                            let uu____21573 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___179_21572.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___179_21572.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21573
                            } in
                          ((let uu___180_21587 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___180_21587.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___181_21598 = x in
                            let uu____21599 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_21598.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_21598.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21599
                            } in
                          ((let uu___182_21613 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___182_21613.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x, t2) ->
                          let x1 =
                            let uu___183_21629 = x in
                            let uu____21630 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___183_21629.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___183_21629.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21630
                            } in
                          let t3 = norm_or_whnf env2 t2 in
                          ((let uu___184_21637 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___184_21637.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____21647 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1 ->
                                  let uu____21661 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____21661 with
                                  | (p, wopt, e) ->
                                      let uu____21681 = norm_pat env1 p in
                                      (match uu____21681 with
                                       | (p1, env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____21706 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____21706 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____21712 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____21712) in
                 let rec is_cons head1 =
                   let uu____21717 =
                     let uu____21718 = FStar_Syntax_Subst.compress head1 in
                     uu____21718.FStar_Syntax_Syntax.n in
                   match uu____21717 with
                   | FStar_Syntax_Syntax.Tm_uinst (h, uu____21722) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____21727 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21728;
                         FStar_Syntax_Syntax.fv_delta = uu____21729;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor);_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21730;
                         FStar_Syntax_Syntax.fv_delta = uu____21731;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____21732);_}
                       -> true
                   | uu____21739 -> false in
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
                   let uu____21884 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____21884 with
                   | (head1, args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____21971 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22010 ->
                                 let uu____22011 =
                                   let uu____22012 = is_cons head1 in
                                   Prims.op_Negation uu____22012 in
                                 FStar_Util.Inr uu____22011)
                        | FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) ->
                            let uu____22037 =
                              let uu____22038 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____22038.FStar_Syntax_Syntax.n in
                            (match uu____22037 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22056 ->
                                 let uu____22057 =
                                   let uu____22058 = is_cons head1 in
                                   Prims.op_Negation uu____22058 in
                                 FStar_Util.Inr uu____22057))
                 and matches_args out a p =
                   match (a, p) with
                   | ([], []) -> FStar_Util.Inl out
                   | ((t2, uu____22127)::rest_a, (p1, uu____22130)::rest_p)
                       ->
                       let uu____22174 = matches_pat t2 p1 in
                       (match uu____22174 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22223 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1, wopt, b)::rest ->
                       let uu____22329 = matches_pat scrutinee1 p1 in
                       (match uu____22329 with
                        | FStar_Util.Inr (false) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____22369 ->
                                  let uu____22370 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____22371 =
                                    let uu____22372 =
                                      FStar_List.map
                                        (fun uu____22382 ->
                                           match uu____22382 with
                                           | (uu____22387, t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s in
                                    FStar_All.pipe_right uu____22372
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22370 uu____22371);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____22418 ->
                                       match uu____22418 with
                                       | (bv, t2) ->
                                           let uu____22441 =
                                             let uu____22448 =
                                               let uu____22451 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____22451 in
                                             let uu____22452 =
                                               let uu____22453 =
                                                 let uu____22484 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2)) in
                                                 ([], t2, uu____22484, false) in
                                               Clos uu____22453 in
                                             (uu____22448, uu____22452) in
                                           uu____22441 :: env2) env1 s in
                              let uu____22649 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____22649))) in
                 if (cfg.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))
let (plugins :
  (primitive_step -> Prims.unit, Prims.unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref [] in
  let register p =
    let uu____22672 =
      let uu____22675 = FStar_ST.op_Bang plugins in p :: uu____22675 in
    FStar_ST.op_Colon_Equals plugins uu____22672 in
  let retrieve uu____22881 = FStar_ST.op_Bang plugins in (register, retrieve)
let (register_plugin : primitive_step -> Prims.unit) =
  fun p -> FStar_Pervasives_Native.fst plugins p
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____23000 -> FStar_Pervasives_Native.snd plugins ()
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
               (fun uu___93_23033 ->
                  match uu___93_23033 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____23037 -> [])) in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____23043 -> d in
        let uu____23046 = to_fsteps s in
        let uu____23047 =
          let uu____23048 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm") in
          let uu____23049 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops") in
          let uu____23050 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380") in
          let uu____23051 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed") in
          let uu____23052 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms") in
          {
            gen = uu____23048;
            primop = uu____23049;
            b380 = uu____23050;
            norm_delayed = uu____23051;
            print_normalized = uu____23052
          } in
        let uu____23053 =
          let uu____23056 =
            let uu____23059 = retrieve_plugins () in
            FStar_List.append uu____23059 psteps in
          add_steps built_in_primitive_steps uu____23056 in
        let uu____23062 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____23064 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations) in
             Prims.op_Negation uu____23064) in
        {
          steps = uu____23046;
          tcenv = e;
          debug = uu____23047;
          delta_level = d1;
          primitive_steps = uu____23053;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____23062
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
      fun t -> let uu____23122 = config s e in norm_comp uu____23122 [] t
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun u ->
      let uu____23135 = config [] env in norm_universe uu____23135 [] u
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
        let uu____23153 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____23153 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____23160 -> c
      | FStar_Syntax_Syntax.GTotal (t, uopt) when non_info t ->
          let uu___185_23179 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___185_23179.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___185_23179.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____23186 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____23186
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
                  let uu___186_23195 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___186_23195.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___186_23195.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___186_23195.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___187_23197 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___187_23197.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___187_23197.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___187_23197.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___187_23197.FStar_Syntax_Syntax.flags)
                  } in
            let uu___188_23198 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___188_23198.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___188_23198.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23200 -> c
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
        let uu____23212 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____23212 in
      let uu____23219 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____23219
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23223 ->
                 let uu____23224 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____23224)
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
            ((let uu____23241 =
                let uu____23246 =
                  let uu____23247 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23247 in
                (FStar_Errors.Warning_NormalizationFailure, uu____23246) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23241);
             t) in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      let c1 =
        try
          let uu____23258 = config [AllowUnboundUniverses] env in
          norm_comp uu____23258 [] c
        with
        | e ->
            ((let uu____23271 =
                let uu____23276 =
                  let uu____23277 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23277 in
                (FStar_Errors.Warning_NormalizationFailure, uu____23276) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23271);
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
                   let uu____23314 =
                     let uu____23315 =
                       let uu____23322 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____23322) in
                     FStar_Syntax_Syntax.Tm_refine uu____23315 in
                   mk uu____23314 t01.FStar_Syntax_Syntax.pos
               | uu____23327 -> t2)
          | uu____23328 -> t2 in
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
        let uu____23368 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____23368 with
        | (formals, c) ->
            (match formals with
             | [] -> e
             | uu____23397 ->
                 let uu____23404 = FStar_Syntax_Util.abs_formals e in
                 (match uu____23404 with
                  | (actuals, uu____23414, uu____23415) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23429 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____23429 with
                         | (binders, args) ->
                             let uu____23446 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____23446
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
      | uu____23454 ->
          let uu____23455 = FStar_Syntax_Util.head_and_args t in
          (match uu____23455 with
           | (head1, args) ->
               let uu____23492 =
                 let uu____23493 = FStar_Syntax_Subst.compress head1 in
                 uu____23493.FStar_Syntax_Syntax.n in
               (match uu____23492 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____23496, thead) ->
                    let uu____23522 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____23522 with
                     | (formals, tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23564 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___193_23572 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___193_23572.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___193_23572.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___193_23572.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___193_23572.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___193_23572.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___193_23572.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___193_23572.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___193_23572.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___193_23572.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___193_23572.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___193_23572.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___193_23572.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___193_23572.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___193_23572.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___193_23572.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___193_23572.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___193_23572.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___193_23572.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___193_23572.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___193_23572.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___193_23572.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___193_23572.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___193_23572.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___193_23572.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___193_23572.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___193_23572.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___193_23572.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___193_23572.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___193_23572.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___193_23572.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___193_23572.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___193_23572.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___193_23572.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____23564 with
                            | (uu____23573, ty, uu____23575) ->
                                eta_expand_with_type env t ty))
                | uu____23576 ->
                    let uu____23577 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___194_23585 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___194_23585.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___194_23585.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___194_23585.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___194_23585.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___194_23585.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___194_23585.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___194_23585.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___194_23585.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___194_23585.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___194_23585.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___194_23585.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___194_23585.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___194_23585.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___194_23585.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___194_23585.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___194_23585.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___194_23585.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___194_23585.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___194_23585.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___194_23585.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___194_23585.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___194_23585.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___194_23585.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___194_23585.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___194_23585.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___194_23585.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___194_23585.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___194_23585.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___194_23585.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___194_23585.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___194_23585.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___194_23585.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___194_23585.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____23577 with
                     | (uu____23586, ty, uu____23588) ->
                         eta_expand_with_type env t ty)))
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos in
    let t1 = FStar_Syntax_Subst.compress t in
    let elim_bv x =
      let uu___195_23645 = x in
      let uu____23646 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___195_23645.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___195_23645.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23646
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23649 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23674 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23675 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23676 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23677 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23684 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23685 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23686 -> t1
    | FStar_Syntax_Syntax.Tm_unknown -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) ->
        let elim_rc rc =
          let uu___196_23714 = rc in
          let uu____23715 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term in
          let uu____23722 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___196_23714.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23715;
            FStar_Syntax_Syntax.residual_flags = uu____23722
          } in
        let uu____23725 =
          let uu____23726 =
            let uu____23743 = elim_delayed_subst_binders bs in
            let uu____23750 = elim_delayed_subst_term t2 in
            let uu____23751 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____23743, uu____23750, uu____23751) in
          FStar_Syntax_Syntax.Tm_abs uu____23726 in
        mk1 uu____23725
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu____23780 =
          let uu____23781 =
            let uu____23794 = elim_delayed_subst_binders bs in
            let uu____23801 = elim_delayed_subst_comp c in
            (uu____23794, uu____23801) in
          FStar_Syntax_Syntax.Tm_arrow uu____23781 in
        mk1 uu____23780
    | FStar_Syntax_Syntax.Tm_refine (bv, phi) ->
        let uu____23814 =
          let uu____23815 =
            let uu____23822 = elim_bv bv in
            let uu____23823 = elim_delayed_subst_term phi in
            (uu____23822, uu____23823) in
          FStar_Syntax_Syntax.Tm_refine uu____23815 in
        mk1 uu____23814
    | FStar_Syntax_Syntax.Tm_app (t2, args) ->
        let uu____23846 =
          let uu____23847 =
            let uu____23862 = elim_delayed_subst_term t2 in
            let uu____23863 = elim_delayed_subst_args args in
            (uu____23862, uu____23863) in
          FStar_Syntax_Syntax.Tm_app uu____23847 in
        mk1 uu____23846
    | FStar_Syntax_Syntax.Tm_match (t2, branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___197_23927 = p in
              let uu____23928 =
                let uu____23929 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____23929 in
              {
                FStar_Syntax_Syntax.v = uu____23928;
                FStar_Syntax_Syntax.p =
                  (uu___197_23927.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___198_23931 = p in
              let uu____23932 =
                let uu____23933 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____23933 in
              {
                FStar_Syntax_Syntax.v = uu____23932;
                FStar_Syntax_Syntax.p =
                  (uu___198_23931.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
              let uu___199_23940 = p in
              let uu____23941 =
                let uu____23942 =
                  let uu____23949 = elim_bv x in
                  let uu____23950 = elim_delayed_subst_term t0 in
                  (uu____23949, uu____23950) in
                FStar_Syntax_Syntax.Pat_dot_term uu____23942 in
              {
                FStar_Syntax_Syntax.v = uu____23941;
                FStar_Syntax_Syntax.p =
                  (uu___199_23940.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
              let uu___200_23969 = p in
              let uu____23970 =
                let uu____23971 =
                  let uu____23984 =
                    FStar_List.map
                      (fun uu____24007 ->
                         match uu____24007 with
                         | (x, b) ->
                             let uu____24020 = elim_pat x in (uu____24020, b))
                      pats in
                  (fv, uu____23984) in
                FStar_Syntax_Syntax.Pat_cons uu____23971 in
              {
                FStar_Syntax_Syntax.v = uu____23970;
                FStar_Syntax_Syntax.p =
                  (uu___200_23969.FStar_Syntax_Syntax.p)
              }
          | uu____24033 -> p in
        let elim_branch uu____24055 =
          match uu____24055 with
          | (pat, wopt, t3) ->
              let uu____24081 = elim_pat pat in
              let uu____24084 =
                FStar_Util.map_opt wopt elim_delayed_subst_term in
              let uu____24087 = elim_delayed_subst_term t3 in
              (uu____24081, uu____24084, uu____24087) in
        let uu____24092 =
          let uu____24093 =
            let uu____24116 = elim_delayed_subst_term t2 in
            let uu____24117 = FStar_List.map elim_branch branches in
            (uu____24116, uu____24117) in
          FStar_Syntax_Syntax.Tm_match uu____24093 in
        mk1 uu____24092
    | FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) ->
        let elim_ascription uu____24226 =
          match uu____24226 with
          | (tc, topt) ->
              let uu____24261 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24271 = elim_delayed_subst_term t3 in
                    FStar_Util.Inl uu____24271
                | FStar_Util.Inr c ->
                    let uu____24273 = elim_delayed_subst_comp c in
                    FStar_Util.Inr uu____24273 in
              let uu____24274 =
                FStar_Util.map_opt topt elim_delayed_subst_term in
              (uu____24261, uu____24274) in
        let uu____24283 =
          let uu____24284 =
            let uu____24311 = elim_delayed_subst_term t2 in
            let uu____24312 = elim_ascription a in
            (uu____24311, uu____24312, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____24284 in
        mk1 uu____24283
    | FStar_Syntax_Syntax.Tm_let (lbs, t2) ->
        let elim_lb lb =
          let uu___201_24357 = lb in
          let uu____24358 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp in
          let uu____24361 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___201_24357.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___201_24357.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24358;
            FStar_Syntax_Syntax.lbeff =
              (uu___201_24357.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24361;
            FStar_Syntax_Syntax.lbattrs =
              (uu___201_24357.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___201_24357.FStar_Syntax_Syntax.lbpos)
          } in
        let uu____24364 =
          let uu____24365 =
            let uu____24378 =
              let uu____24385 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____24385) in
            let uu____24394 = elim_delayed_subst_term t2 in
            (uu____24378, uu____24394) in
          FStar_Syntax_Syntax.Tm_let uu____24365 in
        mk1 uu____24364
    | FStar_Syntax_Syntax.Tm_uvar (uv, t2) ->
        let uu____24427 =
          let uu____24428 =
            let uu____24445 = elim_delayed_subst_term t2 in (uv, uu____24445) in
          FStar_Syntax_Syntax.Tm_uvar uu____24428 in
        mk1 uu____24427
    | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi in
        let uu____24463 =
          let uu____24464 =
            let uu____24471 = elim_delayed_subst_term tm in
            (uu____24471, qi1) in
          FStar_Syntax_Syntax.Tm_quoted uu____24464 in
        mk1 uu____24463
    | FStar_Syntax_Syntax.Tm_meta (t2, md) ->
        let uu____24478 =
          let uu____24479 =
            let uu____24486 = elim_delayed_subst_term t2 in
            let uu____24487 = elim_delayed_subst_meta md in
            (uu____24486, uu____24487) in
          FStar_Syntax_Syntax.Tm_meta uu____24479 in
        mk1 uu____24478
and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1 ->
    FStar_List.map
      (fun uu___94_24494 ->
         match uu___94_24494 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24498 = elim_delayed_subst_term t in
             FStar_Syntax_Syntax.DECREASES uu____24498
         | f -> f) flags1
and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uopt) ->
        let uu____24519 =
          let uu____24520 =
            let uu____24529 = elim_delayed_subst_term t in
            (uu____24529, uopt) in
          FStar_Syntax_Syntax.Total uu____24520 in
        mk1 uu____24519
    | FStar_Syntax_Syntax.GTotal (t, uopt) ->
        let uu____24542 =
          let uu____24543 =
            let uu____24552 = elim_delayed_subst_term t in
            (uu____24552, uopt) in
          FStar_Syntax_Syntax.GTotal uu____24543 in
        mk1 uu____24542
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___202_24557 = ct in
          let uu____24558 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ in
          let uu____24561 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____24570 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___202_24557.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___202_24557.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24558;
            FStar_Syntax_Syntax.effect_args = uu____24561;
            FStar_Syntax_Syntax.flags = uu____24570
          } in
        mk1 (FStar_Syntax_Syntax.Comp ct1)
and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___95_24573 ->
    match uu___95_24573 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24585 = FStar_List.map elim_delayed_subst_args args in
        FStar_Syntax_Syntax.Meta_pattern uu____24585
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____24618 =
          let uu____24625 = elim_delayed_subst_term t in (m, uu____24625) in
        FStar_Syntax_Syntax.Meta_monadic uu____24618
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) ->
        let uu____24633 =
          let uu____24642 = elim_delayed_subst_term t in
          (m1, m2, uu____24642) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24633
    | m -> m
and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
    FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
      FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args ->
    FStar_List.map
      (fun uu____24665 ->
         match uu____24665 with
         | (t, q) ->
             let uu____24676 = elim_delayed_subst_term t in (uu____24676, q))
      args
and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs ->
    FStar_List.map
      (fun uu____24696 ->
         match uu____24696 with
         | (x, q) ->
             let uu____24707 =
               let uu___203_24708 = x in
               let uu____24709 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___203_24708.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___203_24708.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____24709
               } in
             (uu____24707, q)) bs
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
            | (uu____24785, FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____24791, FStar_Util.Inl t) ->
                let uu____24797 =
                  let uu____24800 =
                    let uu____24801 =
                      let uu____24814 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____24814) in
                    FStar_Syntax_Syntax.Tm_arrow uu____24801 in
                  FStar_Syntax_Syntax.mk uu____24800 in
                uu____24797 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____24818 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____24818 with
          | (univ_names1, t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = elim_delayed_subst_term t3 in
              let uu____24846 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____24901 ->
                    let uu____24902 =
                      let uu____24911 =
                        let uu____24912 = FStar_Syntax_Subst.compress t4 in
                        uu____24912.FStar_Syntax_Syntax.n in
                      (uu____24911, tc) in
                    (match uu____24902 with
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inr uu____24937) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inl uu____24974) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____25013, FStar_Util.Inl uu____25014) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____25037 -> failwith "Impossible") in
              (match uu____24846 with
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
          let uu____25142 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____25142 with
          | (univ_names1, binders1, tc) ->
              let uu____25200 = FStar_Util.left tc in
              (univ_names1, binders1, uu____25200)
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
          let uu____25235 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____25235 with
          | (univ_names1, binders1, tc) ->
              let uu____25295 = FStar_Util.right tc in
              (univ_names1, binders1, uu____25295)
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env ->
    fun s ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid, univ_names, binders, typ, lids, lids') ->
          let uu____25328 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____25328 with
           | (univ_names1, binders1, typ1) ->
               let uu___204_25356 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_25356.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_25356.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_25356.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_25356.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
          let uu___205_25377 = s in
          let uu____25378 =
            let uu____25379 =
              let uu____25388 = FStar_List.map (elim_uvars env) sigs in
              (uu____25388, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____25379 in
          {
            FStar_Syntax_Syntax.sigel = uu____25378;
            FStar_Syntax_Syntax.sigrng =
              (uu___205_25377.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___205_25377.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___205_25377.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___205_25377.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon
          (lid, univ_names, typ, lident, i, lids) ->
          let uu____25405 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____25405 with
           | (univ_names1, uu____25423, typ1) ->
               let uu___206_25437 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___206_25437.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___206_25437.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___206_25437.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___206_25437.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) ->
          let uu____25443 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____25443 with
           | (univ_names1, uu____25461, typ1) ->
               let uu___207_25475 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___207_25475.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___207_25475.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___207_25475.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___207_25475.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let uu____25509 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____25509 with
                    | (opening, lbunivs) ->
                        let elim t =
                          let uu____25532 =
                            let uu____25533 =
                              let uu____25534 =
                                FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env uu____25534 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____25533 in
                          elim_delayed_subst_term uu____25532 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___208_25537 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___208_25537.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___208_25537.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___208_25537.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___208_25537.FStar_Syntax_Syntax.lbpos)
                        })) in
          let uu___209_25538 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___209_25538.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___209_25538.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___209_25538.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___209_25538.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___210_25550 = s in
          let uu____25551 =
            let uu____25552 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____25552 in
          {
            FStar_Syntax_Syntax.sigel = uu____25551;
            FStar_Syntax_Syntax.sigrng =
              (uu___210_25550.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___210_25550.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___210_25550.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___210_25550.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l, us, t) ->
          let uu____25556 = elim_uvars_aux_t env us [] t in
          (match uu____25556 with
           | (us1, uu____25574, t1) ->
               let uu___211_25588 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_25588.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_25588.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_25588.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___211_25588.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____25589 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____25591 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____25591 with
           | (univs1, binders, signature) ->
               let uu____25619 =
                 let uu____25628 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____25628 with
                 | (univs_opening, univs2) ->
                     let uu____25655 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____25655) in
               (match uu____25619 with
                | (univs_opening, univs_closing) ->
                    let uu____25672 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____25678 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____25679 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____25678, uu____25679) in
                    (match uu____25672 with
                     | (b_opening, b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____25701 =
                           match uu____25701 with
                           | (us, t) ->
                               let n_us = FStar_List.length us in
                               let uu____25719 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____25719 with
                                | (us1, t1) ->
                                    let uu____25730 =
                                      let uu____25735 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____25742 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____25735, uu____25742) in
                                    (match uu____25730 with
                                     | (b_opening1, b_closing1) ->
                                         let uu____25755 =
                                           let uu____25760 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____25769 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____25760, uu____25769) in
                                         (match uu____25755 with
                                          | (univs_opening1, univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____25785 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____25785 in
                                              let uu____25786 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____25786 with
                                               | (uu____25807, uu____25808,
                                                  t3) ->
                                                   let t4 =
                                                     let uu____25823 =
                                                       let uu____25824 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____25824 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____25823 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____25829 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____25829 with
                           | (uu____25842, uu____25843, t1) -> t1 in
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
                             | uu____25903 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____25920 =
                               let uu____25921 =
                                 FStar_Syntax_Subst.compress body in
                               uu____25921.FStar_Syntax_Syntax.n in
                             match uu____25920 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,
                                  (FStar_Util.Inl typ,
                                   FStar_Pervasives_Native.None),
                                  FStar_Pervasives_Native.None)
                                 -> (defn, typ)
                             | uu____25980 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____26009 =
                               let uu____26010 =
                                 FStar_Syntax_Subst.compress t in
                               uu____26010.FStar_Syntax_Syntax.n in
                             match uu____26009 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars, body, uu____26031) ->
                                 let uu____26052 = destruct_action_body body in
                                 (match uu____26052 with
                                  | (defn, typ) -> (pars, defn, typ))
                             | uu____26097 ->
                                 let uu____26098 = destruct_action_body t in
                                 (match uu____26098 with
                                  | (defn, typ) -> ([], defn, typ)) in
                           let uu____26147 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____26147 with
                           | (action_univs, t) ->
                               let uu____26156 = destruct_action_typ_templ t in
                               (match uu____26156 with
                                | (action_params, action_defn, action_typ) ->
                                    let a' =
                                      let uu___212_26197 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___212_26197.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___212_26197.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___213_26199 = ed in
                           let uu____26200 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____26201 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____26202 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____26203 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____26204 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____26205 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____26206 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____26207 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____26208 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____26209 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____26210 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____26211 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____26212 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____26213 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___213_26199.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___213_26199.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____26200;
                             FStar_Syntax_Syntax.bind_wp = uu____26201;
                             FStar_Syntax_Syntax.if_then_else = uu____26202;
                             FStar_Syntax_Syntax.ite_wp = uu____26203;
                             FStar_Syntax_Syntax.stronger = uu____26204;
                             FStar_Syntax_Syntax.close_wp = uu____26205;
                             FStar_Syntax_Syntax.assert_p = uu____26206;
                             FStar_Syntax_Syntax.assume_p = uu____26207;
                             FStar_Syntax_Syntax.null_wp = uu____26208;
                             FStar_Syntax_Syntax.trivial = uu____26209;
                             FStar_Syntax_Syntax.repr = uu____26210;
                             FStar_Syntax_Syntax.return_repr = uu____26211;
                             FStar_Syntax_Syntax.bind_repr = uu____26212;
                             FStar_Syntax_Syntax.actions = uu____26213;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___213_26199.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         let uu___214_26216 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___214_26216.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___214_26216.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___214_26216.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___214_26216.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___96_26233 =
            match uu___96_26233 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us, t) ->
                let uu____26260 = elim_uvars_aux_t env us [] t in
                (match uu____26260 with
                 | (us1, uu____26284, t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___215_26303 = sub_eff in
            let uu____26304 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____26307 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___215_26303.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___215_26303.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____26304;
              FStar_Syntax_Syntax.lift = uu____26307
            } in
          let uu___216_26310 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___216_26310.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_26310.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_26310.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_26310.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid, univ_names, binders, comp, flags1) ->
          let uu____26320 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____26320 with
           | (univ_names1, binders1, comp1) ->
               let uu___217_26354 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___217_26354.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___217_26354.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___217_26354.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___217_26354.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____26365 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____26366 -> s
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env -> fun t -> normalize [EraseUniverses; AllowUnboundUniverses] env t