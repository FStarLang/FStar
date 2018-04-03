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
  | UnfoldFully of FStar_Ident.lid Prims.list 
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
  fun projectee  -> match projectee with | Beta  -> true | uu____28 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____32 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____36 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____41 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____52 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____56 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____60 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____64 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____68 -> false
  
let (uu___is_NoDeltaSteps : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____72 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____77 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____91 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____111 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____129 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____140 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____144 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____148 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____152 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____156 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____160 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____164 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____168 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____172 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____176 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____180 -> false
  
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____188 'Auu____189 .
    ('Auu____188 -> 'Auu____189) ->
      'Auu____189 ->
        'Auu____188 FStar_Pervasives_Native.option -> 'Auu____189
  =
  fun f  ->
    fun d  ->
      fun uu___77_206  ->
        match uu___77_206 with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> d
  
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
  unfold_fully: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  
let (__proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_fully
  
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
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
    unfold_fully = FStar_Pervasives_Native.None;
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
  fun s  ->
    fun fs  ->
      let add_opt x uu___78_1226 =
        match uu___78_1226 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1246 = fs  in
          {
            beta = true;
            iota = (uu___96_1246.iota);
            zeta = (uu___96_1246.zeta);
            weak = (uu___96_1246.weak);
            hnf = (uu___96_1246.hnf);
            primops = (uu___96_1246.primops);
            no_delta_steps = (uu___96_1246.no_delta_steps);
            unfold_until = (uu___96_1246.unfold_until);
            unfold_only = (uu___96_1246.unfold_only);
            unfold_fully = (uu___96_1246.unfold_fully);
            unfold_attr = (uu___96_1246.unfold_attr);
            unfold_tac = (uu___96_1246.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1246.pure_subterms_within_computations);
            simplify = (uu___96_1246.simplify);
            erase_universes = (uu___96_1246.erase_universes);
            allow_unbound_universes = (uu___96_1246.allow_unbound_universes);
            reify_ = (uu___96_1246.reify_);
            compress_uvars = (uu___96_1246.compress_uvars);
            no_full_norm = (uu___96_1246.no_full_norm);
            check_no_uvars = (uu___96_1246.check_no_uvars);
            unmeta = (uu___96_1246.unmeta);
            unascribe = (uu___96_1246.unascribe)
          }
      | Iota  ->
          let uu___97_1247 = fs  in
          {
            beta = (uu___97_1247.beta);
            iota = true;
            zeta = (uu___97_1247.zeta);
            weak = (uu___97_1247.weak);
            hnf = (uu___97_1247.hnf);
            primops = (uu___97_1247.primops);
            no_delta_steps = (uu___97_1247.no_delta_steps);
            unfold_until = (uu___97_1247.unfold_until);
            unfold_only = (uu___97_1247.unfold_only);
            unfold_fully = (uu___97_1247.unfold_fully);
            unfold_attr = (uu___97_1247.unfold_attr);
            unfold_tac = (uu___97_1247.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1247.pure_subterms_within_computations);
            simplify = (uu___97_1247.simplify);
            erase_universes = (uu___97_1247.erase_universes);
            allow_unbound_universes = (uu___97_1247.allow_unbound_universes);
            reify_ = (uu___97_1247.reify_);
            compress_uvars = (uu___97_1247.compress_uvars);
            no_full_norm = (uu___97_1247.no_full_norm);
            check_no_uvars = (uu___97_1247.check_no_uvars);
            unmeta = (uu___97_1247.unmeta);
            unascribe = (uu___97_1247.unascribe)
          }
      | Zeta  ->
          let uu___98_1248 = fs  in
          {
            beta = (uu___98_1248.beta);
            iota = (uu___98_1248.iota);
            zeta = true;
            weak = (uu___98_1248.weak);
            hnf = (uu___98_1248.hnf);
            primops = (uu___98_1248.primops);
            no_delta_steps = (uu___98_1248.no_delta_steps);
            unfold_until = (uu___98_1248.unfold_until);
            unfold_only = (uu___98_1248.unfold_only);
            unfold_fully = (uu___98_1248.unfold_fully);
            unfold_attr = (uu___98_1248.unfold_attr);
            unfold_tac = (uu___98_1248.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1248.pure_subterms_within_computations);
            simplify = (uu___98_1248.simplify);
            erase_universes = (uu___98_1248.erase_universes);
            allow_unbound_universes = (uu___98_1248.allow_unbound_universes);
            reify_ = (uu___98_1248.reify_);
            compress_uvars = (uu___98_1248.compress_uvars);
            no_full_norm = (uu___98_1248.no_full_norm);
            check_no_uvars = (uu___98_1248.check_no_uvars);
            unmeta = (uu___98_1248.unmeta);
            unascribe = (uu___98_1248.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___99_1249 = fs  in
          {
            beta = false;
            iota = (uu___99_1249.iota);
            zeta = (uu___99_1249.zeta);
            weak = (uu___99_1249.weak);
            hnf = (uu___99_1249.hnf);
            primops = (uu___99_1249.primops);
            no_delta_steps = (uu___99_1249.no_delta_steps);
            unfold_until = (uu___99_1249.unfold_until);
            unfold_only = (uu___99_1249.unfold_only);
            unfold_fully = (uu___99_1249.unfold_fully);
            unfold_attr = (uu___99_1249.unfold_attr);
            unfold_tac = (uu___99_1249.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1249.pure_subterms_within_computations);
            simplify = (uu___99_1249.simplify);
            erase_universes = (uu___99_1249.erase_universes);
            allow_unbound_universes = (uu___99_1249.allow_unbound_universes);
            reify_ = (uu___99_1249.reify_);
            compress_uvars = (uu___99_1249.compress_uvars);
            no_full_norm = (uu___99_1249.no_full_norm);
            check_no_uvars = (uu___99_1249.check_no_uvars);
            unmeta = (uu___99_1249.unmeta);
            unascribe = (uu___99_1249.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___100_1250 = fs  in
          {
            beta = (uu___100_1250.beta);
            iota = false;
            zeta = (uu___100_1250.zeta);
            weak = (uu___100_1250.weak);
            hnf = (uu___100_1250.hnf);
            primops = (uu___100_1250.primops);
            no_delta_steps = (uu___100_1250.no_delta_steps);
            unfold_until = (uu___100_1250.unfold_until);
            unfold_only = (uu___100_1250.unfold_only);
            unfold_fully = (uu___100_1250.unfold_fully);
            unfold_attr = (uu___100_1250.unfold_attr);
            unfold_tac = (uu___100_1250.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1250.pure_subterms_within_computations);
            simplify = (uu___100_1250.simplify);
            erase_universes = (uu___100_1250.erase_universes);
            allow_unbound_universes = (uu___100_1250.allow_unbound_universes);
            reify_ = (uu___100_1250.reify_);
            compress_uvars = (uu___100_1250.compress_uvars);
            no_full_norm = (uu___100_1250.no_full_norm);
            check_no_uvars = (uu___100_1250.check_no_uvars);
            unmeta = (uu___100_1250.unmeta);
            unascribe = (uu___100_1250.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___101_1251 = fs  in
          {
            beta = (uu___101_1251.beta);
            iota = (uu___101_1251.iota);
            zeta = false;
            weak = (uu___101_1251.weak);
            hnf = (uu___101_1251.hnf);
            primops = (uu___101_1251.primops);
            no_delta_steps = (uu___101_1251.no_delta_steps);
            unfold_until = (uu___101_1251.unfold_until);
            unfold_only = (uu___101_1251.unfold_only);
            unfold_fully = (uu___101_1251.unfold_fully);
            unfold_attr = (uu___101_1251.unfold_attr);
            unfold_tac = (uu___101_1251.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1251.pure_subterms_within_computations);
            simplify = (uu___101_1251.simplify);
            erase_universes = (uu___101_1251.erase_universes);
            allow_unbound_universes = (uu___101_1251.allow_unbound_universes);
            reify_ = (uu___101_1251.reify_);
            compress_uvars = (uu___101_1251.compress_uvars);
            no_full_norm = (uu___101_1251.no_full_norm);
            check_no_uvars = (uu___101_1251.check_no_uvars);
            unmeta = (uu___101_1251.unmeta);
            unascribe = (uu___101_1251.unascribe)
          }
      | Exclude uu____1252 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1253 = fs  in
          {
            beta = (uu___102_1253.beta);
            iota = (uu___102_1253.iota);
            zeta = (uu___102_1253.zeta);
            weak = true;
            hnf = (uu___102_1253.hnf);
            primops = (uu___102_1253.primops);
            no_delta_steps = (uu___102_1253.no_delta_steps);
            unfold_until = (uu___102_1253.unfold_until);
            unfold_only = (uu___102_1253.unfold_only);
            unfold_fully = (uu___102_1253.unfold_fully);
            unfold_attr = (uu___102_1253.unfold_attr);
            unfold_tac = (uu___102_1253.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1253.pure_subterms_within_computations);
            simplify = (uu___102_1253.simplify);
            erase_universes = (uu___102_1253.erase_universes);
            allow_unbound_universes = (uu___102_1253.allow_unbound_universes);
            reify_ = (uu___102_1253.reify_);
            compress_uvars = (uu___102_1253.compress_uvars);
            no_full_norm = (uu___102_1253.no_full_norm);
            check_no_uvars = (uu___102_1253.check_no_uvars);
            unmeta = (uu___102_1253.unmeta);
            unascribe = (uu___102_1253.unascribe)
          }
      | HNF  ->
          let uu___103_1254 = fs  in
          {
            beta = (uu___103_1254.beta);
            iota = (uu___103_1254.iota);
            zeta = (uu___103_1254.zeta);
            weak = (uu___103_1254.weak);
            hnf = true;
            primops = (uu___103_1254.primops);
            no_delta_steps = (uu___103_1254.no_delta_steps);
            unfold_until = (uu___103_1254.unfold_until);
            unfold_only = (uu___103_1254.unfold_only);
            unfold_fully = (uu___103_1254.unfold_fully);
            unfold_attr = (uu___103_1254.unfold_attr);
            unfold_tac = (uu___103_1254.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1254.pure_subterms_within_computations);
            simplify = (uu___103_1254.simplify);
            erase_universes = (uu___103_1254.erase_universes);
            allow_unbound_universes = (uu___103_1254.allow_unbound_universes);
            reify_ = (uu___103_1254.reify_);
            compress_uvars = (uu___103_1254.compress_uvars);
            no_full_norm = (uu___103_1254.no_full_norm);
            check_no_uvars = (uu___103_1254.check_no_uvars);
            unmeta = (uu___103_1254.unmeta);
            unascribe = (uu___103_1254.unascribe)
          }
      | Primops  ->
          let uu___104_1255 = fs  in
          {
            beta = (uu___104_1255.beta);
            iota = (uu___104_1255.iota);
            zeta = (uu___104_1255.zeta);
            weak = (uu___104_1255.weak);
            hnf = (uu___104_1255.hnf);
            primops = true;
            no_delta_steps = (uu___104_1255.no_delta_steps);
            unfold_until = (uu___104_1255.unfold_until);
            unfold_only = (uu___104_1255.unfold_only);
            unfold_fully = (uu___104_1255.unfold_fully);
            unfold_attr = (uu___104_1255.unfold_attr);
            unfold_tac = (uu___104_1255.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1255.pure_subterms_within_computations);
            simplify = (uu___104_1255.simplify);
            erase_universes = (uu___104_1255.erase_universes);
            allow_unbound_universes = (uu___104_1255.allow_unbound_universes);
            reify_ = (uu___104_1255.reify_);
            compress_uvars = (uu___104_1255.compress_uvars);
            no_full_norm = (uu___104_1255.no_full_norm);
            check_no_uvars = (uu___104_1255.check_no_uvars);
            unmeta = (uu___104_1255.unmeta);
            unascribe = (uu___104_1255.unascribe)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | NoDeltaSteps  ->
          let uu___105_1256 = fs  in
          {
            beta = (uu___105_1256.beta);
            iota = (uu___105_1256.iota);
            zeta = (uu___105_1256.zeta);
            weak = (uu___105_1256.weak);
            hnf = (uu___105_1256.hnf);
            primops = (uu___105_1256.primops);
            no_delta_steps = true;
            unfold_until = (uu___105_1256.unfold_until);
            unfold_only = (uu___105_1256.unfold_only);
            unfold_fully = (uu___105_1256.unfold_fully);
            unfold_attr = (uu___105_1256.unfold_attr);
            unfold_tac = (uu___105_1256.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1256.pure_subterms_within_computations);
            simplify = (uu___105_1256.simplify);
            erase_universes = (uu___105_1256.erase_universes);
            allow_unbound_universes = (uu___105_1256.allow_unbound_universes);
            reify_ = (uu___105_1256.reify_);
            compress_uvars = (uu___105_1256.compress_uvars);
            no_full_norm = (uu___105_1256.no_full_norm);
            check_no_uvars = (uu___105_1256.check_no_uvars);
            unmeta = (uu___105_1256.unmeta);
            unascribe = (uu___105_1256.unascribe)
          }
      | UnfoldUntil d ->
          let uu___106_1258 = fs  in
          {
            beta = (uu___106_1258.beta);
            iota = (uu___106_1258.iota);
            zeta = (uu___106_1258.zeta);
            weak = (uu___106_1258.weak);
            hnf = (uu___106_1258.hnf);
            primops = (uu___106_1258.primops);
            no_delta_steps = (uu___106_1258.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1258.unfold_only);
            unfold_fully = (uu___106_1258.unfold_fully);
            unfold_attr = (uu___106_1258.unfold_attr);
            unfold_tac = (uu___106_1258.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1258.pure_subterms_within_computations);
            simplify = (uu___106_1258.simplify);
            erase_universes = (uu___106_1258.erase_universes);
            allow_unbound_universes = (uu___106_1258.allow_unbound_universes);
            reify_ = (uu___106_1258.reify_);
            compress_uvars = (uu___106_1258.compress_uvars);
            no_full_norm = (uu___106_1258.no_full_norm);
            check_no_uvars = (uu___106_1258.check_no_uvars);
            unmeta = (uu___106_1258.unmeta);
            unascribe = (uu___106_1258.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___107_1262 = fs  in
          {
            beta = (uu___107_1262.beta);
            iota = (uu___107_1262.iota);
            zeta = (uu___107_1262.zeta);
            weak = (uu___107_1262.weak);
            hnf = (uu___107_1262.hnf);
            primops = (uu___107_1262.primops);
            no_delta_steps = (uu___107_1262.no_delta_steps);
            unfold_until = (uu___107_1262.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___107_1262.unfold_fully);
            unfold_attr = (uu___107_1262.unfold_attr);
            unfold_tac = (uu___107_1262.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1262.pure_subterms_within_computations);
            simplify = (uu___107_1262.simplify);
            erase_universes = (uu___107_1262.erase_universes);
            allow_unbound_universes = (uu___107_1262.allow_unbound_universes);
            reify_ = (uu___107_1262.reify_);
            compress_uvars = (uu___107_1262.compress_uvars);
            no_full_norm = (uu___107_1262.no_full_norm);
            check_no_uvars = (uu___107_1262.check_no_uvars);
            unmeta = (uu___107_1262.unmeta);
            unascribe = (uu___107_1262.unascribe)
          }
      | UnfoldFully lids ->
          let uu___108_1268 = fs  in
          {
            beta = (uu___108_1268.beta);
            iota = (uu___108_1268.iota);
            zeta = (uu___108_1268.zeta);
            weak = (uu___108_1268.weak);
            hnf = (uu___108_1268.hnf);
            primops = (uu___108_1268.primops);
            no_delta_steps = (uu___108_1268.no_delta_steps);
            unfold_until = (uu___108_1268.unfold_until);
            unfold_only = (uu___108_1268.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___108_1268.unfold_attr);
            unfold_tac = (uu___108_1268.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1268.pure_subterms_within_computations);
            simplify = (uu___108_1268.simplify);
            erase_universes = (uu___108_1268.erase_universes);
            allow_unbound_universes = (uu___108_1268.allow_unbound_universes);
            reify_ = (uu___108_1268.reify_);
            compress_uvars = (uu___108_1268.compress_uvars);
            no_full_norm = (uu___108_1268.no_full_norm);
            check_no_uvars = (uu___108_1268.check_no_uvars);
            unmeta = (uu___108_1268.unmeta);
            unascribe = (uu___108_1268.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___109_1272 = fs  in
          {
            beta = (uu___109_1272.beta);
            iota = (uu___109_1272.iota);
            zeta = (uu___109_1272.zeta);
            weak = (uu___109_1272.weak);
            hnf = (uu___109_1272.hnf);
            primops = (uu___109_1272.primops);
            no_delta_steps = (uu___109_1272.no_delta_steps);
            unfold_until = (uu___109_1272.unfold_until);
            unfold_only = (uu___109_1272.unfold_only);
            unfold_fully = (uu___109_1272.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___109_1272.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1272.pure_subterms_within_computations);
            simplify = (uu___109_1272.simplify);
            erase_universes = (uu___109_1272.erase_universes);
            allow_unbound_universes = (uu___109_1272.allow_unbound_universes);
            reify_ = (uu___109_1272.reify_);
            compress_uvars = (uu___109_1272.compress_uvars);
            no_full_norm = (uu___109_1272.no_full_norm);
            check_no_uvars = (uu___109_1272.check_no_uvars);
            unmeta = (uu___109_1272.unmeta);
            unascribe = (uu___109_1272.unascribe)
          }
      | UnfoldTac  ->
          let uu___110_1273 = fs  in
          {
            beta = (uu___110_1273.beta);
            iota = (uu___110_1273.iota);
            zeta = (uu___110_1273.zeta);
            weak = (uu___110_1273.weak);
            hnf = (uu___110_1273.hnf);
            primops = (uu___110_1273.primops);
            no_delta_steps = (uu___110_1273.no_delta_steps);
            unfold_until = (uu___110_1273.unfold_until);
            unfold_only = (uu___110_1273.unfold_only);
            unfold_fully = (uu___110_1273.unfold_fully);
            unfold_attr = (uu___110_1273.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___110_1273.pure_subterms_within_computations);
            simplify = (uu___110_1273.simplify);
            erase_universes = (uu___110_1273.erase_universes);
            allow_unbound_universes = (uu___110_1273.allow_unbound_universes);
            reify_ = (uu___110_1273.reify_);
            compress_uvars = (uu___110_1273.compress_uvars);
            no_full_norm = (uu___110_1273.no_full_norm);
            check_no_uvars = (uu___110_1273.check_no_uvars);
            unmeta = (uu___110_1273.unmeta);
            unascribe = (uu___110_1273.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___111_1274 = fs  in
          {
            beta = (uu___111_1274.beta);
            iota = (uu___111_1274.iota);
            zeta = (uu___111_1274.zeta);
            weak = (uu___111_1274.weak);
            hnf = (uu___111_1274.hnf);
            primops = (uu___111_1274.primops);
            no_delta_steps = (uu___111_1274.no_delta_steps);
            unfold_until = (uu___111_1274.unfold_until);
            unfold_only = (uu___111_1274.unfold_only);
            unfold_fully = (uu___111_1274.unfold_fully);
            unfold_attr = (uu___111_1274.unfold_attr);
            unfold_tac = (uu___111_1274.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___111_1274.simplify);
            erase_universes = (uu___111_1274.erase_universes);
            allow_unbound_universes = (uu___111_1274.allow_unbound_universes);
            reify_ = (uu___111_1274.reify_);
            compress_uvars = (uu___111_1274.compress_uvars);
            no_full_norm = (uu___111_1274.no_full_norm);
            check_no_uvars = (uu___111_1274.check_no_uvars);
            unmeta = (uu___111_1274.unmeta);
            unascribe = (uu___111_1274.unascribe)
          }
      | Simplify  ->
          let uu___112_1275 = fs  in
          {
            beta = (uu___112_1275.beta);
            iota = (uu___112_1275.iota);
            zeta = (uu___112_1275.zeta);
            weak = (uu___112_1275.weak);
            hnf = (uu___112_1275.hnf);
            primops = (uu___112_1275.primops);
            no_delta_steps = (uu___112_1275.no_delta_steps);
            unfold_until = (uu___112_1275.unfold_until);
            unfold_only = (uu___112_1275.unfold_only);
            unfold_fully = (uu___112_1275.unfold_fully);
            unfold_attr = (uu___112_1275.unfold_attr);
            unfold_tac = (uu___112_1275.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1275.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___112_1275.erase_universes);
            allow_unbound_universes = (uu___112_1275.allow_unbound_universes);
            reify_ = (uu___112_1275.reify_);
            compress_uvars = (uu___112_1275.compress_uvars);
            no_full_norm = (uu___112_1275.no_full_norm);
            check_no_uvars = (uu___112_1275.check_no_uvars);
            unmeta = (uu___112_1275.unmeta);
            unascribe = (uu___112_1275.unascribe)
          }
      | EraseUniverses  ->
          let uu___113_1276 = fs  in
          {
            beta = (uu___113_1276.beta);
            iota = (uu___113_1276.iota);
            zeta = (uu___113_1276.zeta);
            weak = (uu___113_1276.weak);
            hnf = (uu___113_1276.hnf);
            primops = (uu___113_1276.primops);
            no_delta_steps = (uu___113_1276.no_delta_steps);
            unfold_until = (uu___113_1276.unfold_until);
            unfold_only = (uu___113_1276.unfold_only);
            unfold_fully = (uu___113_1276.unfold_fully);
            unfold_attr = (uu___113_1276.unfold_attr);
            unfold_tac = (uu___113_1276.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1276.pure_subterms_within_computations);
            simplify = (uu___113_1276.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___113_1276.allow_unbound_universes);
            reify_ = (uu___113_1276.reify_);
            compress_uvars = (uu___113_1276.compress_uvars);
            no_full_norm = (uu___113_1276.no_full_norm);
            check_no_uvars = (uu___113_1276.check_no_uvars);
            unmeta = (uu___113_1276.unmeta);
            unascribe = (uu___113_1276.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___114_1277 = fs  in
          {
            beta = (uu___114_1277.beta);
            iota = (uu___114_1277.iota);
            zeta = (uu___114_1277.zeta);
            weak = (uu___114_1277.weak);
            hnf = (uu___114_1277.hnf);
            primops = (uu___114_1277.primops);
            no_delta_steps = (uu___114_1277.no_delta_steps);
            unfold_until = (uu___114_1277.unfold_until);
            unfold_only = (uu___114_1277.unfold_only);
            unfold_fully = (uu___114_1277.unfold_fully);
            unfold_attr = (uu___114_1277.unfold_attr);
            unfold_tac = (uu___114_1277.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1277.pure_subterms_within_computations);
            simplify = (uu___114_1277.simplify);
            erase_universes = (uu___114_1277.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___114_1277.reify_);
            compress_uvars = (uu___114_1277.compress_uvars);
            no_full_norm = (uu___114_1277.no_full_norm);
            check_no_uvars = (uu___114_1277.check_no_uvars);
            unmeta = (uu___114_1277.unmeta);
            unascribe = (uu___114_1277.unascribe)
          }
      | Reify  ->
          let uu___115_1278 = fs  in
          {
            beta = (uu___115_1278.beta);
            iota = (uu___115_1278.iota);
            zeta = (uu___115_1278.zeta);
            weak = (uu___115_1278.weak);
            hnf = (uu___115_1278.hnf);
            primops = (uu___115_1278.primops);
            no_delta_steps = (uu___115_1278.no_delta_steps);
            unfold_until = (uu___115_1278.unfold_until);
            unfold_only = (uu___115_1278.unfold_only);
            unfold_fully = (uu___115_1278.unfold_fully);
            unfold_attr = (uu___115_1278.unfold_attr);
            unfold_tac = (uu___115_1278.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1278.pure_subterms_within_computations);
            simplify = (uu___115_1278.simplify);
            erase_universes = (uu___115_1278.erase_universes);
            allow_unbound_universes = (uu___115_1278.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___115_1278.compress_uvars);
            no_full_norm = (uu___115_1278.no_full_norm);
            check_no_uvars = (uu___115_1278.check_no_uvars);
            unmeta = (uu___115_1278.unmeta);
            unascribe = (uu___115_1278.unascribe)
          }
      | CompressUvars  ->
          let uu___116_1279 = fs  in
          {
            beta = (uu___116_1279.beta);
            iota = (uu___116_1279.iota);
            zeta = (uu___116_1279.zeta);
            weak = (uu___116_1279.weak);
            hnf = (uu___116_1279.hnf);
            primops = (uu___116_1279.primops);
            no_delta_steps = (uu___116_1279.no_delta_steps);
            unfold_until = (uu___116_1279.unfold_until);
            unfold_only = (uu___116_1279.unfold_only);
            unfold_fully = (uu___116_1279.unfold_fully);
            unfold_attr = (uu___116_1279.unfold_attr);
            unfold_tac = (uu___116_1279.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1279.pure_subterms_within_computations);
            simplify = (uu___116_1279.simplify);
            erase_universes = (uu___116_1279.erase_universes);
            allow_unbound_universes = (uu___116_1279.allow_unbound_universes);
            reify_ = (uu___116_1279.reify_);
            compress_uvars = true;
            no_full_norm = (uu___116_1279.no_full_norm);
            check_no_uvars = (uu___116_1279.check_no_uvars);
            unmeta = (uu___116_1279.unmeta);
            unascribe = (uu___116_1279.unascribe)
          }
      | NoFullNorm  ->
          let uu___117_1280 = fs  in
          {
            beta = (uu___117_1280.beta);
            iota = (uu___117_1280.iota);
            zeta = (uu___117_1280.zeta);
            weak = (uu___117_1280.weak);
            hnf = (uu___117_1280.hnf);
            primops = (uu___117_1280.primops);
            no_delta_steps = (uu___117_1280.no_delta_steps);
            unfold_until = (uu___117_1280.unfold_until);
            unfold_only = (uu___117_1280.unfold_only);
            unfold_fully = (uu___117_1280.unfold_fully);
            unfold_attr = (uu___117_1280.unfold_attr);
            unfold_tac = (uu___117_1280.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1280.pure_subterms_within_computations);
            simplify = (uu___117_1280.simplify);
            erase_universes = (uu___117_1280.erase_universes);
            allow_unbound_universes = (uu___117_1280.allow_unbound_universes);
            reify_ = (uu___117_1280.reify_);
            compress_uvars = (uu___117_1280.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___117_1280.check_no_uvars);
            unmeta = (uu___117_1280.unmeta);
            unascribe = (uu___117_1280.unascribe)
          }
      | CheckNoUvars  ->
          let uu___118_1281 = fs  in
          {
            beta = (uu___118_1281.beta);
            iota = (uu___118_1281.iota);
            zeta = (uu___118_1281.zeta);
            weak = (uu___118_1281.weak);
            hnf = (uu___118_1281.hnf);
            primops = (uu___118_1281.primops);
            no_delta_steps = (uu___118_1281.no_delta_steps);
            unfold_until = (uu___118_1281.unfold_until);
            unfold_only = (uu___118_1281.unfold_only);
            unfold_fully = (uu___118_1281.unfold_fully);
            unfold_attr = (uu___118_1281.unfold_attr);
            unfold_tac = (uu___118_1281.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1281.pure_subterms_within_computations);
            simplify = (uu___118_1281.simplify);
            erase_universes = (uu___118_1281.erase_universes);
            allow_unbound_universes = (uu___118_1281.allow_unbound_universes);
            reify_ = (uu___118_1281.reify_);
            compress_uvars = (uu___118_1281.compress_uvars);
            no_full_norm = (uu___118_1281.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___118_1281.unmeta);
            unascribe = (uu___118_1281.unascribe)
          }
      | Unmeta  ->
          let uu___119_1282 = fs  in
          {
            beta = (uu___119_1282.beta);
            iota = (uu___119_1282.iota);
            zeta = (uu___119_1282.zeta);
            weak = (uu___119_1282.weak);
            hnf = (uu___119_1282.hnf);
            primops = (uu___119_1282.primops);
            no_delta_steps = (uu___119_1282.no_delta_steps);
            unfold_until = (uu___119_1282.unfold_until);
            unfold_only = (uu___119_1282.unfold_only);
            unfold_fully = (uu___119_1282.unfold_fully);
            unfold_attr = (uu___119_1282.unfold_attr);
            unfold_tac = (uu___119_1282.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1282.pure_subterms_within_computations);
            simplify = (uu___119_1282.simplify);
            erase_universes = (uu___119_1282.erase_universes);
            allow_unbound_universes = (uu___119_1282.allow_unbound_universes);
            reify_ = (uu___119_1282.reify_);
            compress_uvars = (uu___119_1282.compress_uvars);
            no_full_norm = (uu___119_1282.no_full_norm);
            check_no_uvars = (uu___119_1282.check_no_uvars);
            unmeta = true;
            unascribe = (uu___119_1282.unascribe)
          }
      | Unascribe  ->
          let uu___120_1283 = fs  in
          {
            beta = (uu___120_1283.beta);
            iota = (uu___120_1283.iota);
            zeta = (uu___120_1283.zeta);
            weak = (uu___120_1283.weak);
            hnf = (uu___120_1283.hnf);
            primops = (uu___120_1283.primops);
            no_delta_steps = (uu___120_1283.no_delta_steps);
            unfold_until = (uu___120_1283.unfold_until);
            unfold_only = (uu___120_1283.unfold_only);
            unfold_fully = (uu___120_1283.unfold_fully);
            unfold_attr = (uu___120_1283.unfold_attr);
            unfold_tac = (uu___120_1283.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1283.pure_subterms_within_computations);
            simplify = (uu___120_1283.simplify);
            erase_universes = (uu___120_1283.erase_universes);
            allow_unbound_universes = (uu___120_1283.allow_unbound_universes);
            reify_ = (uu___120_1283.reify_);
            compress_uvars = (uu___120_1283.compress_uvars);
            no_full_norm = (uu___120_1283.no_full_norm);
            check_no_uvars = (uu___120_1283.check_no_uvars);
            unmeta = (uu___120_1283.unmeta);
            unascribe = true
          }
  
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t }[@@deriving show]
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
  
let (__proj__Mkpsc__item__psc_subst :
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
  
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1322  -> []) } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
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
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
  
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
  
let (__proj__Mkprimitive_step__item__auto_reflect :
  primitive_step -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__auto_reflect
  
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
  
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee  ->
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
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
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
  | Dummy [@@deriving show]
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____1565 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1667 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1678 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___79_1697  ->
    match uu___79_1697 with
    | Clos (uu____1698,t,uu____1700,uu____1701) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1746 -> "Univ"
    | Dummy  -> "dummy"
  
type debug_switches =
  {
  gen: Prims.bool ;
  primop: Prims.bool ;
  b380: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }[@@deriving show]
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
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
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__steps
  
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__tcenv
  
let (__proj__Mkcfg__item__debug : cfg -> debug_switches) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__debug
  
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__delta_level
  
let (__proj__Mkcfg__item__primitive_steps :
  cfg -> primitive_step FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__primitive_steps
  
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__strong
  
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__memoize_lazy
  
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee  ->
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
  fun m  ->
    fun l  ->
      FStar_List.fold_right
        (fun p  ->
           fun m1  ->
             let uu____1998 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____1998 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2010 = FStar_Util.psmap_empty ()  in add_steps uu____2010 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2021 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2021
  
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
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____2163 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2199 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2235 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2304 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2346 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2402 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2442 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2474 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2510 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2526 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2551 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2551 with | (hd1,uu____2565) -> hd1
  
let mk :
  'Auu____2585 .
    'Auu____2585 ->
      FStar_Range.range -> 'Auu____2585 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2639 = FStar_ST.op_Bang r  in
          match uu____2639 with
          | FStar_Pervasives_Native.Some uu____2687 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2741 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2741 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_2748  ->
    match uu___80_2748 with
    | Arg (c,uu____2750,uu____2751) ->
        let uu____2752 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2752
    | MemoLazy uu____2753 -> "MemoLazy"
    | Abs (uu____2760,bs,uu____2762,uu____2763,uu____2764) ->
        let uu____2769 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2769
    | UnivArgs uu____2774 -> "UnivArgs"
    | Match uu____2781 -> "Match"
    | App (uu____2788,t,uu____2790,uu____2791) ->
        let uu____2792 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2792
    | Meta (m,uu____2794) -> "Meta"
    | Let uu____2795 -> "Let"
    | Cfg uu____2804 -> "Cfg"
    | Debug (t,uu____2806) ->
        let uu____2807 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2807
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2815 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2815 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2846 . 'Auu____2846 Prims.list -> Prims.bool =
  fun uu___81_2852  ->
    match uu___81_2852 with | [] -> true | uu____2855 -> false
  
let lookup_bvar :
  'Auu____2862 'Auu____2863 .
    ('Auu____2862,'Auu____2863) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2863
  =
  fun env  ->
    fun x  ->
      try
        let uu____2887 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2887
      with
      | uu____2900 ->
          let uu____2901 =
            let uu____2902 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2902  in
          failwith uu____2901
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____2908 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____2908
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____2912 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____2912
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____2916 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____2916
          then
            FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
          else FStar_Pervasives_Native.None))
  
let (norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____2942 =
            FStar_List.fold_left
              (fun uu____2968  ->
                 fun u1  ->
                   match uu____2968 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2993 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2993 with
                        | (k_u,n1) ->
                            let uu____3008 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3008
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2942 with
          | (uu____3026,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3051 =
                   let uu____3052 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3052  in
                 match uu____3051 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3070 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3078 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3084 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3093 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3102 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3109 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3109 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3126 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3126 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3134 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3142 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3142 with
                                  | (uu____3147,m) -> n1 <= m))
                           in
                        if uu____3134 then rest1 else us1
                    | uu____3152 -> us1)
               | uu____3157 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3161 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3161
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3165 = aux u  in
           match uu____3165 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____3269  ->
             let uu____3270 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3271 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3270
               uu____3271);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3278 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3280 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3305 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3306 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3307 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3308 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3309 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3326 =
                      let uu____3327 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3328 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3327 uu____3328
                       in
                    failwith uu____3326
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3331 =
                    let uu____3332 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3332  in
                  mk uu____3331 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3339 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3339
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3341 = lookup_bvar env x  in
                  (match uu____3341 with
                   | Univ uu____3344 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3347,uu____3348) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3460 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3460 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3488 =
                         let uu____3489 =
                           let uu____3506 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3506)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3489  in
                       mk uu____3488 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3537 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3537 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3579 =
                    let uu____3590 =
                      let uu____3597 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3597]  in
                    closures_as_binders_delayed cfg env uu____3590  in
                  (match uu____3579 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3615 =
                         let uu____3616 =
                           let uu____3623 =
                             let uu____3624 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3624
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3623, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3616  in
                       mk uu____3615 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3715 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3715
                    | FStar_Util.Inr c ->
                        let uu____3729 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3729
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3745 =
                    let uu____3746 =
                      let uu____3773 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3773, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3746  in
                  mk uu____3745 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                  (match qi.FStar_Syntax_Syntax.qkind with
                   | FStar_Syntax_Syntax.Quote_dynamic  ->
                       let uu____3814 =
                         let uu____3815 =
                           let uu____3822 =
                             closure_as_term_delayed cfg env t'  in
                           (uu____3822, qi)  in
                         FStar_Syntax_Syntax.Tm_quoted uu____3815  in
                       mk uu____3814 t1.FStar_Syntax_Syntax.pos
                   | FStar_Syntax_Syntax.Quote_static  ->
                       let qi1 =
                         FStar_Syntax_Syntax.on_antiquoted
                           (closure_as_term_delayed cfg env) qi
                          in
                       mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3846 =
                    let uu____3847 =
                      let uu____3854 = closure_as_term_delayed cfg env t'  in
                      let uu____3857 =
                        let uu____3858 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3858  in
                      (uu____3854, uu____3857)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3847  in
                  mk uu____3846 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3918 =
                    let uu____3919 =
                      let uu____3926 = closure_as_term_delayed cfg env t'  in
                      let uu____3929 =
                        let uu____3930 =
                          let uu____3937 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3937)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3930  in
                      (uu____3926, uu____3929)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3919  in
                  mk uu____3918 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3956 =
                    let uu____3957 =
                      let uu____3964 = closure_as_term_delayed cfg env t'  in
                      let uu____3967 =
                        let uu____3968 =
                          let uu____3977 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3977)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3968  in
                      (uu____3964, uu____3967)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3957  in
                  mk uu____3956 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3990 =
                    let uu____3991 =
                      let uu____3998 = closure_as_term_delayed cfg env t'  in
                      (uu____3998, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3991  in
                  mk uu____3990 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____4038  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____4057 =
                    let uu____4068 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____4068
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____4087 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___125_4099 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_4099.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_4099.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____4087))
                     in
                  (match uu____4057 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___126_4115 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___126_4115.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___126_4115.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___126_4115.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___126_4115.FStar_Syntax_Syntax.lbpos)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____4126,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____4185  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____4210 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4210
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4230  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4252 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4252
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___127_4264 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_4264.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_4264.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___128_4265 = lb  in
                    let uu____4266 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___128_4265.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___128_4265.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4266;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___128_4265.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___128_4265.FStar_Syntax_Syntax.lbpos)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4296  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4385 =
                    match uu____4385 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4440 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4461 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4521  ->
                                        fun uu____4522  ->
                                          match (uu____4521, uu____4522) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4613 =
                                                norm_pat env3 p1  in
                                              (match uu____4613 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4461 with
                               | (pats1,env3) ->
                                   ((let uu___129_4695 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___129_4695.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___130_4714 = x  in
                                let uu____4715 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___130_4714.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___130_4714.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4715
                                }  in
                              ((let uu___131_4729 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___131_4729.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___132_4740 = x  in
                                let uu____4741 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___132_4740.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___132_4740.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4741
                                }  in
                              ((let uu___133_4755 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___133_4755.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___134_4771 = x  in
                                let uu____4772 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___134_4771.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___134_4771.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4772
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___135_4779 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___135_4779.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4782 = norm_pat env1 pat  in
                        (match uu____4782 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4811 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4811
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4817 =
                    let uu____4818 =
                      let uu____4841 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4841)  in
                    FStar_Syntax_Syntax.Tm_match uu____4818  in
                  mk uu____4817 t1.FStar_Syntax_Syntax.pos))

and (closure_as_term_delayed :
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> t
        | uu____4927 -> closure_as_term cfg env t

and (closures_as_args_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> args
        | uu____4953 ->
            FStar_List.map
              (fun uu____4970  ->
                 match uu____4970 with
                 | (x,imp) ->
                     let uu____4989 = closure_as_term_delayed cfg env x  in
                     (uu____4989, imp)) args

and (closures_as_binders_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____5003 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5052  ->
                  fun uu____5053  ->
                    match (uu____5052, uu____5053) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___136_5123 = b  in
                          let uu____5124 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___136_5123.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___136_5123.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5124
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5003 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

and (close_comp :
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> c
        | uu____5217 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5230 = closure_as_term_delayed cfg env t  in
                 let uu____5231 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5230 uu____5231
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5244 = closure_as_term_delayed cfg env t  in
                 let uu____5245 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5244 uu____5245
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_5271  ->
                           match uu___82_5271 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5275 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5275
                           | f -> f))
                    in
                 let uu____5279 =
                   let uu___137_5280 = c1  in
                   let uu____5281 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5281;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___137_5280.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5279)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_5291  ->
            match uu___83_5291 with
            | FStar_Syntax_Syntax.DECREASES uu____5292 -> false
            | uu____5295 -> true))

and (close_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___84_5313  ->
                      match uu___84_5313 with
                      | FStar_Syntax_Syntax.DECREASES uu____5314 -> false
                      | uu____5317 -> true))
               in
            let rc1 =
              let uu___138_5319 = rc  in
              let uu____5320 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___138_5319.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5320;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5327 -> lopt

let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_int)
     in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_bool)
     in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_char)
     in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_string)
     in
  let arg_as_list a e a =
    let uu____5409 =
      let uu____5416 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____5416  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5409  in
  let arg_as_bounded_int uu____5440 =
    match uu____5440 with
    | (a,uu____5452) ->
        let uu____5459 =
          let uu____5460 = FStar_Syntax_Subst.compress a  in
          uu____5460.FStar_Syntax_Syntax.n  in
        (match uu____5459 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5470;
                FStar_Syntax_Syntax.vars = uu____5471;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5473;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5474;_},uu____5475)::[])
             when
             let uu____5514 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5514 "int_to_t" ->
             let uu____5515 =
               let uu____5520 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5520)  in
             FStar_Pervasives_Native.Some uu____5515
         | uu____5525 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5565 = f a  in FStar_Pervasives_Native.Some uu____5565
    | uu____5566 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5614 = f a0 a1  in FStar_Pervasives_Native.Some uu____5614
    | uu____5615 -> FStar_Pervasives_Native.None  in
  let unary_op a394 a395 a396 a397 a398 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5657 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a393  -> (Obj.magic (f res.psc_range)) a393)
                    uu____5657)) a394 a395 a396 a397 a398
     in
  let binary_op a401 a402 a403 a404 a405 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5706 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a399  ->
                       fun a400  -> (Obj.magic (f res.psc_range)) a399 a400)
                    uu____5706)) a401 a402 a403 a404 a405
     in
  let as_primitive_step is_strong uu____5733 =
    match uu____5733 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          auto_reflect = FStar_Pervasives_Native.None;
          strong_reduction_ok = is_strong;
          requires_binder_substitution = false;
          interpretation = f
        }
     in
  let unary_int_op f =
    unary_op () (fun a406  -> (Obj.magic arg_as_int) a406)
      (fun a407  ->
         fun a408  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5781 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_int r uu____5781)) a407 a408)
     in
  let binary_int_op f =
    binary_op () (fun a409  -> (Obj.magic arg_as_int) a409)
      (fun a410  ->
         fun a411  ->
           fun a412  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5809 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_int r uu____5809)) a410
               a411 a412)
     in
  let unary_bool_op f =
    unary_op () (fun a413  -> (Obj.magic arg_as_bool) a413)
      (fun a414  ->
         fun a415  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5830 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_bool r uu____5830)) a414 a415)
     in
  let binary_bool_op f =
    binary_op () (fun a416  -> (Obj.magic arg_as_bool) a416)
      (fun a417  ->
         fun a418  ->
           fun a419  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5858 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_bool r uu____5858)) a417
               a418 a419)
     in
  let binary_string_op f =
    binary_op () (fun a420  -> (Obj.magic arg_as_string) a420)
      (fun a421  ->
         fun a422  ->
           fun a423  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5886 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_string r uu____5886)) a421
               a422 a423)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5994 =
          let uu____6003 = as_a a  in
          let uu____6006 = as_b b  in (uu____6003, uu____6006)  in
        (match uu____5994 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____6021 =
               let uu____6022 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____6022  in
             FStar_Pervasives_Native.Some uu____6021
         | uu____6023 -> FStar_Pervasives_Native.None)
    | uu____6032 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____6046 =
        let uu____6047 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____6047  in
      mk uu____6046 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____6057 =
      let uu____6060 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____6060  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____6057  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____6092 =
      let uu____6093 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____6093  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____6092
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____6111 = arg_as_string a1  in
        (match uu____6111 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6117 =
               Obj.magic
                 (arg_as_list () (Obj.magic FStar_Syntax_Embeddings.e_string)
                    a2)
                in
             (match uu____6117 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6130 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____6130
              | uu____6131 -> FStar_Pervasives_Native.None)
         | uu____6136 -> FStar_Pervasives_Native.None)
    | uu____6139 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____6149 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____6149
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6178 =
          let uu____6199 = arg_as_string fn  in
          let uu____6202 = arg_as_int from_line  in
          let uu____6205 = arg_as_int from_col  in
          let uu____6208 = arg_as_int to_line  in
          let uu____6211 = arg_as_int to_col  in
          (uu____6199, uu____6202, uu____6205, uu____6208, uu____6211)  in
        (match uu____6178 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6242 =
                 let uu____6243 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6244 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6243 uu____6244  in
               let uu____6245 =
                 let uu____6246 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6247 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6246 uu____6247  in
               FStar_Range.mk_range fn1 uu____6242 uu____6245  in
             let uu____6248 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6248
         | uu____6249 -> FStar_Pervasives_Native.None)
    | uu____6270 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6297)::(a1,uu____6299)::(a2,uu____6301)::[] ->
        let uu____6338 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6338 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6351 -> FStar_Pervasives_Native.None)
    | uu____6352 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____6379)::[] ->
        let uu____6388 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____6388 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6394 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6394
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6395 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6419 =
      let uu____6434 =
        let uu____6449 =
          let uu____6464 =
            let uu____6479 =
              let uu____6494 =
                let uu____6509 =
                  let uu____6524 =
                    let uu____6539 =
                      let uu____6554 =
                        let uu____6569 =
                          let uu____6584 =
                            let uu____6599 =
                              let uu____6614 =
                                let uu____6629 =
                                  let uu____6644 =
                                    let uu____6659 =
                                      let uu____6674 =
                                        let uu____6689 =
                                          let uu____6704 =
                                            let uu____6719 =
                                              let uu____6734 =
                                                let uu____6747 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6747,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a424  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a424)
                                                     (fun a425  ->
                                                        fun a426  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a425 a426)))
                                                 in
                                              let uu____6754 =
                                                let uu____6769 =
                                                  let uu____6782 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6782,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a427  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.e_char)))
                                                            a427)
                                                       (fun a428  ->
                                                          fun a429  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a428 a429)))
                                                   in
                                                let uu____6789 =
                                                  let uu____6804 =
                                                    let uu____6819 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6819,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6828 =
                                                    let uu____6845 =
                                                      let uu____6860 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6860,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____6845]  in
                                                  uu____6804 :: uu____6828
                                                   in
                                                uu____6769 :: uu____6789  in
                                              uu____6734 :: uu____6754  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6719
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6704
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a430  ->
                                                (Obj.magic arg_as_string)
                                                  a430)
                                             (fun a431  ->
                                                fun a432  ->
                                                  fun a433  ->
                                                    (Obj.magic
                                                       string_compare') a431
                                                      a432 a433)))
                                          :: uu____6689
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a434  ->
                                              (Obj.magic arg_as_bool) a434)
                                           (fun a435  ->
                                              fun a436  ->
                                                (Obj.magic string_of_bool1)
                                                  a435 a436)))
                                        :: uu____6674
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a437  ->
                                            (Obj.magic arg_as_int) a437)
                                         (fun a438  ->
                                            fun a439  ->
                                              (Obj.magic string_of_int1) a438
                                                a439)))
                                      :: uu____6659
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a440  ->
                                          (Obj.magic arg_as_int) a440)
                                       (fun a441  ->
                                          (Obj.magic arg_as_char) a441)
                                       (fun a442  ->
                                          fun a443  ->
                                            (Obj.magic
                                               (FStar_Syntax_Embeddings.embed
                                                  FStar_Syntax_Embeddings.e_string))
                                              a442 a443)
                                       (fun a444  ->
                                          fun a445  ->
                                            fun a446  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____7051 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____7051 y)) a444
                                                a445 a446)))
                                    :: uu____6644
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6629
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6614
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6599
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6584
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6569
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6554
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a447  -> (Obj.magic arg_as_int) a447)
                         (fun a448  ->
                            fun a449  ->
                              fun a450  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____7218 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed
                                            FStar_Syntax_Embeddings.e_bool r
                                            uu____7218)) a448 a449 a450)))
                      :: uu____6539
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a451  -> (Obj.magic arg_as_int) a451)
                       (fun a452  ->
                          fun a453  ->
                            fun a454  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____7244 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_bool r
                                          uu____7244)) a452 a453 a454)))
                    :: uu____6524
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a455  -> (Obj.magic arg_as_int) a455)
                     (fun a456  ->
                        fun a457  ->
                          fun a458  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7270 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed
                                        FStar_Syntax_Embeddings.e_bool r
                                        uu____7270)) a456 a457 a458)))
                  :: uu____6509
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a459  -> (Obj.magic arg_as_int) a459)
                   (fun a460  ->
                      fun a461  ->
                        fun a462  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7296 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_bool r
                                      uu____7296)) a460 a461 a462)))
                :: uu____6494
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6479
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6464
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6449
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6434
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6419
     in
  let weak_ops =
    let uu____7435 =
      let uu____7454 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____7454, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____7435]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7538 =
        let uu____7539 =
          let uu____7540 = FStar_Syntax_Syntax.as_arg c  in [uu____7540]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7539  in
      uu____7538 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7590 =
                let uu____7603 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7603, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a463  -> (Obj.magic arg_as_bounded_int) a463)
                     (fun a464  ->
                        fun a465  ->
                          fun a466  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7619  ->
                                    fun uu____7620  ->
                                      match (uu____7619, uu____7620) with
                                      | ((int_to_t1,x),(uu____7639,y)) ->
                                          let uu____7649 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7649)) a464 a465 a466)))
                 in
              let uu____7650 =
                let uu____7665 =
                  let uu____7678 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7678, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a467  -> (Obj.magic arg_as_bounded_int) a467)
                       (fun a468  ->
                          fun a469  ->
                            fun a470  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7694  ->
                                      fun uu____7695  ->
                                        match (uu____7694, uu____7695) with
                                        | ((int_to_t1,x),(uu____7714,y)) ->
                                            let uu____7724 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7724)) a468 a469 a470)))
                   in
                let uu____7725 =
                  let uu____7740 =
                    let uu____7753 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7753, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a471  -> (Obj.magic arg_as_bounded_int) a471)
                         (fun a472  ->
                            fun a473  ->
                              fun a474  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7769  ->
                                        fun uu____7770  ->
                                          match (uu____7769, uu____7770) with
                                          | ((int_to_t1,x),(uu____7789,y)) ->
                                              let uu____7799 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7799)) a472 a473 a474)))
                     in
                  let uu____7800 =
                    let uu____7815 =
                      let uu____7828 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7828, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a475  -> (Obj.magic arg_as_bounded_int) a475)
                           (fun a476  ->
                              fun a477  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7840  ->
                                        match uu____7840 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed
                                              FStar_Syntax_Embeddings.e_int r
                                              x)) a476 a477)))
                       in
                    [uu____7815]  in
                  uu____7740 :: uu____7800  in
                uu____7665 :: uu____7725  in
              uu____7590 :: uu____7650))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7954 =
                let uu____7967 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7967, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a478  -> (Obj.magic arg_as_bounded_int) a478)
                     (fun a479  ->
                        fun a480  ->
                          fun a481  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7983  ->
                                    fun uu____7984  ->
                                      match (uu____7983, uu____7984) with
                                      | ((int_to_t1,x),(uu____8003,y)) ->
                                          let uu____8013 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8013)) a479 a480 a481)))
                 in
              let uu____8014 =
                let uu____8029 =
                  let uu____8042 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____8042, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                       (fun a483  ->
                          fun a484  ->
                            fun a485  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8058  ->
                                      fun uu____8059  ->
                                        match (uu____8058, uu____8059) with
                                        | ((int_to_t1,x),(uu____8078,y)) ->
                                            let uu____8088 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8088)) a483 a484 a485)))
                   in
                [uu____8029]  in
              uu____7954 :: uu____8014))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  let strong_steps =
    FStar_List.map (as_primitive_step true)
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  let weak_steps = FStar_List.map (as_primitive_step false) weak_ops  in
  FStar_All.pipe_left prim_from_list
    (FStar_List.append strong_steps weak_steps)
  
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____8200)::(a1,uu____8202)::(a2,uu____8204)::[] ->
        let uu____8241 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8241 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8247 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8247.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8247.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8251 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8251.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8251.FStar_Syntax_Syntax.vars)
                })
         | uu____8252 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8254)::uu____8255::(a1,uu____8257)::(a2,uu____8259)::[] ->
        let uu____8308 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8308 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8314 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8314.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8314.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8318 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8318.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8318.FStar_Syntax_Syntax.vars)
                })
         | uu____8319 -> FStar_Pervasives_Native.None)
    | uu____8320 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8372 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8372 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8417 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8417) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8477  ->
           fun subst1  ->
             match uu____8477 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8518,uu____8519)) ->
                      let uu____8578 = b  in
                      (match uu____8578 with
                       | (bv,uu____8586) ->
                           let uu____8587 =
                             let uu____8588 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8588  in
                           if uu____8587
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8593 = unembed_binder term1  in
                              match uu____8593 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8600 =
                                      let uu___141_8601 = bv  in
                                      let uu____8602 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___141_8601.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___141_8601.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8602
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8600
                                     in
                                  let b_for_x =
                                    let uu____8606 =
                                      let uu____8613 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8613)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8606  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_8623  ->
                                         match uu___85_8623 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8624,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8626;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8627;_})
                                             ->
                                             let uu____8632 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____8632
                                         | uu____8633 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8634 -> subst1)) env []
  
let reduce_primops :
  'Auu____8651 'Auu____8652 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8651) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8652 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8694 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8694 with
             | (head1,args) ->
                 let uu____8731 =
                   let uu____8732 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8732.FStar_Syntax_Syntax.n  in
                 (match uu____8731 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8736 = find_prim_step cfg fv  in
                      (match uu____8736 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8758  ->
                                   let uu____8759 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8760 =
                                     FStar_Util.string_of_int l  in
                                   let uu____8767 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8759 uu____8760 uu____8767);
                              tm)
                           else
                             (let uu____8769 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____8769 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____8880  ->
                                        let uu____8881 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____8881);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____8884  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____8886 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____8886 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____8892  ->
                                              let uu____8893 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____8893);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____8899  ->
                                              let uu____8900 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____8901 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____8900 uu____8901);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____8902 ->
                           (log_primops cfg
                              (fun uu____8906  ->
                                 let uu____8907 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8907);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8911  ->
                            let uu____8912 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8912);
                       (match args with
                        | (a1,uu____8914)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8931 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8943  ->
                            let uu____8944 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8944);
                       (match args with
                        | (t,uu____8946)::(r,uu____8948)::[] ->
                            let uu____8975 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____8975 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___142_8979 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___142_8979.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___142_8979.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8982 -> tm))
                  | uu____8991 -> tm))
  
let reduce_equality :
  'Auu____8996 'Auu____8997 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8996) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8997 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___143_9035 = cfg  in
         {
           steps =
             (let uu___144_9038 = default_steps  in
              {
                beta = (uu___144_9038.beta);
                iota = (uu___144_9038.iota);
                zeta = (uu___144_9038.zeta);
                weak = (uu___144_9038.weak);
                hnf = (uu___144_9038.hnf);
                primops = true;
                no_delta_steps = (uu___144_9038.no_delta_steps);
                unfold_until = (uu___144_9038.unfold_until);
                unfold_only = (uu___144_9038.unfold_only);
                unfold_fully = (uu___144_9038.unfold_fully);
                unfold_attr = (uu___144_9038.unfold_attr);
                unfold_tac = (uu___144_9038.unfold_tac);
                pure_subterms_within_computations =
                  (uu___144_9038.pure_subterms_within_computations);
                simplify = (uu___144_9038.simplify);
                erase_universes = (uu___144_9038.erase_universes);
                allow_unbound_universes =
                  (uu___144_9038.allow_unbound_universes);
                reify_ = (uu___144_9038.reify_);
                compress_uvars = (uu___144_9038.compress_uvars);
                no_full_norm = (uu___144_9038.no_full_norm);
                check_no_uvars = (uu___144_9038.check_no_uvars);
                unmeta = (uu___144_9038.unmeta);
                unascribe = (uu___144_9038.unascribe)
              });
           tcenv = (uu___143_9035.tcenv);
           debug = (uu___143_9035.debug);
           delta_level = (uu___143_9035.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___143_9035.strong);
           memoize_lazy = (uu___143_9035.memoize_lazy);
           normalize_pure_lets = (uu___143_9035.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____9042 .
    FStar_Syntax_Syntax.term -> 'Auu____9042 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____9055 =
        let uu____9062 =
          let uu____9063 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9063.FStar_Syntax_Syntax.n  in
        (uu____9062, args)  in
      match uu____9055 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9069::uu____9070::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9074::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____9079::uu____9080::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____9083 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_9094  ->
    match uu___86_9094 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____9100 =
          let uu____9103 =
            let uu____9104 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____9104  in
          [uu____9103]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9100
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____9110 =
          let uu____9113 =
            let uu____9114 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldFully uu____9114  in
          [uu____9113]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9110
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____9130 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____9130) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____9172 =
          let uu____9177 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____9177 s  in
        match uu____9172 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____9193 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____9193
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____9210::(tm,uu____9212)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____9241)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____9262)::uu____9263::(tm,uu____9265)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____9302 =
            let uu____9307 = full_norm steps  in parse_steps uu____9307  in
          (match uu____9302 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9346 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_9363  ->
    match uu___87_9363 with
    | (App
        (uu____9366,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____9367;
                      FStar_Syntax_Syntax.vars = uu____9368;_},uu____9369,uu____9370))::uu____9371
        -> true
    | uu____9378 -> false
  
let firstn :
  'Auu____9384 .
    Prims.int ->
      'Auu____9384 Prims.list ->
        ('Auu____9384 Prims.list,'Auu____9384 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify : cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      match stack with
      | (App
          (uu____9420,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____9421;
                        FStar_Syntax_Syntax.vars = uu____9422;_},uu____9423,uu____9424))::uu____9425
          -> (cfg.steps).reify_
      | uu____9432 -> false
  
let rec (norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            if (cfg.debug).norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____9616 ->
                   let uu____9641 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9641
               | uu____9642 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____9650  ->
               let uu____9651 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9652 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9653 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9660 =
                 let uu____9661 =
                   let uu____9664 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9664
                    in
                 stack_to_string uu____9661  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____9651 uu____9652 uu____9653 uu____9660);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____9687 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____9688 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____9689 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9690;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____9691;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9694;
                 FStar_Syntax_Syntax.fv_delta = uu____9695;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9696;
                 FStar_Syntax_Syntax.fv_delta = uu____9697;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9698);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____9705 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____9741 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____9741)
               ->
               let cfg' =
                 let uu___145_9743 = cfg  in
                 {
                   steps =
                     (let uu___146_9746 = cfg.steps  in
                      {
                        beta = (uu___146_9746.beta);
                        iota = (uu___146_9746.iota);
                        zeta = (uu___146_9746.zeta);
                        weak = (uu___146_9746.weak);
                        hnf = (uu___146_9746.hnf);
                        primops = (uu___146_9746.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___146_9746.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___146_9746.unfold_attr);
                        unfold_tac = (uu___146_9746.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___146_9746.pure_subterms_within_computations);
                        simplify = (uu___146_9746.simplify);
                        erase_universes = (uu___146_9746.erase_universes);
                        allow_unbound_universes =
                          (uu___146_9746.allow_unbound_universes);
                        reify_ = (uu___146_9746.reify_);
                        compress_uvars = (uu___146_9746.compress_uvars);
                        no_full_norm = (uu___146_9746.no_full_norm);
                        check_no_uvars = (uu___146_9746.check_no_uvars);
                        unmeta = (uu___146_9746.unmeta);
                        unascribe = (uu___146_9746.unascribe)
                      });
                   tcenv = (uu___145_9743.tcenv);
                   debug = (uu___145_9743.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___145_9743.primitive_steps);
                   strong = (uu___145_9743.strong);
                   memoize_lazy = (uu___145_9743.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____9751 = get_norm_request (norm cfg' env []) args  in
               (match uu____9751 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____9782  ->
                              fun stack1  ->
                                match uu____9782 with
                                | (a,aq) ->
                                    let uu____9794 =
                                      let uu____9795 =
                                        let uu____9802 =
                                          let uu____9803 =
                                            let uu____9834 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____9834, false)  in
                                          Clos uu____9803  in
                                        (uu____9802, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____9795  in
                                    uu____9794 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____9918  ->
                          let uu____9919 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____9919);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____9941 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_9946  ->
                                match uu___88_9946 with
                                | UnfoldUntil uu____9947 -> true
                                | UnfoldOnly uu____9948 -> true
                                | UnfoldFully uu____9951 -> true
                                | uu____9954 -> false))
                         in
                      if uu____9941
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___147_9959 = cfg  in
                      let uu____9960 = to_fsteps s  in
                      {
                        steps = uu____9960;
                        tcenv = (uu___147_9959.tcenv);
                        debug = (uu___147_9959.debug);
                        delta_level;
                        primitive_steps = (uu___147_9959.primitive_steps);
                        strong = (uu___147_9959.strong);
                        memoize_lazy = (uu___147_9959.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____9969 =
                          let uu____9970 =
                            let uu____9975 = FStar_Util.now ()  in
                            (t1, uu____9975)  in
                          Debug uu____9970  in
                        uu____9969 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____9979 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____9979
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____9988 =
                      let uu____9995 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____9995, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____9988  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____10005 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____10005  in
               let uu____10006 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____10006
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____10012  ->
                       let uu____10013 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10014 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____10013 uu____10014);
                  if b
                  then
                    (let uu____10015 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____10015 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____10023 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____10023) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_10029  ->
                               match uu___89_10029 with
                               | FStar_TypeChecker_Env.UnfoldTac  -> false
                               | FStar_TypeChecker_Env.NoDelta  -> false
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | FStar_TypeChecker_Env.Unfold l ->
                                   FStar_TypeChecker_Common.delta_depth_greater_than
                                     fv.FStar_Syntax_Syntax.fv_delta l)))
                     in
                  let should_delta1 =
                    should_delta &&
                      (let attrs =
                         FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                       ((Prims.op_Negation (cfg.steps).unfold_tac) ||
                          (let uu____10039 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____10039))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____10058) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____10093,uu____10094) -> false)))
                     in
                  let uu____10111 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____10127 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____10127 then (true, true) else (false, false)
                     in
                  match uu____10111 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____10140  ->
                            let uu____10141 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____10142 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____10143 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____10141 uu____10142 uu____10143);
                       if should_delta2
                       then
                         (let uu____10144 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___148_10160 = cfg  in
                                 {
                                   steps =
                                     (let uu___149_10163 = cfg.steps  in
                                      {
                                        beta = (uu___149_10163.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        no_delta_steps =
                                          (uu___149_10163.no_delta_steps);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___149_10163.unfold_attr);
                                        unfold_tac =
                                          (uu___149_10163.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___149_10163.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___149_10163.erase_universes);
                                        allow_unbound_universes =
                                          (uu___149_10163.allow_unbound_universes);
                                        reify_ = (uu___149_10163.reify_);
                                        compress_uvars =
                                          (uu___149_10163.compress_uvars);
                                        no_full_norm =
                                          (uu___149_10163.no_full_norm);
                                        check_no_uvars =
                                          (uu___149_10163.check_no_uvars);
                                        unmeta = (uu___149_10163.unmeta);
                                        unascribe =
                                          (uu___149_10163.unascribe)
                                      });
                                   tcenv = (uu___148_10160.tcenv);
                                   debug = (uu___148_10160.debug);
                                   delta_level = (uu___148_10160.delta_level);
                                   primitive_steps =
                                     (uu___148_10160.primitive_steps);
                                   strong = (uu___148_10160.strong);
                                   memoize_lazy =
                                     (uu___148_10160.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___148_10160.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____10144 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10177 = lookup_bvar env x  in
               (match uu____10177 with
                | Univ uu____10180 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____10229 = FStar_ST.op_Bang r  in
                      (match uu____10229 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____10347  ->
                                 let uu____10348 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10349 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10348
                                   uu____10349);
                            (let uu____10350 =
                               let uu____10351 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____10351.FStar_Syntax_Syntax.n  in
                             match uu____10350 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10354 ->
                                 norm cfg env2 stack t'
                             | uu____10371 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10441)::uu____10442 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10451)::uu____10452 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____10462,uu____10463))::stack_rest ->
                    (match c with
                     | Univ uu____10467 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10476 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____10497  ->
                                    let uu____10498 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10498);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____10538  ->
                                    let uu____10539 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10539);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     log cfg
                       (fun uu____10617  ->
                          let uu____10618 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10618);
                     norm cfg env stack1 t1)
                | (Debug uu____10619)::uu____10620 ->
                    if (cfg.steps).weak
                    then
                      let uu____10627 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10627
                    else
                      (let uu____10629 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10629 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10671  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10708 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10708)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_10713 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_10713.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_10713.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10714 -> lopt  in
                           (log cfg
                              (fun uu____10720  ->
                                 let uu____10721 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10721);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_10730 = cfg  in
                               {
                                 steps = (uu___151_10730.steps);
                                 tcenv = (uu___151_10730.tcenv);
                                 debug = (uu___151_10730.debug);
                                 delta_level = (uu___151_10730.delta_level);
                                 primitive_steps =
                                   (uu___151_10730.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_10730.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_10730.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10741)::uu____10742 ->
                    if (cfg.steps).weak
                    then
                      let uu____10749 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10749
                    else
                      (let uu____10751 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10751 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10793  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10830 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10830)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_10835 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_10835.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_10835.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10836 -> lopt  in
                           (log cfg
                              (fun uu____10842  ->
                                 let uu____10843 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10843);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_10852 = cfg  in
                               {
                                 steps = (uu___151_10852.steps);
                                 tcenv = (uu___151_10852.tcenv);
                                 debug = (uu___151_10852.debug);
                                 delta_level = (uu___151_10852.delta_level);
                                 primitive_steps =
                                   (uu___151_10852.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_10852.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_10852.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____10863)::uu____10864 ->
                    if (cfg.steps).weak
                    then
                      let uu____10875 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10875
                    else
                      (let uu____10877 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10877 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10919  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10956 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10956)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_10961 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_10961.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_10961.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10962 -> lopt  in
                           (log cfg
                              (fun uu____10968  ->
                                 let uu____10969 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10969);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_10978 = cfg  in
                               {
                                 steps = (uu___151_10978.steps);
                                 tcenv = (uu___151_10978.tcenv);
                                 debug = (uu___151_10978.debug);
                                 delta_level = (uu___151_10978.delta_level);
                                 primitive_steps =
                                   (uu___151_10978.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_10978.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_10978.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____10989)::uu____10990 ->
                    if (cfg.steps).weak
                    then
                      let uu____11001 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11001
                    else
                      (let uu____11003 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11003 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11045  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11082 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11082)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11087 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11087.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11087.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11088 -> lopt  in
                           (log cfg
                              (fun uu____11094  ->
                                 let uu____11095 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11095);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11104 = cfg  in
                               {
                                 steps = (uu___151_11104.steps);
                                 tcenv = (uu___151_11104.tcenv);
                                 debug = (uu___151_11104.debug);
                                 delta_level = (uu___151_11104.delta_level);
                                 primitive_steps =
                                   (uu___151_11104.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11104.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11104.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11115)::uu____11116 ->
                    if (cfg.steps).weak
                    then
                      let uu____11131 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11131
                    else
                      (let uu____11133 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11133 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11175  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11212 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11212)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11217 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11217.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11217.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11218 -> lopt  in
                           (log cfg
                              (fun uu____11224  ->
                                 let uu____11225 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11225);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11234 = cfg  in
                               {
                                 steps = (uu___151_11234.steps);
                                 tcenv = (uu___151_11234.tcenv);
                                 debug = (uu___151_11234.debug);
                                 delta_level = (uu___151_11234.delta_level);
                                 primitive_steps =
                                   (uu___151_11234.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11234.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11234.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____11245 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11245
                    else
                      (let uu____11247 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11247 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11289  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11326 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11326)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11331 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11331.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11331.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11332 -> lopt  in
                           (log cfg
                              (fun uu____11338  ->
                                 let uu____11339 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11339);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11348 = cfg  in
                               {
                                 steps = (uu___151_11348.steps);
                                 tcenv = (uu___151_11348.tcenv);
                                 debug = (uu___151_11348.debug);
                                 delta_level = (uu___151_11348.delta_level);
                                 primitive_steps =
                                   (uu___151_11348.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11348.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11348.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____11397  ->
                         fun stack1  ->
                           match uu____11397 with
                           | (a,aq) ->
                               let uu____11409 =
                                 let uu____11410 =
                                   let uu____11417 =
                                     let uu____11418 =
                                       let uu____11449 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____11449, false)  in
                                     Clos uu____11418  in
                                   (uu____11417, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____11410  in
                               uu____11409 :: stack1) args)
                  in
               (log cfg
                  (fun uu____11533  ->
                     let uu____11534 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11534);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if (cfg.steps).weak
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                         in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___152_11570 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___152_11570.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___152_11570.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____11571 ->
                      let uu____11576 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11576)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____11579 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____11579 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____11610 =
                          let uu____11611 =
                            let uu____11618 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___153_11620 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___153_11620.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___153_11620.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11618)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____11611  in
                        mk uu____11610 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____11639 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____11639
               else
                 (let uu____11641 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____11641 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____11649 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____11673  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____11649 c1  in
                      let t2 =
                        let uu____11695 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____11695 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____11806)::uu____11807 ->
                    (log cfg
                       (fun uu____11818  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____11819)::uu____11820 ->
                    (log cfg
                       (fun uu____11831  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____11832,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____11833;
                                   FStar_Syntax_Syntax.vars = uu____11834;_},uu____11835,uu____11836))::uu____11837
                    ->
                    (log cfg
                       (fun uu____11846  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____11847)::uu____11848 ->
                    (log cfg
                       (fun uu____11859  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____11860 ->
                    (log cfg
                       (fun uu____11863  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____11867  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____11884 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____11884
                         | FStar_Util.Inr c ->
                             let uu____11892 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____11892
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____11905 =
                               let uu____11906 =
                                 let uu____11933 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11933, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11906
                                in
                             mk uu____11905 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____11952 ->
                           let uu____11953 =
                             let uu____11954 =
                               let uu____11955 =
                                 let uu____11982 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11982, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11955
                                in
                             mk uu____11954 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____11953))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack  in
               norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____12092 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12092 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___154_12112 = cfg  in
                               let uu____12113 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___154_12112.steps);
                                 tcenv = uu____12113;
                                 debug = (uu___154_12112.debug);
                                 delta_level = (uu___154_12112.delta_level);
                                 primitive_steps =
                                   (uu___154_12112.primitive_steps);
                                 strong = (uu___154_12112.strong);
                                 memoize_lazy = (uu___154_12112.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_12112.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____12118 =
                                 let uu____12119 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12119  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12118
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___155_12122 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___155_12122.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___155_12122.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___155_12122.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___155_12122.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12123 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12123
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12134,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12135;
                               FStar_Syntax_Syntax.lbunivs = uu____12136;
                               FStar_Syntax_Syntax.lbtyp = uu____12137;
                               FStar_Syntax_Syntax.lbeff = uu____12138;
                               FStar_Syntax_Syntax.lbdef = uu____12139;
                               FStar_Syntax_Syntax.lbattrs = uu____12140;
                               FStar_Syntax_Syntax.lbpos = uu____12141;_}::uu____12142),uu____12143)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12183 =
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
                            (cfg.steps).pure_subterms_within_computations)))
                  in
               if uu____12183
               then
                 let binder =
                   let uu____12185 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12185  in
                 let env1 =
                   let uu____12195 =
                     let uu____12202 =
                       let uu____12203 =
                         let uu____12234 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12234,
                           false)
                          in
                       Clos uu____12203  in
                     ((FStar_Pervasives_Native.Some binder), uu____12202)  in
                   uu____12195 :: env  in
                 (log cfg
                    (fun uu____12327  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____12331  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12332 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12332))
                 else
                   (let uu____12334 =
                      let uu____12339 =
                        let uu____12340 =
                          let uu____12341 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12341
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12340]  in
                      FStar_Syntax_Subst.open_term uu____12339 body  in
                    match uu____12334 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____12350  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12358 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12358  in
                            FStar_Util.Inl
                              (let uu___156_12368 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___156_12368.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___156_12368.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____12371  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___157_12373 = lb  in
                             let uu____12374 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___157_12373.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___157_12373.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12374;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___157_12373.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___157_12373.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12409  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___158_12432 = cfg  in
                             {
                               steps = (uu___158_12432.steps);
                               tcenv = (uu___158_12432.tcenv);
                               debug = (uu___158_12432.debug);
                               delta_level = (uu___158_12432.delta_level);
                               primitive_steps =
                                 (uu___158_12432.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___158_12432.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___158_12432.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____12435  ->
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
               let uu____12452 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____12452 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____12488 =
                               let uu___159_12489 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___159_12489.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___159_12489.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____12488  in
                           let uu____12490 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____12490 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____12516 =
                                   FStar_List.map (fun uu____12532  -> dummy)
                                     lbs1
                                    in
                                 let uu____12533 =
                                   let uu____12542 =
                                     FStar_List.map
                                       (fun uu____12562  -> dummy) xs1
                                      in
                                   FStar_List.append uu____12542 env  in
                                 FStar_List.append uu____12516 uu____12533
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12586 =
                                       let uu___160_12587 = rc  in
                                       let uu____12588 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___160_12587.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12588;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___160_12587.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____12586
                                 | uu____12595 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___161_12599 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___161_12599.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___161_12599.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___161_12599.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___161_12599.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____12609 =
                        FStar_List.map (fun uu____12625  -> dummy) lbs2  in
                      FStar_List.append uu____12609 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____12633 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____12633 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___162_12649 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___162_12649.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___162_12649.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____12676 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12676
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12695 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____12771  ->
                        match uu____12771 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___163_12892 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___163_12892.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___163_12892.FStar_Syntax_Syntax.sort)
                              }  in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv  in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env  in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____12695 with
                | (rec_env,memos,uu____13105) ->
                    let uu____13158 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos
                       in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____13469 =
                               let uu____13476 =
                                 let uu____13477 =
                                   let uu____13508 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13508, false)
                                    in
                                 Clos uu____13477  in
                               (FStar_Pervasives_Native.None, uu____13476)
                                in
                             uu____13469 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____13618  ->
                     let uu____13619 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13619);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13641 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____13643::uu____13644 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____13649) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____13672 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____13686 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____13686
                              | uu____13697 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____13701 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13727 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13745 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____13762 =
                        let uu____13763 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____13764 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13763 uu____13764
                         in
                      failwith uu____13762
                    else rebuild cfg env stack t2
                | uu____13766 -> norm cfg env stack t2))

and (do_unfold_fv :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun qninfo  ->
            fun f  ->
              let r_env =
                let uu____13776 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____13776  in
              let uu____13777 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____13777 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____13790  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____13801  ->
                        let uu____13802 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____13803 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____13802 uu____13803);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____13808 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____13808 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____13817))::stack1 ->
                          let env1 =
                            FStar_All.pipe_right us'
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun u  ->
                                      (FStar_Pervasives_Native.None,
                                        (Univ u))
                                      :: env1) env)
                             in
                          norm cfg env1 stack1 t1
                      | uu____13872 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____13875 ->
                          let uu____13878 =
                            let uu____13879 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____13879
                             in
                          failwith uu____13878
                    else norm cfg env stack t1))

and (reduce_impure_comp :
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t  in
              let stack1 = (Cfg cfg) :: stack  in
              let cfg1 =
                if (cfg.steps).pure_subterms_within_computations
                then
                  let new_steps =
                    [PureSubtermsWithinComputations;
                    Primops;
                    AllowUnboundUniverses;
                    EraseUniverses;
                    Exclude Zeta;
                    Inlining]  in
                  let uu___164_13903 = cfg  in
                  let uu____13904 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____13904;
                    tcenv = (uu___164_13903.tcenv);
                    debug = (uu___164_13903.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___164_13903.primitive_steps);
                    strong = (uu___164_13903.strong);
                    memoize_lazy = (uu___164_13903.memoize_lazy);
                    normalize_pure_lets =
                      (uu___164_13903.normalize_pure_lets)
                  }
                else
                  (let uu___165_13906 = cfg  in
                   {
                     steps =
                       (let uu___166_13909 = cfg.steps  in
                        {
                          beta = (uu___166_13909.beta);
                          iota = (uu___166_13909.iota);
                          zeta = false;
                          weak = (uu___166_13909.weak);
                          hnf = (uu___166_13909.hnf);
                          primops = (uu___166_13909.primops);
                          no_delta_steps = (uu___166_13909.no_delta_steps);
                          unfold_until = (uu___166_13909.unfold_until);
                          unfold_only = (uu___166_13909.unfold_only);
                          unfold_fully = (uu___166_13909.unfold_fully);
                          unfold_attr = (uu___166_13909.unfold_attr);
                          unfold_tac = (uu___166_13909.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___166_13909.pure_subterms_within_computations);
                          simplify = (uu___166_13909.simplify);
                          erase_universes = (uu___166_13909.erase_universes);
                          allow_unbound_universes =
                            (uu___166_13909.allow_unbound_universes);
                          reify_ = (uu___166_13909.reify_);
                          compress_uvars = (uu___166_13909.compress_uvars);
                          no_full_norm = (uu___166_13909.no_full_norm);
                          check_no_uvars = (uu___166_13909.check_no_uvars);
                          unmeta = (uu___166_13909.unmeta);
                          unascribe = (uu___166_13909.unascribe)
                        });
                     tcenv = (uu___165_13906.tcenv);
                     debug = (uu___165_13906.debug);
                     delta_level = (uu___165_13906.delta_level);
                     primitive_steps = (uu___165_13906.primitive_steps);
                     strong = (uu___165_13906.strong);
                     memoize_lazy = (uu___165_13906.memoize_lazy);
                     normalize_pure_lets =
                       (uu___165_13906.normalize_pure_lets)
                   })
                 in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1)
                 in
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
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                let head0 = head1  in
                let head2 = FStar_Syntax_Util.unascribe head1  in
                log cfg
                  (fun uu____13939  ->
                     let uu____13940 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____13941 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____13940
                       uu____13941);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____13943 =
                   let uu____13944 = FStar_Syntax_Subst.compress head3  in
                   uu____13944.FStar_Syntax_Syntax.n  in
                 match uu____13943 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____13962 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____13962
                        in
                     let uu____13963 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____13963 with
                      | (uu____13964,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____13970 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____13978 =
                                   let uu____13979 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____13979.FStar_Syntax_Syntax.n  in
                                 match uu____13978 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____13985,uu____13986))
                                     ->
                                     let uu____13995 =
                                       let uu____13996 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____13996.FStar_Syntax_Syntax.n  in
                                     (match uu____13995 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____14002,msrc,uu____14004))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____14013 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14013
                                      | uu____14014 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____14015 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____14016 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____14016 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___167_14021 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___167_14021.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___167_14021.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___167_14021.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___167_14021.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___167_14021.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____14022 = FStar_List.tl stack  in
                                    let uu____14023 =
                                      let uu____14024 =
                                        let uu____14027 =
                                          let uu____14028 =
                                            let uu____14041 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____14041)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____14028
                                           in
                                        FStar_Syntax_Syntax.mk uu____14027
                                         in
                                      uu____14024
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____14022 uu____14023
                                | FStar_Pervasives_Native.None  ->
                                    let uu____14057 =
                                      let uu____14058 = is_return body  in
                                      match uu____14058 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____14062;
                                            FStar_Syntax_Syntax.vars =
                                              uu____14063;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____14068 -> false  in
                                    if uu____14057
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head3.FStar_Syntax_Syntax.pos  in
                                       let head4 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify
                                           lb.FStar_Syntax_Syntax.lbdef
                                          in
                                       let body1 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify body
                                          in
                                       let body_rc =
                                         {
                                           FStar_Syntax_Syntax.residual_effect
                                             = m;
                                           FStar_Syntax_Syntax.residual_typ =
                                             (FStar_Pervasives_Native.Some t);
                                           FStar_Syntax_Syntax.residual_flags
                                             = []
                                         }  in
                                       let body2 =
                                         let uu____14091 =
                                           let uu____14094 =
                                             let uu____14095 =
                                               let uu____14112 =
                                                 let uu____14115 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____14115]  in
                                               (uu____14112, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____14095
                                              in
                                           FStar_Syntax_Syntax.mk uu____14094
                                            in
                                         uu____14091
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____14131 =
                                           let uu____14132 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____14132.FStar_Syntax_Syntax.n
                                            in
                                         match uu____14131 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____14138::uu____14139::[])
                                             ->
                                             let uu____14146 =
                                               let uu____14149 =
                                                 let uu____14150 =
                                                   let uu____14157 =
                                                     let uu____14160 =
                                                       let uu____14161 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____14161
                                                        in
                                                     let uu____14162 =
                                                       let uu____14165 =
                                                         let uu____14166 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____14166
                                                          in
                                                       [uu____14165]  in
                                                     uu____14160 ::
                                                       uu____14162
                                                      in
                                                   (bind1, uu____14157)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____14150
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____14149
                                                in
                                             uu____14146
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____14174 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____14180 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____14180
                                         then
                                           let uu____14183 =
                                             let uu____14184 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14184
                                              in
                                           let uu____14185 =
                                             let uu____14188 =
                                               let uu____14189 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____14189
                                                in
                                             [uu____14188]  in
                                           uu____14183 :: uu____14185
                                         else []  in
                                       let reified =
                                         let uu____14194 =
                                           let uu____14197 =
                                             let uu____14198 =
                                               let uu____14213 =
                                                 let uu____14216 =
                                                   let uu____14219 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____14220 =
                                                     let uu____14223 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____14223]  in
                                                   uu____14219 :: uu____14220
                                                    in
                                                 let uu____14224 =
                                                   let uu____14227 =
                                                     let uu____14230 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____14231 =
                                                       let uu____14234 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____14235 =
                                                         let uu____14238 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____14239 =
                                                           let uu____14242 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____14242]  in
                                                         uu____14238 ::
                                                           uu____14239
                                                          in
                                                       uu____14234 ::
                                                         uu____14235
                                                        in
                                                     uu____14230 ::
                                                       uu____14231
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____14227
                                                    in
                                                 FStar_List.append
                                                   uu____14216 uu____14224
                                                  in
                                               (bind_inst, uu____14213)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____14198
                                              in
                                           FStar_Syntax_Syntax.mk uu____14197
                                            in
                                         uu____14194
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____14254  ->
                                            let uu____14255 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____14256 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____14255 uu____14256);
                                       (let uu____14257 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____14257 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____14281 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14281
                        in
                     let uu____14282 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14282 with
                      | (uu____14283,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____14318 =
                                  let uu____14319 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____14319.FStar_Syntax_Syntax.n  in
                                match uu____14318 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____14325) -> t2
                                | uu____14330 -> head4  in
                              let uu____14331 =
                                let uu____14332 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____14332.FStar_Syntax_Syntax.n  in
                              match uu____14331 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____14338 -> FStar_Pervasives_Native.None
                               in
                            let uu____14339 = maybe_extract_fv head4  in
                            match uu____14339 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____14349 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____14349
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____14354 = maybe_extract_fv head5
                                     in
                                  match uu____14354 with
                                  | FStar_Pervasives_Native.Some uu____14359
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____14360 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____14365 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____14380 =
                              match uu____14380 with
                              | (e,q) ->
                                  let uu____14387 =
                                    let uu____14388 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14388.FStar_Syntax_Syntax.n  in
                                  (match uu____14387 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____14403 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____14403
                                   | uu____14404 -> false)
                               in
                            let uu____14405 =
                              let uu____14406 =
                                let uu____14413 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____14413 :: args  in
                              FStar_Util.for_some is_arg_impure uu____14406
                               in
                            if uu____14405
                            then
                              let uu____14418 =
                                let uu____14419 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____14419
                                 in
                              failwith uu____14418
                            else ());
                           (let uu____14421 = maybe_unfold_action head_app
                               in
                            match uu____14421 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head3.FStar_Syntax_Syntax.pos
                                   in
                                let body =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head_app1, args))
                                   in
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
                                      body
                                   in
                                (log cfg
                                   (fun uu____14462  ->
                                      let uu____14463 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____14464 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____14463 uu____14464);
                                 (let uu____14465 = FStar_List.tl stack  in
                                  norm cfg env uu____14465 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____14467) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____14491 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____14491  in
                     (log cfg
                        (fun uu____14495  ->
                           let uu____14496 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____14496);
                      (let uu____14497 = FStar_List.tl stack  in
                       norm cfg env uu____14497 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____14618  ->
                               match uu____14618 with
                               | (pat,wopt,tm) ->
                                   let uu____14666 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____14666)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____14698 = FStar_List.tl stack  in
                     norm cfg env uu____14698 tm
                 | uu____14699 -> fallback ())

and (reify_lift :
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.tcenv  in
            log cfg
              (fun uu____14713  ->
                 let uu____14714 = FStar_Ident.string_of_lid msrc  in
                 let uu____14715 = FStar_Ident.string_of_lid mtgt  in
                 let uu____14716 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14714
                   uu____14715 uu____14716);
            (let uu____14717 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____14717
             then
               let ed =
                 let uu____14719 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____14719  in
               let uu____14720 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____14720 with
               | (uu____14721,return_repr) ->
                   let return_inst =
                     let uu____14730 =
                       let uu____14731 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____14731.FStar_Syntax_Syntax.n  in
                     match uu____14730 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____14737::[]) ->
                         let uu____14744 =
                           let uu____14747 =
                             let uu____14748 =
                               let uu____14755 =
                                 let uu____14758 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____14758]  in
                               (return_tm, uu____14755)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____14748  in
                           FStar_Syntax_Syntax.mk uu____14747  in
                         uu____14744 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14766 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____14769 =
                     let uu____14772 =
                       let uu____14773 =
                         let uu____14788 =
                           let uu____14791 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14792 =
                             let uu____14795 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14795]  in
                           uu____14791 :: uu____14792  in
                         (return_inst, uu____14788)  in
                       FStar_Syntax_Syntax.Tm_app uu____14773  in
                     FStar_Syntax_Syntax.mk uu____14772  in
                   uu____14769 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14804 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14804 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14807 =
                      let uu____14808 = FStar_Ident.text_of_lid msrc  in
                      let uu____14809 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14808 uu____14809
                       in
                    failwith uu____14807
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14810;
                      FStar_TypeChecker_Env.mtarget = uu____14811;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14812;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____14827 =
                      let uu____14828 = FStar_Ident.text_of_lid msrc  in
                      let uu____14829 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14828 uu____14829
                       in
                    failwith uu____14827
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14830;
                      FStar_TypeChecker_Env.mtarget = uu____14831;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14832;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14856 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____14857 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____14856 t FStar_Syntax_Syntax.tun uu____14857))

and (norm_pattern_args :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____14913  ->
                   match uu____14913 with
                   | (a,imp) ->
                       let uu____14924 = norm cfg env [] a  in
                       (uu____14924, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____14932  ->
             let uu____14933 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____14934 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____14933 uu____14934);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14958 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____14958
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___168_14961 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___168_14961.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___168_14961.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14981 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____14981
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___169_14984 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___169_14984.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___169_14984.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____15017  ->
                      match uu____15017 with
                      | (a,i) ->
                          let uu____15028 = norm cfg env [] a  in
                          (uu____15028, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_15046  ->
                       match uu___90_15046 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____15050 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____15050
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___170_15058 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___171_15061 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___171_15061.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___170_15058.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___170_15058.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____15064  ->
        match uu____15064 with
        | (x,imp) ->
            let uu____15067 =
              let uu___172_15068 = x  in
              let uu____15069 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___172_15068.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___172_15068.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15069
              }  in
            (uu____15067, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15075 =
          FStar_List.fold_left
            (fun uu____15093  ->
               fun b  ->
                 match uu____15093 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____15075 with | (nbs,uu____15133) -> FStar_List.rev nbs

and (norm_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____15149 =
              let uu___173_15150 = rc  in
              let uu____15151 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___173_15150.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15151;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___173_15150.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____15149
        | uu____15158 -> lopt

and (maybe_simplify :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____15179 = FStar_Syntax_Print.term_to_string tm  in
             let uu____15180 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____15179
               uu____15180)
          else ();
          tm'

and (maybe_simplify_aux :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____15200 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____15200
          then tm1
          else
            (let w t =
               let uu___174_15212 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___174_15212.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___174_15212.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____15221 =
                 let uu____15222 = FStar_Syntax_Util.unmeta t  in
                 uu____15222.FStar_Syntax_Syntax.n  in
               match uu____15221 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____15229 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____15274)::args1,(bv,uu____15277)::bs1) ->
                   let uu____15311 =
                     let uu____15312 = FStar_Syntax_Subst.compress t  in
                     uu____15312.FStar_Syntax_Syntax.n  in
                   (match uu____15311 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____15316 -> false)
               | ([],[]) -> true
               | (uu____15337,uu____15338) -> false  in
             let is_applied bs t =
               let uu____15374 = FStar_Syntax_Util.head_and_args' t  in
               match uu____15374 with
               | (hd1,args) ->
                   let uu____15407 =
                     let uu____15408 = FStar_Syntax_Subst.compress hd1  in
                     uu____15408.FStar_Syntax_Syntax.n  in
                   (match uu____15407 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____15414 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____15426 = FStar_Syntax_Util.is_squash t  in
               match uu____15426 with
               | FStar_Pervasives_Native.Some (uu____15437,t') ->
                   is_applied bs t'
               | uu____15449 ->
                   let uu____15458 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____15458 with
                    | FStar_Pervasives_Native.Some (uu____15469,t') ->
                        is_applied bs t'
                    | uu____15481 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____15498 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15498 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15505)::(q,uu____15507)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____15542 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____15542 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____15547 =
                          let uu____15548 = FStar_Syntax_Subst.compress p  in
                          uu____15548.FStar_Syntax_Syntax.n  in
                        (match uu____15547 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15554 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____15554
                         | uu____15555 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____15558)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____15583 =
                          let uu____15584 = FStar_Syntax_Subst.compress p1
                             in
                          uu____15584.FStar_Syntax_Syntax.n  in
                        (match uu____15583 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15590 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____15590
                         | uu____15591 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____15595 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____15595 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____15600 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____15600 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15607 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15607
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____15610)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____15635 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____15635 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15642 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15642
                              | uu____15643 -> FStar_Pervasives_Native.None)
                         | uu____15646 -> FStar_Pervasives_Native.None)
                    | uu____15649 -> FStar_Pervasives_Native.None)
               | uu____15652 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15663 =
                 let uu____15664 = FStar_Syntax_Subst.compress phi  in
                 uu____15664.FStar_Syntax_Syntax.n  in
               match uu____15663 with
               | FStar_Syntax_Syntax.Tm_match (uu____15669,br::brs) ->
                   let uu____15736 = br  in
                   (match uu____15736 with
                    | (uu____15753,uu____15754,e) ->
                        let r =
                          let uu____15775 = simp_t e  in
                          match uu____15775 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15781 =
                                FStar_List.for_all
                                  (fun uu____15799  ->
                                     match uu____15799 with
                                     | (uu____15812,uu____15813,e') ->
                                         let uu____15827 = simp_t e'  in
                                         uu____15827 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15781
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15835 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15840 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15840
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15861 =
                 match uu____15861 with
                 | (t1,q) ->
                     let uu____15874 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15874 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15902 -> (t1, q))
                  in
               let uu____15911 = FStar_Syntax_Util.head_and_args t  in
               match uu____15911 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15973 =
                 let uu____15974 = FStar_Syntax_Util.unmeta ty  in
                 uu____15974.FStar_Syntax_Syntax.n  in
               match uu____15973 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15978) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15983,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____16003 -> false  in
             let simplify1 arg =
               let uu____16026 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____16026, arg)  in
             let uu____16035 = is_quantified_const tm1  in
             match uu____16035 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____16039 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____16039
             | FStar_Pervasives_Native.None  ->
                 let uu____16040 =
                   let uu____16041 = FStar_Syntax_Subst.compress tm1  in
                   uu____16041.FStar_Syntax_Syntax.n  in
                 (match uu____16040 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____16045;
                              FStar_Syntax_Syntax.vars = uu____16046;_},uu____16047);
                         FStar_Syntax_Syntax.pos = uu____16048;
                         FStar_Syntax_Syntax.vars = uu____16049;_},args)
                      ->
                      let uu____16075 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____16075
                      then
                        let uu____16076 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____16076 with
                         | (FStar_Pervasives_Native.Some (true ),uu____16123)::
                             (uu____16124,(arg,uu____16126))::[] ->
                             maybe_auto_squash arg
                         | (uu____16175,(arg,uu____16177))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____16178)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____16227)::uu____16228::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16279::(FStar_Pervasives_Native.Some (false
                                         ),uu____16280)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16331 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16345 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16345
                         then
                           let uu____16346 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16346 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16393)::uu____16394::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16445::(FStar_Pervasives_Native.Some (true
                                           ),uu____16446)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16497)::(uu____16498,(arg,uu____16500))::[]
                               -> maybe_auto_squash arg
                           | (uu____16549,(arg,uu____16551))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16552)::[]
                               -> maybe_auto_squash arg
                           | uu____16601 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16615 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16615
                            then
                              let uu____16616 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16616 with
                              | uu____16663::(FStar_Pervasives_Native.Some
                                              (true ),uu____16664)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16715)::uu____16716::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16767)::(uu____16768,(arg,uu____16770))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16819,(p,uu____16821))::(uu____16822,
                                                                (q,uu____16824))::[]
                                  ->
                                  let uu____16871 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16871
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16873 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16887 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16887
                               then
                                 let uu____16888 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16888 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16935)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16936)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16987)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16988)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17039)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17040)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17091)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17092)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17143,(arg,uu____17145))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17146)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17195)::(uu____17196,(arg,uu____17198))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17247,(arg,uu____17249))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17250)::[]
                                     ->
                                     let uu____17299 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17299
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17300)::(uu____17301,(arg,uu____17303))::[]
                                     ->
                                     let uu____17352 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17352
                                 | (uu____17353,(p,uu____17355))::(uu____17356,
                                                                   (q,uu____17358))::[]
                                     ->
                                     let uu____17405 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17405
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17407 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17421 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17421
                                  then
                                    let uu____17422 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17422 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17469)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17500)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17531 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17545 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17545
                                     then
                                       match args with
                                       | (t,uu____17547)::[] ->
                                           let uu____17564 =
                                             let uu____17565 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17565.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17564 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17568::[],body,uu____17570)
                                                ->
                                                let uu____17597 = simp_t body
                                                   in
                                                (match uu____17597 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17600 -> tm1)
                                            | uu____17603 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17605))::(t,uu____17607)::[]
                                           ->
                                           let uu____17646 =
                                             let uu____17647 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17647.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17646 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17650::[],body,uu____17652)
                                                ->
                                                let uu____17679 = simp_t body
                                                   in
                                                (match uu____17679 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17682 -> tm1)
                                            | uu____17685 -> tm1)
                                       | uu____17686 -> tm1
                                     else
                                       (let uu____17696 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17696
                                        then
                                          match args with
                                          | (t,uu____17698)::[] ->
                                              let uu____17715 =
                                                let uu____17716 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17716.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17715 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17719::[],body,uu____17721)
                                                   ->
                                                   let uu____17748 =
                                                     simp_t body  in
                                                   (match uu____17748 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17751 -> tm1)
                                               | uu____17754 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17756))::(t,uu____17758)::[]
                                              ->
                                              let uu____17797 =
                                                let uu____17798 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17798.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17797 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17801::[],body,uu____17803)
                                                   ->
                                                   let uu____17830 =
                                                     simp_t body  in
                                                   (match uu____17830 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____17833 -> tm1)
                                               | uu____17836 -> tm1)
                                          | uu____17837 -> tm1
                                        else
                                          (let uu____17847 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____17847
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17848;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17849;_},uu____17850)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17867;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17868;_},uu____17869)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____17886 -> tm1
                                           else
                                             (let uu____17896 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____17896 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____17916 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____17926;
                         FStar_Syntax_Syntax.vars = uu____17927;_},args)
                      ->
                      let uu____17949 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17949
                      then
                        let uu____17950 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17950 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17997)::
                             (uu____17998,(arg,uu____18000))::[] ->
                             maybe_auto_squash arg
                         | (uu____18049,(arg,uu____18051))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18052)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18101)::uu____18102::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18153::(FStar_Pervasives_Native.Some (false
                                         ),uu____18154)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18205 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18219 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18219
                         then
                           let uu____18220 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18220 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18267)::uu____18268::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18319::(FStar_Pervasives_Native.Some (true
                                           ),uu____18320)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18371)::(uu____18372,(arg,uu____18374))::[]
                               -> maybe_auto_squash arg
                           | (uu____18423,(arg,uu____18425))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18426)::[]
                               -> maybe_auto_squash arg
                           | uu____18475 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18489 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18489
                            then
                              let uu____18490 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18490 with
                              | uu____18537::(FStar_Pervasives_Native.Some
                                              (true ),uu____18538)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18589)::uu____18590::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18641)::(uu____18642,(arg,uu____18644))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18693,(p,uu____18695))::(uu____18696,
                                                                (q,uu____18698))::[]
                                  ->
                                  let uu____18745 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18745
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18747 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18761 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18761
                               then
                                 let uu____18762 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18762 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18809)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18810)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18861)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18862)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18913)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18914)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18965)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18966)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19017,(arg,uu____19019))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19020)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19069)::(uu____19070,(arg,uu____19072))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19121,(arg,uu____19123))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19124)::[]
                                     ->
                                     let uu____19173 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19173
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19174)::(uu____19175,(arg,uu____19177))::[]
                                     ->
                                     let uu____19226 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19226
                                 | (uu____19227,(p,uu____19229))::(uu____19230,
                                                                   (q,uu____19232))::[]
                                     ->
                                     let uu____19279 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19279
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19281 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19295 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19295
                                  then
                                    let uu____19296 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19296 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19343)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19374)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19405 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19419 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19419
                                     then
                                       match args with
                                       | (t,uu____19421)::[] ->
                                           let uu____19438 =
                                             let uu____19439 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19439.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19438 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19442::[],body,uu____19444)
                                                ->
                                                let uu____19471 = simp_t body
                                                   in
                                                (match uu____19471 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19474 -> tm1)
                                            | uu____19477 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19479))::(t,uu____19481)::[]
                                           ->
                                           let uu____19520 =
                                             let uu____19521 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19521.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19520 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19524::[],body,uu____19526)
                                                ->
                                                let uu____19553 = simp_t body
                                                   in
                                                (match uu____19553 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19556 -> tm1)
                                            | uu____19559 -> tm1)
                                       | uu____19560 -> tm1
                                     else
                                       (let uu____19570 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19570
                                        then
                                          match args with
                                          | (t,uu____19572)::[] ->
                                              let uu____19589 =
                                                let uu____19590 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19590.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19589 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19593::[],body,uu____19595)
                                                   ->
                                                   let uu____19622 =
                                                     simp_t body  in
                                                   (match uu____19622 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19625 -> tm1)
                                               | uu____19628 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19630))::(t,uu____19632)::[]
                                              ->
                                              let uu____19671 =
                                                let uu____19672 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19672.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19671 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19675::[],body,uu____19677)
                                                   ->
                                                   let uu____19704 =
                                                     simp_t body  in
                                                   (match uu____19704 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____19707 -> tm1)
                                               | uu____19710 -> tm1)
                                          | uu____19711 -> tm1
                                        else
                                          (let uu____19721 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19721
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19722;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19723;_},uu____19724)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19741;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19742;_},uu____19743)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19760 -> tm1
                                           else
                                             (let uu____19770 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____19770 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19790 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____19805 = simp_t t  in
                      (match uu____19805 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____19808 ->
                      let uu____19831 = is_const_match tm1  in
                      (match uu____19831 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____19834 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____19845  ->
               let uu____19846 = FStar_Syntax_Print.tag_of_term t  in
               let uu____19847 = FStar_Syntax_Print.term_to_string t  in
               let uu____19848 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____19855 =
                 let uu____19856 =
                   let uu____19859 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____19859
                    in
                 stack_to_string uu____19856  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____19846 uu____19847 uu____19848 uu____19855);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____19890 =
                     let uu____19891 =
                       let uu____19892 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____19892  in
                     FStar_Util.string_of_int uu____19891  in
                   let uu____19897 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____19898 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____19890 uu____19897 uu____19898)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____19952  ->
                     let uu____19953 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____19953);
                rebuild cfg env stack1 t1)
           | (Let (env',bs,lb,r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t1  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env' stack1 t2
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let bs1 = norm_binders cfg env' bs  in
               let lopt1 = norm_lcomp_opt cfg env'' lopt  in
               let uu____19989 =
                 let uu___175_19990 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___175_19990.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___175_19990.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19989
           | (Arg (Univ uu____19991,uu____19992,uu____19993))::uu____19994 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19997,uu____19998))::uu____19999 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20014,uu____20015),aq,r))::stack1
               when
               let uu____20065 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20065 ->
               let t2 =
                 let uu____20069 =
                   let uu____20070 =
                     let uu____20071 = closure_as_term cfg env_arg tm  in
                     (uu____20071, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20070  in
                 uu____20069 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20077),aq,r))::stack1 ->
               (log cfg
                  (fun uu____20130  ->
                     let uu____20131 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20131);
                if Prims.op_Negation (cfg.steps).iota
                then
                  (if (cfg.steps).hnf
                   then
                     let arg = closure_as_term cfg env_arg tm  in
                     let t2 =
                       FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env_arg stack1 t2
                   else
                     (let stack2 = (App (env, t1, aq, r)) :: stack1  in
                      norm cfg env_arg stack2 tm))
                else
                  (let uu____20141 = FStar_ST.op_Bang m  in
                   match uu____20141 with
                   | FStar_Pervasives_Native.None  ->
                       if (cfg.steps).hnf
                       then
                         let arg = closure_as_term cfg env_arg tm  in
                         let t2 =
                           FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                             FStar_Pervasives_Native.None r
                            in
                         rebuild cfg env_arg stack1 t2
                       else
                         (let stack2 = (MemoLazy m) :: (App (env, t1, aq, r))
                            :: stack1  in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____20278,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____20325 =
                 log cfg
                   (fun uu____20329  ->
                      let uu____20330 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____20330);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____20334 =
                 let uu____20335 = FStar_Syntax_Subst.compress t1  in
                 uu____20335.FStar_Syntax_Syntax.n  in
               (match uu____20334 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____20362 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____20362  in
                    (log cfg
                       (fun uu____20366  ->
                          let uu____20367 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____20367);
                     (let uu____20368 = FStar_List.tl stack  in
                      norm cfg env1 uu____20368 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____20369);
                       FStar_Syntax_Syntax.pos = uu____20370;
                       FStar_Syntax_Syntax.vars = uu____20371;_},(e,uu____20373)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____20402 when
                    (cfg.steps).primops ->
                    let uu____20417 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____20417 with
                     | (hd1,args) ->
                         let uu____20454 =
                           let uu____20455 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____20455.FStar_Syntax_Syntax.n  in
                         (match uu____20454 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____20459 = find_prim_step cfg fv  in
                              (match uu____20459 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____20462; arity = uu____20463;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____20465;
                                     requires_binder_substitution =
                                       uu____20466;
                                     interpretation = uu____20467;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____20480 -> fallback " (3)" ())
                          | uu____20483 -> fallback " (4)" ()))
                | uu____20484 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____20504  ->
                     let uu____20505 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____20505);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____20510 =
                   log cfg
                     (fun uu____20515  ->
                        let uu____20516 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____20517 =
                          let uu____20518 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____20535  ->
                                    match uu____20535 with
                                    | (p,uu____20545,uu____20546) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____20518
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____20516 uu____20517);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___91_20563  ->
                                match uu___91_20563 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____20564 -> false))
                         in
                      let uu___176_20565 = cfg  in
                      {
                        steps =
                          (let uu___177_20568 = cfg.steps  in
                           {
                             beta = (uu___177_20568.beta);
                             iota = (uu___177_20568.iota);
                             zeta = false;
                             weak = (uu___177_20568.weak);
                             hnf = (uu___177_20568.hnf);
                             primops = (uu___177_20568.primops);
                             no_delta_steps = (uu___177_20568.no_delta_steps);
                             unfold_until = (uu___177_20568.unfold_until);
                             unfold_only = (uu___177_20568.unfold_only);
                             unfold_fully = (uu___177_20568.unfold_fully);
                             unfold_attr = (uu___177_20568.unfold_attr);
                             unfold_tac = (uu___177_20568.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___177_20568.pure_subterms_within_computations);
                             simplify = (uu___177_20568.simplify);
                             erase_universes =
                               (uu___177_20568.erase_universes);
                             allow_unbound_universes =
                               (uu___177_20568.allow_unbound_universes);
                             reify_ = (uu___177_20568.reify_);
                             compress_uvars = (uu___177_20568.compress_uvars);
                             no_full_norm = (uu___177_20568.no_full_norm);
                             check_no_uvars = (uu___177_20568.check_no_uvars);
                             unmeta = (uu___177_20568.unmeta);
                             unascribe = (uu___177_20568.unascribe)
                           });
                        tcenv = (uu___176_20565.tcenv);
                        debug = (uu___176_20565.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___176_20565.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___176_20565.memoize_lazy);
                        normalize_pure_lets =
                          (uu___176_20565.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____20600 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____20621 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20681  ->
                                    fun uu____20682  ->
                                      match (uu____20681, uu____20682) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____20773 = norm_pat env3 p1
                                             in
                                          (match uu____20773 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____20621 with
                           | (pats1,env3) ->
                               ((let uu___178_20855 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___178_20855.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___179_20874 = x  in
                            let uu____20875 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___179_20874.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___179_20874.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20875
                            }  in
                          ((let uu___180_20889 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___180_20889.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___181_20900 = x  in
                            let uu____20901 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_20900.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_20900.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20901
                            }  in
                          ((let uu___182_20915 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___182_20915.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___183_20931 = x  in
                            let uu____20932 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___183_20931.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___183_20931.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20932
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___184_20939 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___184_20939.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20949 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20963 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20963 with
                                  | (p,wopt,e) ->
                                      let uu____20983 = norm_pat env1 p  in
                                      (match uu____20983 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____21008 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____21008
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____21014 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____21014)
                    in
                 let rec is_cons head1 =
                   let uu____21019 =
                     let uu____21020 = FStar_Syntax_Subst.compress head1  in
                     uu____21020.FStar_Syntax_Syntax.n  in
                   match uu____21019 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____21024) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____21029 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21030;
                         FStar_Syntax_Syntax.fv_delta = uu____21031;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21032;
                         FStar_Syntax_Syntax.fv_delta = uu____21033;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____21034);_}
                       -> true
                   | uu____21041 -> false  in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b  in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r
                          in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch
                    in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig
                      in
                   let uu____21186 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____21186 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____21273 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____21312 ->
                                 let uu____21313 =
                                   let uu____21314 = is_cons head1  in
                                   Prims.op_Negation uu____21314  in
                                 FStar_Util.Inr uu____21313)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____21339 =
                              let uu____21340 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____21340.FStar_Syntax_Syntax.n  in
                            (match uu____21339 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____21358 ->
                                 let uu____21359 =
                                   let uu____21360 = is_cons head1  in
                                   Prims.op_Negation uu____21360  in
                                 FStar_Util.Inr uu____21359))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____21429)::rest_a,(p1,uu____21432)::rest_p) ->
                       let uu____21476 = matches_pat t2 p1  in
                       (match uu____21476 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____21525 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21631 = matches_pat scrutinee1 p1  in
                       (match uu____21631 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____21671  ->
                                  let uu____21672 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21673 =
                                    let uu____21674 =
                                      FStar_List.map
                                        (fun uu____21684  ->
                                           match uu____21684 with
                                           | (uu____21689,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21674
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21672 uu____21673);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21720  ->
                                       match uu____21720 with
                                       | (bv,t2) ->
                                           let uu____21743 =
                                             let uu____21750 =
                                               let uu____21753 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21753
                                                in
                                             let uu____21754 =
                                               let uu____21755 =
                                                 let uu____21786 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21786, false)
                                                  in
                                               Clos uu____21755  in
                                             (uu____21750, uu____21754)  in
                                           uu____21743 :: env2) env1 s
                                 in
                              let uu____21903 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____21903)))
                    in
                 if (cfg.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

let (plugins :
  (primitive_step -> Prims.unit,Prims.unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____21926 =
      let uu____21929 = FStar_ST.op_Bang plugins  in p :: uu____21929  in
    FStar_ST.op_Colon_Equals plugins uu____21926  in
  let retrieve uu____22027 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____22092  -> FStar_Pervasives_Native.snd plugins () 
let (config' :
  primitive_step Prims.list ->
    step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  =
  fun psteps  ->
    fun s  ->
      fun e  ->
        let d =
          FStar_All.pipe_right s
            (FStar_List.collect
               (fun uu___92_22125  ->
                  match uu___92_22125 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____22129 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____22135 -> d  in
        let uu____22138 = to_fsteps s  in
        let uu____22139 =
          let uu____22140 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____22141 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____22142 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____22143 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____22144 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____22140;
            primop = uu____22141;
            b380 = uu____22142;
            norm_delayed = uu____22143;
            print_normalized = uu____22144
          }  in
        let uu____22145 =
          let uu____22148 =
            let uu____22151 = retrieve_plugins ()  in
            FStar_List.append uu____22151 psteps  in
          add_steps built_in_primitive_steps uu____22148  in
        let uu____22154 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____22156 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____22156)
           in
        {
          steps = uu____22138;
          tcenv = e;
          debug = uu____22139;
          delta_level = d1;
          primitive_steps = uu____22145;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____22154
        }
  
let (config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg) =
  fun s  -> fun e  -> config' [] s e 
let (normalize_with_primitive_steps :
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps  ->
    fun s  -> fun e  -> fun t  -> let c = config' ps s e  in norm c [] [] t
  
let (normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t 
let (normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____22214 = config s e  in norm_comp uu____22214 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____22227 = config [] env  in norm_universe uu____22227 [] u
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env
         in
      let non_info t =
        let uu____22245 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22245  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____22252 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___185_22271 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___185_22271.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___185_22271.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____22278 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____22278
          then
            let ct1 =
              let uu____22280 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____22280 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____22287 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____22287
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___186_22291 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___186_22291.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___186_22291.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___186_22291.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___187_22293 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___187_22293.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___187_22293.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___187_22293.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___187_22293.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___188_22294 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___188_22294.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___188_22294.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____22296 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env
         in
      let non_info t =
        let uu____22308 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22308  in
      let uu____22315 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____22315
      then
        let uu____22316 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____22316 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____22322  ->
                 let uu____22323 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____22323)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____22340 =
                let uu____22345 =
                  let uu____22346 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22346
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22345)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____22340);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____22357 = config [AllowUnboundUniverses] env  in
          norm_comp uu____22357 [] c
        with
        | e ->
            ((let uu____22370 =
                let uu____22375 =
                  let uu____22376 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22376
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22375)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____22370);
             c)
         in
      FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1
  
let (normalize_refinement :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0  in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1  in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort  in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____22413 =
                     let uu____22414 =
                       let uu____22421 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____22421)  in
                     FStar_Syntax_Syntax.Tm_refine uu____22414  in
                   mk uu____22413 t01.FStar_Syntax_Syntax.pos
               | uu____22426 -> t2)
          | uu____22427 -> t2  in
        aux t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
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
  
let (reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t 
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t 
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____22467 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____22467 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____22496 ->
                 let uu____22503 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____22503 with
                  | (actuals,uu____22513,uu____22514) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____22528 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____22528 with
                         | (binders,args) ->
                             let uu____22545 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____22545
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____22553 ->
          let uu____22554 = FStar_Syntax_Util.head_and_args t  in
          (match uu____22554 with
           | (head1,args) ->
               let uu____22591 =
                 let uu____22592 = FStar_Syntax_Subst.compress head1  in
                 uu____22592.FStar_Syntax_Syntax.n  in
               (match uu____22591 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____22595,thead) ->
                    let uu____22621 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____22621 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____22663 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___193_22671 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___193_22671.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___193_22671.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___193_22671.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___193_22671.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___193_22671.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___193_22671.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___193_22671.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___193_22671.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___193_22671.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___193_22671.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___193_22671.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___193_22671.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___193_22671.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___193_22671.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___193_22671.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___193_22671.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___193_22671.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___193_22671.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___193_22671.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___193_22671.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___193_22671.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___193_22671.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___193_22671.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___193_22671.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___193_22671.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___193_22671.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___193_22671.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___193_22671.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___193_22671.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___193_22671.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___193_22671.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___193_22671.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___193_22671.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____22663 with
                            | (uu____22672,ty,uu____22674) ->
                                eta_expand_with_type env t ty))
                | uu____22675 ->
                    let uu____22676 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___194_22684 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___194_22684.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___194_22684.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___194_22684.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___194_22684.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___194_22684.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___194_22684.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___194_22684.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___194_22684.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___194_22684.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___194_22684.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___194_22684.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___194_22684.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___194_22684.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___194_22684.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___194_22684.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___194_22684.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___194_22684.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___194_22684.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___194_22684.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___194_22684.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___194_22684.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___194_22684.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___194_22684.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___194_22684.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___194_22684.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___194_22684.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___194_22684.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___194_22684.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___194_22684.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___194_22684.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___194_22684.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___194_22684.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___194_22684.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____22676 with
                     | (uu____22685,ty,uu____22687) ->
                         eta_expand_with_type env t ty)))
  
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
       in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___195_22744 = x  in
      let uu____22745 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___195_22744.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___195_22744.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____22745
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____22748 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____22773 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____22774 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____22775 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____22776 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____22783 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____22784 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____22785 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___196_22813 = rc  in
          let uu____22814 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____22821 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___196_22813.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____22814;
            FStar_Syntax_Syntax.residual_flags = uu____22821
          }  in
        let uu____22824 =
          let uu____22825 =
            let uu____22842 = elim_delayed_subst_binders bs  in
            let uu____22849 = elim_delayed_subst_term t2  in
            let uu____22850 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____22842, uu____22849, uu____22850)  in
          FStar_Syntax_Syntax.Tm_abs uu____22825  in
        mk1 uu____22824
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____22879 =
          let uu____22880 =
            let uu____22893 = elim_delayed_subst_binders bs  in
            let uu____22900 = elim_delayed_subst_comp c  in
            (uu____22893, uu____22900)  in
          FStar_Syntax_Syntax.Tm_arrow uu____22880  in
        mk1 uu____22879
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____22913 =
          let uu____22914 =
            let uu____22921 = elim_bv bv  in
            let uu____22922 = elim_delayed_subst_term phi  in
            (uu____22921, uu____22922)  in
          FStar_Syntax_Syntax.Tm_refine uu____22914  in
        mk1 uu____22913
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____22945 =
          let uu____22946 =
            let uu____22961 = elim_delayed_subst_term t2  in
            let uu____22962 = elim_delayed_subst_args args  in
            (uu____22961, uu____22962)  in
          FStar_Syntax_Syntax.Tm_app uu____22946  in
        mk1 uu____22945
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___197_23026 = p  in
              let uu____23027 =
                let uu____23028 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____23028  in
              {
                FStar_Syntax_Syntax.v = uu____23027;
                FStar_Syntax_Syntax.p =
                  (uu___197_23026.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___198_23030 = p  in
              let uu____23031 =
                let uu____23032 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____23032  in
              {
                FStar_Syntax_Syntax.v = uu____23031;
                FStar_Syntax_Syntax.p =
                  (uu___198_23030.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___199_23039 = p  in
              let uu____23040 =
                let uu____23041 =
                  let uu____23048 = elim_bv x  in
                  let uu____23049 = elim_delayed_subst_term t0  in
                  (uu____23048, uu____23049)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____23041  in
              {
                FStar_Syntax_Syntax.v = uu____23040;
                FStar_Syntax_Syntax.p =
                  (uu___199_23039.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___200_23068 = p  in
              let uu____23069 =
                let uu____23070 =
                  let uu____23083 =
                    FStar_List.map
                      (fun uu____23106  ->
                         match uu____23106 with
                         | (x,b) ->
                             let uu____23119 = elim_pat x  in
                             (uu____23119, b)) pats
                     in
                  (fv, uu____23083)  in
                FStar_Syntax_Syntax.Pat_cons uu____23070  in
              {
                FStar_Syntax_Syntax.v = uu____23069;
                FStar_Syntax_Syntax.p =
                  (uu___200_23068.FStar_Syntax_Syntax.p)
              }
          | uu____23132 -> p  in
        let elim_branch uu____23154 =
          match uu____23154 with
          | (pat,wopt,t3) ->
              let uu____23180 = elim_pat pat  in
              let uu____23183 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____23186 = elim_delayed_subst_term t3  in
              (uu____23180, uu____23183, uu____23186)
           in
        let uu____23191 =
          let uu____23192 =
            let uu____23215 = elim_delayed_subst_term t2  in
            let uu____23216 = FStar_List.map elim_branch branches  in
            (uu____23215, uu____23216)  in
          FStar_Syntax_Syntax.Tm_match uu____23192  in
        mk1 uu____23191
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____23325 =
          match uu____23325 with
          | (tc,topt) ->
              let uu____23360 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____23370 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____23370
                | FStar_Util.Inr c ->
                    let uu____23372 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____23372
                 in
              let uu____23373 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____23360, uu____23373)
           in
        let uu____23382 =
          let uu____23383 =
            let uu____23410 = elim_delayed_subst_term t2  in
            let uu____23411 = elim_ascription a  in
            (uu____23410, uu____23411, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____23383  in
        mk1 uu____23382
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___201_23456 = lb  in
          let uu____23457 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23460 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___201_23456.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___201_23456.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____23457;
            FStar_Syntax_Syntax.lbeff =
              (uu___201_23456.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____23460;
            FStar_Syntax_Syntax.lbattrs =
              (uu___201_23456.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___201_23456.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____23463 =
          let uu____23464 =
            let uu____23477 =
              let uu____23484 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____23484)  in
            let uu____23493 = elim_delayed_subst_term t2  in
            (uu____23477, uu____23493)  in
          FStar_Syntax_Syntax.Tm_let uu____23464  in
        mk1 uu____23463
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____23526 =
          let uu____23527 =
            let uu____23544 = elim_delayed_subst_term t2  in
            (uv, uu____23544)  in
          FStar_Syntax_Syntax.Tm_uvar uu____23527  in
        mk1 uu____23526
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____23562 =
          let uu____23563 =
            let uu____23570 = elim_delayed_subst_term tm  in
            (uu____23570, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____23563  in
        mk1 uu____23562
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____23577 =
          let uu____23578 =
            let uu____23585 = elim_delayed_subst_term t2  in
            let uu____23586 = elim_delayed_subst_meta md  in
            (uu____23585, uu____23586)  in
          FStar_Syntax_Syntax.Tm_meta uu____23578  in
        mk1 uu____23577

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_23593  ->
         match uu___93_23593 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____23597 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____23597
         | f -> f) flags1

and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____23618 =
          let uu____23619 =
            let uu____23628 = elim_delayed_subst_term t  in
            (uu____23628, uopt)  in
          FStar_Syntax_Syntax.Total uu____23619  in
        mk1 uu____23618
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____23641 =
          let uu____23642 =
            let uu____23651 = elim_delayed_subst_term t  in
            (uu____23651, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____23642  in
        mk1 uu____23641
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___202_23656 = ct  in
          let uu____23657 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____23660 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____23669 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___202_23656.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___202_23656.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____23657;
            FStar_Syntax_Syntax.effect_args = uu____23660;
            FStar_Syntax_Syntax.flags = uu____23669
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_23672  ->
    match uu___94_23672 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____23684 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____23684
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____23717 =
          let uu____23724 = elim_delayed_subst_term t  in (m, uu____23724)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____23717
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____23732 =
          let uu____23741 = elim_delayed_subst_term t  in
          (m1, m2, uu____23741)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23732
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____23764  ->
         match uu____23764 with
         | (t,q) ->
             let uu____23775 = elim_delayed_subst_term t  in (uu____23775, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____23795  ->
         match uu____23795 with
         | (x,q) ->
             let uu____23806 =
               let uu___203_23807 = x  in
               let uu____23808 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___203_23807.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___203_23807.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____23808
               }  in
             (uu____23806, q)) bs

let (elim_uvars_aux_tc :
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
            FStar_Pervasives_Native.tuple3)
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
            | (uu____23884,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____23890,FStar_Util.Inl t) ->
                let uu____23896 =
                  let uu____23899 =
                    let uu____23900 =
                      let uu____23913 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____23913)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____23900  in
                  FStar_Syntax_Syntax.mk uu____23899  in
                uu____23896 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____23917 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____23917 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____23945 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____24000 ->
                    let uu____24001 =
                      let uu____24010 =
                        let uu____24011 = FStar_Syntax_Subst.compress t4  in
                        uu____24011.FStar_Syntax_Syntax.n  in
                      (uu____24010, tc)  in
                    (match uu____24001 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____24036) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____24073) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____24112,FStar_Util.Inl uu____24113) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____24136 -> failwith "Impossible")
                 in
              (match uu____23945 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____24241 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____24241 with
          | (univ_names1,binders1,tc) ->
              let uu____24299 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____24299)
  
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____24334 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____24334 with
          | (univ_names1,binders1,tc) ->
              let uu____24394 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____24394)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____24427 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____24427 with
           | (univ_names1,binders1,typ1) ->
               let uu___204_24455 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_24455.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_24455.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_24455.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_24455.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___205_24476 = s  in
          let uu____24477 =
            let uu____24478 =
              let uu____24487 = FStar_List.map (elim_uvars env) sigs  in
              (uu____24487, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____24478  in
          {
            FStar_Syntax_Syntax.sigel = uu____24477;
            FStar_Syntax_Syntax.sigrng =
              (uu___205_24476.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___205_24476.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___205_24476.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___205_24476.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____24504 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24504 with
           | (univ_names1,uu____24522,typ1) ->
               let uu___206_24536 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___206_24536.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___206_24536.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___206_24536.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___206_24536.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____24542 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24542 with
           | (univ_names1,uu____24560,typ1) ->
               let uu___207_24574 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___207_24574.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___207_24574.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___207_24574.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___207_24574.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____24608 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____24608 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____24631 =
                            let uu____24632 =
                              let uu____24633 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____24633  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24632
                             in
                          elim_delayed_subst_term uu____24631  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___208_24636 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___208_24636.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___208_24636.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___208_24636.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___208_24636.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___209_24637 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___209_24637.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___209_24637.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___209_24637.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___209_24637.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___210_24649 = s  in
          let uu____24650 =
            let uu____24651 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____24651  in
          {
            FStar_Syntax_Syntax.sigel = uu____24650;
            FStar_Syntax_Syntax.sigrng =
              (uu___210_24649.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___210_24649.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___210_24649.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___210_24649.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____24655 = elim_uvars_aux_t env us [] t  in
          (match uu____24655 with
           | (us1,uu____24673,t1) ->
               let uu___211_24687 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_24687.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_24687.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_24687.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___211_24687.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24688 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24690 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____24690 with
           | (univs1,binders,signature) ->
               let uu____24718 =
                 let uu____24727 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____24727 with
                 | (univs_opening,univs2) ->
                     let uu____24754 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____24754)
                  in
               (match uu____24718 with
                | (univs_opening,univs_closing) ->
                    let uu____24771 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____24777 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____24778 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____24777, uu____24778)  in
                    (match uu____24771 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____24800 =
                           match uu____24800 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____24818 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____24818 with
                                | (us1,t1) ->
                                    let uu____24829 =
                                      let uu____24834 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____24841 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____24834, uu____24841)  in
                                    (match uu____24829 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____24854 =
                                           let uu____24859 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____24868 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____24859, uu____24868)  in
                                         (match uu____24854 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____24884 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____24884
                                                 in
                                              let uu____24885 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____24885 with
                                               | (uu____24906,uu____24907,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____24922 =
                                                       let uu____24923 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24923
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24922
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____24928 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____24928 with
                           | (uu____24941,uu____24942,t1) -> t1  in
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
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____25002 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____25019 =
                               let uu____25020 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____25020.FStar_Syntax_Syntax.n  in
                             match uu____25019 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____25079 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____25108 =
                               let uu____25109 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____25109.FStar_Syntax_Syntax.n  in
                             match uu____25108 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____25130) ->
                                 let uu____25151 = destruct_action_body body
                                    in
                                 (match uu____25151 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____25196 ->
                                 let uu____25197 = destruct_action_body t  in
                                 (match uu____25197 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____25246 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____25246 with
                           | (action_univs,t) ->
                               let uu____25255 = destruct_action_typ_templ t
                                  in
                               (match uu____25255 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___212_25296 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___212_25296.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___212_25296.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      }  in
                                    a')
                            in
                         let ed1 =
                           let uu___213_25298 = ed  in
                           let uu____25299 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____25300 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____25301 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____25302 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____25303 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____25304 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____25305 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____25306 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____25307 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____25308 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____25309 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____25310 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____25311 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____25312 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___213_25298.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___213_25298.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____25299;
                             FStar_Syntax_Syntax.bind_wp = uu____25300;
                             FStar_Syntax_Syntax.if_then_else = uu____25301;
                             FStar_Syntax_Syntax.ite_wp = uu____25302;
                             FStar_Syntax_Syntax.stronger = uu____25303;
                             FStar_Syntax_Syntax.close_wp = uu____25304;
                             FStar_Syntax_Syntax.assert_p = uu____25305;
                             FStar_Syntax_Syntax.assume_p = uu____25306;
                             FStar_Syntax_Syntax.null_wp = uu____25307;
                             FStar_Syntax_Syntax.trivial = uu____25308;
                             FStar_Syntax_Syntax.repr = uu____25309;
                             FStar_Syntax_Syntax.return_repr = uu____25310;
                             FStar_Syntax_Syntax.bind_repr = uu____25311;
                             FStar_Syntax_Syntax.actions = uu____25312;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___213_25298.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___214_25315 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___214_25315.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___214_25315.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___214_25315.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___214_25315.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_25332 =
            match uu___95_25332 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____25359 = elim_uvars_aux_t env us [] t  in
                (match uu____25359 with
                 | (us1,uu____25383,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___215_25402 = sub_eff  in
            let uu____25403 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____25406 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___215_25402.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___215_25402.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____25403;
              FStar_Syntax_Syntax.lift = uu____25406
            }  in
          let uu___216_25409 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___216_25409.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_25409.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_25409.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_25409.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____25419 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____25419 with
           | (univ_names1,binders1,comp1) ->
               let uu___217_25453 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___217_25453.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___217_25453.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___217_25453.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___217_25453.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25464 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25465 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  