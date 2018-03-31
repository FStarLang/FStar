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
                                          (uu___149_10163.unfold_fully);
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
               let uu____10175 = lookup_bvar env x  in
               (match uu____10175 with
                | Univ uu____10178 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____10227 = FStar_ST.op_Bang r  in
                      (match uu____10227 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____10345  ->
                                 let uu____10346 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10347 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10346
                                   uu____10347);
                            (let uu____10348 =
                               let uu____10349 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____10349.FStar_Syntax_Syntax.n  in
                             match uu____10348 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10352 ->
                                 norm cfg env2 stack t'
                             | uu____10369 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10439)::uu____10440 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10449)::uu____10450 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____10460,uu____10461))::stack_rest ->
                    (match c with
                     | Univ uu____10465 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10474 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____10495  ->
                                    let uu____10496 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10496);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____10536  ->
                                    let uu____10537 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10537);
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
                       (fun uu____10615  ->
                          let uu____10616 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10616);
                     norm cfg env stack1 t1)
                | (Debug uu____10617)::uu____10618 ->
                    if (cfg.steps).weak
                    then
                      let uu____10625 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10625
                    else
                      (let uu____10627 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10627 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10669  -> dummy :: env1) env)
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
                                          let uu____10706 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10706)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_10711 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_10711.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_10711.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10712 -> lopt  in
                           (log cfg
                              (fun uu____10718  ->
                                 let uu____10719 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10719);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_10728 = cfg  in
                               {
                                 steps = (uu___151_10728.steps);
                                 tcenv = (uu___151_10728.tcenv);
                                 debug = (uu___151_10728.debug);
                                 delta_level = (uu___151_10728.delta_level);
                                 primitive_steps =
                                   (uu___151_10728.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_10728.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_10728.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10739)::uu____10740 ->
                    if (cfg.steps).weak
                    then
                      let uu____10747 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10747
                    else
                      (let uu____10749 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10749 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10791  -> dummy :: env1) env)
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
                                          let uu____10828 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10828)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_10833 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_10833.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_10833.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10834 -> lopt  in
                           (log cfg
                              (fun uu____10840  ->
                                 let uu____10841 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10841);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_10850 = cfg  in
                               {
                                 steps = (uu___151_10850.steps);
                                 tcenv = (uu___151_10850.tcenv);
                                 debug = (uu___151_10850.debug);
                                 delta_level = (uu___151_10850.delta_level);
                                 primitive_steps =
                                   (uu___151_10850.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_10850.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_10850.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____10861)::uu____10862 ->
                    if (cfg.steps).weak
                    then
                      let uu____10873 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10873
                    else
                      (let uu____10875 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10875 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10917  -> dummy :: env1) env)
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
                                          let uu____10954 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10954)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_10959 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_10959.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_10959.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10960 -> lopt  in
                           (log cfg
                              (fun uu____10966  ->
                                 let uu____10967 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10967);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_10976 = cfg  in
                               {
                                 steps = (uu___151_10976.steps);
                                 tcenv = (uu___151_10976.tcenv);
                                 debug = (uu___151_10976.debug);
                                 delta_level = (uu___151_10976.delta_level);
                                 primitive_steps =
                                   (uu___151_10976.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_10976.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_10976.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____10987)::uu____10988 ->
                    if (cfg.steps).weak
                    then
                      let uu____10999 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10999
                    else
                      (let uu____11001 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11001 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11043  -> dummy :: env1) env)
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
                                          let uu____11080 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11080)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11085 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11085.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11085.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11086 -> lopt  in
                           (log cfg
                              (fun uu____11092  ->
                                 let uu____11093 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11093);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11102 = cfg  in
                               {
                                 steps = (uu___151_11102.steps);
                                 tcenv = (uu___151_11102.tcenv);
                                 debug = (uu___151_11102.debug);
                                 delta_level = (uu___151_11102.delta_level);
                                 primitive_steps =
                                   (uu___151_11102.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11102.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11102.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11113)::uu____11114 ->
                    if (cfg.steps).weak
                    then
                      let uu____11129 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11129
                    else
                      (let uu____11131 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11131 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11173  -> dummy :: env1) env)
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
                                          let uu____11210 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11210)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11215 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11215.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11215.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11216 -> lopt  in
                           (log cfg
                              (fun uu____11222  ->
                                 let uu____11223 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11223);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11232 = cfg  in
                               {
                                 steps = (uu___151_11232.steps);
                                 tcenv = (uu___151_11232.tcenv);
                                 debug = (uu___151_11232.debug);
                                 delta_level = (uu___151_11232.delta_level);
                                 primitive_steps =
                                   (uu___151_11232.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11232.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11232.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____11243 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11243
                    else
                      (let uu____11245 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11245 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11287  -> dummy :: env1) env)
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
                                          let uu____11324 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11324)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11329 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11329.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11329.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11330 -> lopt  in
                           (log cfg
                              (fun uu____11336  ->
                                 let uu____11337 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11337);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11346 = cfg  in
                               {
                                 steps = (uu___151_11346.steps);
                                 tcenv = (uu___151_11346.tcenv);
                                 debug = (uu___151_11346.debug);
                                 delta_level = (uu___151_11346.delta_level);
                                 primitive_steps =
                                   (uu___151_11346.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11346.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11346.normalize_pure_lets)
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
                      (fun uu____11395  ->
                         fun stack1  ->
                           match uu____11395 with
                           | (a,aq) ->
                               let uu____11407 =
                                 let uu____11408 =
                                   let uu____11415 =
                                     let uu____11416 =
                                       let uu____11447 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____11447, false)  in
                                     Clos uu____11416  in
                                   (uu____11415, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____11408  in
                               uu____11407 :: stack1) args)
                  in
               (log cfg
                  (fun uu____11531  ->
                     let uu____11532 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11532);
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
                             ((let uu___152_11568 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___152_11568.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___152_11568.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____11569 ->
                      let uu____11574 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11574)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____11577 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____11577 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____11608 =
                          let uu____11609 =
                            let uu____11616 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___153_11618 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___153_11618.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___153_11618.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11616)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____11609  in
                        mk uu____11608 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____11637 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____11637
               else
                 (let uu____11639 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____11639 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____11647 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____11671  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____11647 c1  in
                      let t2 =
                        let uu____11693 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____11693 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____11804)::uu____11805 ->
                    (log cfg
                       (fun uu____11816  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____11817)::uu____11818 ->
                    (log cfg
                       (fun uu____11829  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____11830,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____11831;
                                   FStar_Syntax_Syntax.vars = uu____11832;_},uu____11833,uu____11834))::uu____11835
                    ->
                    (log cfg
                       (fun uu____11844  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____11845)::uu____11846 ->
                    (log cfg
                       (fun uu____11857  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____11858 ->
                    (log cfg
                       (fun uu____11861  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____11865  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____11882 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____11882
                         | FStar_Util.Inr c ->
                             let uu____11890 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____11890
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____11903 =
                               let uu____11904 =
                                 let uu____11931 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11931, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11904
                                in
                             mk uu____11903 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____11950 ->
                           let uu____11951 =
                             let uu____11952 =
                               let uu____11953 =
                                 let uu____11980 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11980, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11953
                                in
                             mk uu____11952 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____11951))))
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
                         let uu____12090 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12090 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___154_12110 = cfg  in
                               let uu____12111 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___154_12110.steps);
                                 tcenv = uu____12111;
                                 debug = (uu___154_12110.debug);
                                 delta_level = (uu___154_12110.delta_level);
                                 primitive_steps =
                                   (uu___154_12110.primitive_steps);
                                 strong = (uu___154_12110.strong);
                                 memoize_lazy = (uu___154_12110.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_12110.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____12116 =
                                 let uu____12117 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12117  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12116
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___155_12120 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___155_12120.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___155_12120.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___155_12120.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___155_12120.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12121 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12121
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12132,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12133;
                               FStar_Syntax_Syntax.lbunivs = uu____12134;
                               FStar_Syntax_Syntax.lbtyp = uu____12135;
                               FStar_Syntax_Syntax.lbeff = uu____12136;
                               FStar_Syntax_Syntax.lbdef = uu____12137;
                               FStar_Syntax_Syntax.lbattrs = uu____12138;
                               FStar_Syntax_Syntax.lbpos = uu____12139;_}::uu____12140),uu____12141)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12181 =
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
               if uu____12181
               then
                 let binder =
                   let uu____12183 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12183  in
                 let env1 =
                   let uu____12193 =
                     let uu____12200 =
                       let uu____12201 =
                         let uu____12232 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12232,
                           false)
                          in
                       Clos uu____12201  in
                     ((FStar_Pervasives_Native.Some binder), uu____12200)  in
                   uu____12193 :: env  in
                 (log cfg
                    (fun uu____12325  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____12329  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12330 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12330))
                 else
                   (let uu____12332 =
                      let uu____12337 =
                        let uu____12338 =
                          let uu____12339 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12339
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12338]  in
                      FStar_Syntax_Subst.open_term uu____12337 body  in
                    match uu____12332 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____12348  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12356 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12356  in
                            FStar_Util.Inl
                              (let uu___156_12366 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___156_12366.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___156_12366.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____12369  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___157_12371 = lb  in
                             let uu____12372 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___157_12371.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___157_12371.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12372;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___157_12371.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___157_12371.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12407  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___158_12430 = cfg  in
                             {
                               steps = (uu___158_12430.steps);
                               tcenv = (uu___158_12430.tcenv);
                               debug = (uu___158_12430.debug);
                               delta_level = (uu___158_12430.delta_level);
                               primitive_steps =
                                 (uu___158_12430.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___158_12430.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___158_12430.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____12433  ->
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
               let uu____12450 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____12450 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____12486 =
                               let uu___159_12487 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___159_12487.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___159_12487.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____12486  in
                           let uu____12488 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____12488 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____12514 =
                                   FStar_List.map (fun uu____12530  -> dummy)
                                     lbs1
                                    in
                                 let uu____12531 =
                                   let uu____12540 =
                                     FStar_List.map
                                       (fun uu____12560  -> dummy) xs1
                                      in
                                   FStar_List.append uu____12540 env  in
                                 FStar_List.append uu____12514 uu____12531
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12584 =
                                       let uu___160_12585 = rc  in
                                       let uu____12586 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___160_12585.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12586;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___160_12585.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____12584
                                 | uu____12593 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___161_12597 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___161_12597.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___161_12597.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___161_12597.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___161_12597.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____12607 =
                        FStar_List.map (fun uu____12623  -> dummy) lbs2  in
                      FStar_List.append uu____12607 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____12631 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____12631 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___162_12647 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___162_12647.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___162_12647.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____12674 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12674
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12693 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____12769  ->
                        match uu____12769 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___163_12890 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___163_12890.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___163_12890.FStar_Syntax_Syntax.sort)
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
               (match uu____12693 with
                | (rec_env,memos,uu____13103) ->
                    let uu____13156 =
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
                             let uu____13467 =
                               let uu____13474 =
                                 let uu____13475 =
                                   let uu____13506 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13506, false)
                                    in
                                 Clos uu____13475  in
                               (FStar_Pervasives_Native.None, uu____13474)
                                in
                             uu____13467 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____13616  ->
                     let uu____13617 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13617);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13639 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____13641::uu____13642 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____13647) ->
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
                             | uu____13670 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____13684 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____13684
                              | uu____13695 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____13699 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13725 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13743 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____13760 =
                        let uu____13761 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____13762 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13761 uu____13762
                         in
                      failwith uu____13760
                    else rebuild cfg env stack t2
                | uu____13764 -> norm cfg env stack t2))

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
                let uu____13774 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____13774  in
              let uu____13775 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____13775 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____13788  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____13799  ->
                        let uu____13800 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____13801 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____13800 uu____13801);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____13806 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____13806 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____13815))::stack1 ->
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
                      | uu____13870 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____13873 ->
                          let uu____13876 =
                            let uu____13877 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____13877
                             in
                          failwith uu____13876
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
                  let uu___164_13901 = cfg  in
                  let uu____13902 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____13902;
                    tcenv = (uu___164_13901.tcenv);
                    debug = (uu___164_13901.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___164_13901.primitive_steps);
                    strong = (uu___164_13901.strong);
                    memoize_lazy = (uu___164_13901.memoize_lazy);
                    normalize_pure_lets =
                      (uu___164_13901.normalize_pure_lets)
                  }
                else
                  (let uu___165_13904 = cfg  in
                   {
                     steps =
                       (let uu___166_13907 = cfg.steps  in
                        {
                          beta = (uu___166_13907.beta);
                          iota = (uu___166_13907.iota);
                          zeta = false;
                          weak = (uu___166_13907.weak);
                          hnf = (uu___166_13907.hnf);
                          primops = (uu___166_13907.primops);
                          no_delta_steps = (uu___166_13907.no_delta_steps);
                          unfold_until = (uu___166_13907.unfold_until);
                          unfold_only = (uu___166_13907.unfold_only);
                          unfold_fully = (uu___166_13907.unfold_fully);
                          unfold_attr = (uu___166_13907.unfold_attr);
                          unfold_tac = (uu___166_13907.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___166_13907.pure_subterms_within_computations);
                          simplify = (uu___166_13907.simplify);
                          erase_universes = (uu___166_13907.erase_universes);
                          allow_unbound_universes =
                            (uu___166_13907.allow_unbound_universes);
                          reify_ = (uu___166_13907.reify_);
                          compress_uvars = (uu___166_13907.compress_uvars);
                          no_full_norm = (uu___166_13907.no_full_norm);
                          check_no_uvars = (uu___166_13907.check_no_uvars);
                          unmeta = (uu___166_13907.unmeta);
                          unascribe = (uu___166_13907.unascribe)
                        });
                     tcenv = (uu___165_13904.tcenv);
                     debug = (uu___165_13904.debug);
                     delta_level = (uu___165_13904.delta_level);
                     primitive_steps = (uu___165_13904.primitive_steps);
                     strong = (uu___165_13904.strong);
                     memoize_lazy = (uu___165_13904.memoize_lazy);
                     normalize_pure_lets =
                       (uu___165_13904.normalize_pure_lets)
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
                  (fun uu____13937  ->
                     let uu____13938 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____13939 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____13938
                       uu____13939);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____13941 =
                   let uu____13942 = FStar_Syntax_Subst.compress head3  in
                   uu____13942.FStar_Syntax_Syntax.n  in
                 match uu____13941 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____13960 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____13960
                        in
                     let uu____13961 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____13961 with
                      | (uu____13962,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____13968 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____13976 =
                                   let uu____13977 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____13977.FStar_Syntax_Syntax.n  in
                                 match uu____13976 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____13983,uu____13984))
                                     ->
                                     let uu____13993 =
                                       let uu____13994 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____13994.FStar_Syntax_Syntax.n  in
                                     (match uu____13993 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____14000,msrc,uu____14002))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____14011 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14011
                                      | uu____14012 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____14013 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____14014 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____14014 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___167_14019 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___167_14019.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___167_14019.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___167_14019.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___167_14019.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___167_14019.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____14020 = FStar_List.tl stack  in
                                    let uu____14021 =
                                      let uu____14022 =
                                        let uu____14025 =
                                          let uu____14026 =
                                            let uu____14039 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____14039)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____14026
                                           in
                                        FStar_Syntax_Syntax.mk uu____14025
                                         in
                                      uu____14022
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____14020 uu____14021
                                | FStar_Pervasives_Native.None  ->
                                    let uu____14055 =
                                      let uu____14056 = is_return body  in
                                      match uu____14056 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____14060;
                                            FStar_Syntax_Syntax.vars =
                                              uu____14061;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____14066 -> false  in
                                    if uu____14055
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
                                         let uu____14089 =
                                           let uu____14092 =
                                             let uu____14093 =
                                               let uu____14110 =
                                                 let uu____14113 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____14113]  in
                                               (uu____14110, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____14093
                                              in
                                           FStar_Syntax_Syntax.mk uu____14092
                                            in
                                         uu____14089
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____14129 =
                                           let uu____14130 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____14130.FStar_Syntax_Syntax.n
                                            in
                                         match uu____14129 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____14136::uu____14137::[])
                                             ->
                                             let uu____14144 =
                                               let uu____14147 =
                                                 let uu____14148 =
                                                   let uu____14155 =
                                                     let uu____14158 =
                                                       let uu____14159 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____14159
                                                        in
                                                     let uu____14160 =
                                                       let uu____14163 =
                                                         let uu____14164 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____14164
                                                          in
                                                       [uu____14163]  in
                                                     uu____14158 ::
                                                       uu____14160
                                                      in
                                                   (bind1, uu____14155)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____14148
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____14147
                                                in
                                             uu____14144
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____14172 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____14178 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____14178
                                         then
                                           let uu____14181 =
                                             let uu____14182 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14182
                                              in
                                           let uu____14183 =
                                             let uu____14186 =
                                               let uu____14187 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____14187
                                                in
                                             [uu____14186]  in
                                           uu____14181 :: uu____14183
                                         else []  in
                                       let reified =
                                         let uu____14192 =
                                           let uu____14195 =
                                             let uu____14196 =
                                               let uu____14211 =
                                                 let uu____14214 =
                                                   let uu____14217 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____14218 =
                                                     let uu____14221 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____14221]  in
                                                   uu____14217 :: uu____14218
                                                    in
                                                 let uu____14222 =
                                                   let uu____14225 =
                                                     let uu____14228 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____14229 =
                                                       let uu____14232 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____14233 =
                                                         let uu____14236 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____14237 =
                                                           let uu____14240 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____14240]  in
                                                         uu____14236 ::
                                                           uu____14237
                                                          in
                                                       uu____14232 ::
                                                         uu____14233
                                                        in
                                                     uu____14228 ::
                                                       uu____14229
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____14225
                                                    in
                                                 FStar_List.append
                                                   uu____14214 uu____14222
                                                  in
                                               (bind_inst, uu____14211)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____14196
                                              in
                                           FStar_Syntax_Syntax.mk uu____14195
                                            in
                                         uu____14192
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____14252  ->
                                            let uu____14253 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____14254 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____14253 uu____14254);
                                       (let uu____14255 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____14255 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____14279 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14279
                        in
                     let uu____14280 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14280 with
                      | (uu____14281,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____14316 =
                                  let uu____14317 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____14317.FStar_Syntax_Syntax.n  in
                                match uu____14316 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____14323) -> t2
                                | uu____14328 -> head4  in
                              let uu____14329 =
                                let uu____14330 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____14330.FStar_Syntax_Syntax.n  in
                              match uu____14329 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____14336 -> FStar_Pervasives_Native.None
                               in
                            let uu____14337 = maybe_extract_fv head4  in
                            match uu____14337 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____14347 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____14347
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____14352 = maybe_extract_fv head5
                                     in
                                  match uu____14352 with
                                  | FStar_Pervasives_Native.Some uu____14357
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____14358 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____14363 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____14378 =
                              match uu____14378 with
                              | (e,q) ->
                                  let uu____14385 =
                                    let uu____14386 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14386.FStar_Syntax_Syntax.n  in
                                  (match uu____14385 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____14401 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____14401
                                   | uu____14402 -> false)
                               in
                            let uu____14403 =
                              let uu____14404 =
                                let uu____14411 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____14411 :: args  in
                              FStar_Util.for_some is_arg_impure uu____14404
                               in
                            if uu____14403
                            then
                              let uu____14416 =
                                let uu____14417 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____14417
                                 in
                              failwith uu____14416
                            else ());
                           (let uu____14419 = maybe_unfold_action head_app
                               in
                            match uu____14419 with
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
                                   (fun uu____14460  ->
                                      let uu____14461 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____14462 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____14461 uu____14462);
                                 (let uu____14463 = FStar_List.tl stack  in
                                  norm cfg env uu____14463 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____14465) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____14489 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____14489  in
                     (log cfg
                        (fun uu____14493  ->
                           let uu____14494 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____14494);
                      (let uu____14495 = FStar_List.tl stack  in
                       norm cfg env uu____14495 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____14616  ->
                               match uu____14616 with
                               | (pat,wopt,tm) ->
                                   let uu____14664 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____14664)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____14696 = FStar_List.tl stack  in
                     norm cfg env uu____14696 tm
                 | uu____14697 -> fallback ())

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
              (fun uu____14711  ->
                 let uu____14712 = FStar_Ident.string_of_lid msrc  in
                 let uu____14713 = FStar_Ident.string_of_lid mtgt  in
                 let uu____14714 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14712
                   uu____14713 uu____14714);
            (let uu____14715 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____14715
             then
               let ed =
                 let uu____14717 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____14717  in
               let uu____14718 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____14718 with
               | (uu____14719,return_repr) ->
                   let return_inst =
                     let uu____14728 =
                       let uu____14729 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____14729.FStar_Syntax_Syntax.n  in
                     match uu____14728 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____14735::[]) ->
                         let uu____14742 =
                           let uu____14745 =
                             let uu____14746 =
                               let uu____14753 =
                                 let uu____14756 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____14756]  in
                               (return_tm, uu____14753)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____14746  in
                           FStar_Syntax_Syntax.mk uu____14745  in
                         uu____14742 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14764 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____14767 =
                     let uu____14770 =
                       let uu____14771 =
                         let uu____14786 =
                           let uu____14789 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14790 =
                             let uu____14793 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14793]  in
                           uu____14789 :: uu____14790  in
                         (return_inst, uu____14786)  in
                       FStar_Syntax_Syntax.Tm_app uu____14771  in
                     FStar_Syntax_Syntax.mk uu____14770  in
                   uu____14767 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14802 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14802 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14805 =
                      let uu____14806 = FStar_Ident.text_of_lid msrc  in
                      let uu____14807 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14806 uu____14807
                       in
                    failwith uu____14805
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14808;
                      FStar_TypeChecker_Env.mtarget = uu____14809;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14810;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____14825 =
                      let uu____14826 = FStar_Ident.text_of_lid msrc  in
                      let uu____14827 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14826 uu____14827
                       in
                    failwith uu____14825
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14828;
                      FStar_TypeChecker_Env.mtarget = uu____14829;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14830;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14854 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____14855 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____14854 t FStar_Syntax_Syntax.tun uu____14855))

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
                (fun uu____14911  ->
                   match uu____14911 with
                   | (a,imp) ->
                       let uu____14922 = norm cfg env [] a  in
                       (uu____14922, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____14930  ->
             let uu____14931 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____14932 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____14931 uu____14932);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14956 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____14956
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___168_14959 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___168_14959.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___168_14959.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14979 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____14979
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___169_14982 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___169_14982.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___169_14982.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____15015  ->
                      match uu____15015 with
                      | (a,i) ->
                          let uu____15026 = norm cfg env [] a  in
                          (uu____15026, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_15044  ->
                       match uu___90_15044 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____15048 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____15048
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___170_15056 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___171_15059 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___171_15059.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___170_15056.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___170_15056.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____15062  ->
        match uu____15062 with
        | (x,imp) ->
            let uu____15065 =
              let uu___172_15066 = x  in
              let uu____15067 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___172_15066.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___172_15066.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15067
              }  in
            (uu____15065, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15073 =
          FStar_List.fold_left
            (fun uu____15091  ->
               fun b  ->
                 match uu____15091 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____15073 with | (nbs,uu____15131) -> FStar_List.rev nbs

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
            let uu____15147 =
              let uu___173_15148 = rc  in
              let uu____15149 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___173_15148.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15149;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___173_15148.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____15147
        | uu____15156 -> lopt

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
            (let uu____15177 = FStar_Syntax_Print.term_to_string tm  in
             let uu____15178 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____15177
               uu____15178)
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
          let uu____15198 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____15198
          then tm1
          else
            (let w t =
               let uu___174_15210 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___174_15210.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___174_15210.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____15219 =
                 let uu____15220 = FStar_Syntax_Util.unmeta t  in
                 uu____15220.FStar_Syntax_Syntax.n  in
               match uu____15219 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____15227 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____15272)::args1,(bv,uu____15275)::bs1) ->
                   let uu____15309 =
                     let uu____15310 = FStar_Syntax_Subst.compress t  in
                     uu____15310.FStar_Syntax_Syntax.n  in
                   (match uu____15309 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____15314 -> false)
               | ([],[]) -> true
               | (uu____15335,uu____15336) -> false  in
             let is_applied bs t =
               let uu____15372 = FStar_Syntax_Util.head_and_args' t  in
               match uu____15372 with
               | (hd1,args) ->
                   let uu____15405 =
                     let uu____15406 = FStar_Syntax_Subst.compress hd1  in
                     uu____15406.FStar_Syntax_Syntax.n  in
                   (match uu____15405 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____15412 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____15424 = FStar_Syntax_Util.is_squash t  in
               match uu____15424 with
               | FStar_Pervasives_Native.Some (uu____15435,t') ->
                   is_applied bs t'
               | uu____15447 ->
                   let uu____15456 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____15456 with
                    | FStar_Pervasives_Native.Some (uu____15467,t') ->
                        is_applied bs t'
                    | uu____15479 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____15496 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15496 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15503)::(q,uu____15505)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____15540 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____15540 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____15545 =
                          let uu____15546 = FStar_Syntax_Subst.compress p  in
                          uu____15546.FStar_Syntax_Syntax.n  in
                        (match uu____15545 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15552 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____15552
                         | uu____15553 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____15556)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____15581 =
                          let uu____15582 = FStar_Syntax_Subst.compress p1
                             in
                          uu____15582.FStar_Syntax_Syntax.n  in
                        (match uu____15581 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15588 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____15588
                         | uu____15589 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____15593 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____15593 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____15598 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____15598 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15605 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15605
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____15608)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____15633 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____15633 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15640 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15640
                              | uu____15641 -> FStar_Pervasives_Native.None)
                         | uu____15644 -> FStar_Pervasives_Native.None)
                    | uu____15647 -> FStar_Pervasives_Native.None)
               | uu____15650 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15661 =
                 let uu____15662 = FStar_Syntax_Subst.compress phi  in
                 uu____15662.FStar_Syntax_Syntax.n  in
               match uu____15661 with
               | FStar_Syntax_Syntax.Tm_match (uu____15667,br::brs) ->
                   let uu____15734 = br  in
                   (match uu____15734 with
                    | (uu____15751,uu____15752,e) ->
                        let r =
                          let uu____15773 = simp_t e  in
                          match uu____15773 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15779 =
                                FStar_List.for_all
                                  (fun uu____15797  ->
                                     match uu____15797 with
                                     | (uu____15810,uu____15811,e') ->
                                         let uu____15825 = simp_t e'  in
                                         uu____15825 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15779
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15833 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15838 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15838
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15859 =
                 match uu____15859 with
                 | (t1,q) ->
                     let uu____15872 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15872 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15900 -> (t1, q))
                  in
               let uu____15909 = FStar_Syntax_Util.head_and_args t  in
               match uu____15909 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15971 =
                 let uu____15972 = FStar_Syntax_Util.unmeta ty  in
                 uu____15972.FStar_Syntax_Syntax.n  in
               match uu____15971 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15976) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15981,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____16001 -> false  in
             let simplify1 arg =
               let uu____16024 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____16024, arg)  in
             let uu____16033 = is_quantified_const tm1  in
             match uu____16033 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____16037 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____16037
             | FStar_Pervasives_Native.None  ->
                 let uu____16038 =
                   let uu____16039 = FStar_Syntax_Subst.compress tm1  in
                   uu____16039.FStar_Syntax_Syntax.n  in
                 (match uu____16038 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____16043;
                              FStar_Syntax_Syntax.vars = uu____16044;_},uu____16045);
                         FStar_Syntax_Syntax.pos = uu____16046;
                         FStar_Syntax_Syntax.vars = uu____16047;_},args)
                      ->
                      let uu____16073 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____16073
                      then
                        let uu____16074 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____16074 with
                         | (FStar_Pervasives_Native.Some (true ),uu____16121)::
                             (uu____16122,(arg,uu____16124))::[] ->
                             maybe_auto_squash arg
                         | (uu____16173,(arg,uu____16175))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____16176)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____16225)::uu____16226::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16277::(FStar_Pervasives_Native.Some (false
                                         ),uu____16278)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16329 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16343 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16343
                         then
                           let uu____16344 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16344 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16391)::uu____16392::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16443::(FStar_Pervasives_Native.Some (true
                                           ),uu____16444)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16495)::(uu____16496,(arg,uu____16498))::[]
                               -> maybe_auto_squash arg
                           | (uu____16547,(arg,uu____16549))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16550)::[]
                               -> maybe_auto_squash arg
                           | uu____16599 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16613 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16613
                            then
                              let uu____16614 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16614 with
                              | uu____16661::(FStar_Pervasives_Native.Some
                                              (true ),uu____16662)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16713)::uu____16714::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16765)::(uu____16766,(arg,uu____16768))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16817,(p,uu____16819))::(uu____16820,
                                                                (q,uu____16822))::[]
                                  ->
                                  let uu____16869 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16869
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16871 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16885 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16885
                               then
                                 let uu____16886 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16886 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16933)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16934)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16985)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16986)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17037)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17038)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17089)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17090)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17141,(arg,uu____17143))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17144)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17193)::(uu____17194,(arg,uu____17196))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17245,(arg,uu____17247))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17248)::[]
                                     ->
                                     let uu____17297 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17297
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17298)::(uu____17299,(arg,uu____17301))::[]
                                     ->
                                     let uu____17350 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17350
                                 | (uu____17351,(p,uu____17353))::(uu____17354,
                                                                   (q,uu____17356))::[]
                                     ->
                                     let uu____17403 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17403
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17405 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17419 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17419
                                  then
                                    let uu____17420 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17420 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17467)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17498)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17529 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17543 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17543
                                     then
                                       match args with
                                       | (t,uu____17545)::[] ->
                                           let uu____17562 =
                                             let uu____17563 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17563.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17562 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17566::[],body,uu____17568)
                                                ->
                                                let uu____17595 = simp_t body
                                                   in
                                                (match uu____17595 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17598 -> tm1)
                                            | uu____17601 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17603))::(t,uu____17605)::[]
                                           ->
                                           let uu____17644 =
                                             let uu____17645 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17645.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17644 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17648::[],body,uu____17650)
                                                ->
                                                let uu____17677 = simp_t body
                                                   in
                                                (match uu____17677 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17680 -> tm1)
                                            | uu____17683 -> tm1)
                                       | uu____17684 -> tm1
                                     else
                                       (let uu____17694 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17694
                                        then
                                          match args with
                                          | (t,uu____17696)::[] ->
                                              let uu____17713 =
                                                let uu____17714 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17714.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17713 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17717::[],body,uu____17719)
                                                   ->
                                                   let uu____17746 =
                                                     simp_t body  in
                                                   (match uu____17746 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17749 -> tm1)
                                               | uu____17752 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17754))::(t,uu____17756)::[]
                                              ->
                                              let uu____17795 =
                                                let uu____17796 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17796.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17795 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17799::[],body,uu____17801)
                                                   ->
                                                   let uu____17828 =
                                                     simp_t body  in
                                                   (match uu____17828 with
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
                                                    | uu____17831 -> tm1)
                                               | uu____17834 -> tm1)
                                          | uu____17835 -> tm1
                                        else
                                          (let uu____17845 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____17845
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17846;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17847;_},uu____17848)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17865;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17866;_},uu____17867)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____17884 -> tm1
                                           else
                                             (let uu____17894 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____17894 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____17914 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____17924;
                         FStar_Syntax_Syntax.vars = uu____17925;_},args)
                      ->
                      let uu____17947 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17947
                      then
                        let uu____17948 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17948 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17995)::
                             (uu____17996,(arg,uu____17998))::[] ->
                             maybe_auto_squash arg
                         | (uu____18047,(arg,uu____18049))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18050)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18099)::uu____18100::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18151::(FStar_Pervasives_Native.Some (false
                                         ),uu____18152)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18203 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18217 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18217
                         then
                           let uu____18218 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18218 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18265)::uu____18266::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18317::(FStar_Pervasives_Native.Some (true
                                           ),uu____18318)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18369)::(uu____18370,(arg,uu____18372))::[]
                               -> maybe_auto_squash arg
                           | (uu____18421,(arg,uu____18423))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18424)::[]
                               -> maybe_auto_squash arg
                           | uu____18473 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18487 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18487
                            then
                              let uu____18488 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18488 with
                              | uu____18535::(FStar_Pervasives_Native.Some
                                              (true ),uu____18536)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18587)::uu____18588::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18639)::(uu____18640,(arg,uu____18642))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18691,(p,uu____18693))::(uu____18694,
                                                                (q,uu____18696))::[]
                                  ->
                                  let uu____18743 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18743
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18745 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18759 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18759
                               then
                                 let uu____18760 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18760 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18807)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18808)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18859)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18860)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18911)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18912)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18963)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18964)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19015,(arg,uu____19017))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19018)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19067)::(uu____19068,(arg,uu____19070))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19119,(arg,uu____19121))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19122)::[]
                                     ->
                                     let uu____19171 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19171
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19172)::(uu____19173,(arg,uu____19175))::[]
                                     ->
                                     let uu____19224 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19224
                                 | (uu____19225,(p,uu____19227))::(uu____19228,
                                                                   (q,uu____19230))::[]
                                     ->
                                     let uu____19277 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19277
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19279 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19293 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19293
                                  then
                                    let uu____19294 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19294 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19341)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19372)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19403 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19417 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19417
                                     then
                                       match args with
                                       | (t,uu____19419)::[] ->
                                           let uu____19436 =
                                             let uu____19437 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19437.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19436 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19440::[],body,uu____19442)
                                                ->
                                                let uu____19469 = simp_t body
                                                   in
                                                (match uu____19469 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19472 -> tm1)
                                            | uu____19475 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19477))::(t,uu____19479)::[]
                                           ->
                                           let uu____19518 =
                                             let uu____19519 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19519.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19518 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19522::[],body,uu____19524)
                                                ->
                                                let uu____19551 = simp_t body
                                                   in
                                                (match uu____19551 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19554 -> tm1)
                                            | uu____19557 -> tm1)
                                       | uu____19558 -> tm1
                                     else
                                       (let uu____19568 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19568
                                        then
                                          match args with
                                          | (t,uu____19570)::[] ->
                                              let uu____19587 =
                                                let uu____19588 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19588.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19587 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19591::[],body,uu____19593)
                                                   ->
                                                   let uu____19620 =
                                                     simp_t body  in
                                                   (match uu____19620 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19623 -> tm1)
                                               | uu____19626 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19628))::(t,uu____19630)::[]
                                              ->
                                              let uu____19669 =
                                                let uu____19670 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19670.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19669 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19673::[],body,uu____19675)
                                                   ->
                                                   let uu____19702 =
                                                     simp_t body  in
                                                   (match uu____19702 with
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
                                                    | uu____19705 -> tm1)
                                               | uu____19708 -> tm1)
                                          | uu____19709 -> tm1
                                        else
                                          (let uu____19719 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19719
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19720;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19721;_},uu____19722)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19739;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19740;_},uu____19741)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19758 -> tm1
                                           else
                                             (let uu____19768 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____19768 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19788 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____19803 = simp_t t  in
                      (match uu____19803 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____19806 ->
                      let uu____19829 = is_const_match tm1  in
                      (match uu____19829 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____19832 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____19843  ->
               let uu____19844 = FStar_Syntax_Print.tag_of_term t  in
               let uu____19845 = FStar_Syntax_Print.term_to_string t  in
               let uu____19846 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____19853 =
                 let uu____19854 =
                   let uu____19857 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____19857
                    in
                 stack_to_string uu____19854  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____19844 uu____19845 uu____19846 uu____19853);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____19888 =
                     let uu____19889 =
                       let uu____19890 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____19890  in
                     FStar_Util.string_of_int uu____19889  in
                   let uu____19895 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____19896 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____19888 uu____19895 uu____19896)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____19950  ->
                     let uu____19951 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____19951);
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
               let uu____19987 =
                 let uu___175_19988 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___175_19988.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___175_19988.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19987
           | (Arg (Univ uu____19989,uu____19990,uu____19991))::uu____19992 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19995,uu____19996))::uu____19997 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20012,uu____20013),aq,r))::stack1
               when
               let uu____20063 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20063 ->
               let t2 =
                 let uu____20067 =
                   let uu____20068 =
                     let uu____20069 = closure_as_term cfg env_arg tm  in
                     (uu____20069, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20068  in
                 uu____20067 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20075),aq,r))::stack1 ->
               (log cfg
                  (fun uu____20128  ->
                     let uu____20129 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20129);
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
                  (let uu____20139 = FStar_ST.op_Bang m  in
                   match uu____20139 with
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
                   | FStar_Pervasives_Native.Some (uu____20276,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____20323 =
                 log cfg
                   (fun uu____20327  ->
                      let uu____20328 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____20328);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____20332 =
                 let uu____20333 = FStar_Syntax_Subst.compress t1  in
                 uu____20333.FStar_Syntax_Syntax.n  in
               (match uu____20332 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____20360 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____20360  in
                    (log cfg
                       (fun uu____20364  ->
                          let uu____20365 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____20365);
                     (let uu____20366 = FStar_List.tl stack  in
                      norm cfg env1 uu____20366 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____20367);
                       FStar_Syntax_Syntax.pos = uu____20368;
                       FStar_Syntax_Syntax.vars = uu____20369;_},(e,uu____20371)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____20400 when
                    (cfg.steps).primops ->
                    let uu____20415 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____20415 with
                     | (hd1,args) ->
                         let uu____20452 =
                           let uu____20453 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____20453.FStar_Syntax_Syntax.n  in
                         (match uu____20452 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____20457 = find_prim_step cfg fv  in
                              (match uu____20457 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____20460; arity = uu____20461;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____20463;
                                     requires_binder_substitution =
                                       uu____20464;
                                     interpretation = uu____20465;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____20478 -> fallback " (3)" ())
                          | uu____20481 -> fallback " (4)" ()))
                | uu____20482 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____20502  ->
                     let uu____20503 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____20503);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____20508 =
                   log cfg
                     (fun uu____20513  ->
                        let uu____20514 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____20515 =
                          let uu____20516 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____20533  ->
                                    match uu____20533 with
                                    | (p,uu____20543,uu____20544) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____20516
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____20514 uu____20515);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___91_20561  ->
                                match uu___91_20561 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____20562 -> false))
                         in
                      let uu___176_20563 = cfg  in
                      {
                        steps =
                          (let uu___177_20566 = cfg.steps  in
                           {
                             beta = (uu___177_20566.beta);
                             iota = (uu___177_20566.iota);
                             zeta = false;
                             weak = (uu___177_20566.weak);
                             hnf = (uu___177_20566.hnf);
                             primops = (uu___177_20566.primops);
                             no_delta_steps = (uu___177_20566.no_delta_steps);
                             unfold_until = (uu___177_20566.unfold_until);
                             unfold_only = (uu___177_20566.unfold_only);
                             unfold_fully = (uu___177_20566.unfold_fully);
                             unfold_attr = (uu___177_20566.unfold_attr);
                             unfold_tac = (uu___177_20566.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___177_20566.pure_subterms_within_computations);
                             simplify = (uu___177_20566.simplify);
                             erase_universes =
                               (uu___177_20566.erase_universes);
                             allow_unbound_universes =
                               (uu___177_20566.allow_unbound_universes);
                             reify_ = (uu___177_20566.reify_);
                             compress_uvars = (uu___177_20566.compress_uvars);
                             no_full_norm = (uu___177_20566.no_full_norm);
                             check_no_uvars = (uu___177_20566.check_no_uvars);
                             unmeta = (uu___177_20566.unmeta);
                             unascribe = (uu___177_20566.unascribe)
                           });
                        tcenv = (uu___176_20563.tcenv);
                        debug = (uu___176_20563.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___176_20563.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___176_20563.memoize_lazy);
                        normalize_pure_lets =
                          (uu___176_20563.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____20598 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____20619 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20679  ->
                                    fun uu____20680  ->
                                      match (uu____20679, uu____20680) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____20771 = norm_pat env3 p1
                                             in
                                          (match uu____20771 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____20619 with
                           | (pats1,env3) ->
                               ((let uu___178_20853 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___178_20853.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___179_20872 = x  in
                            let uu____20873 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___179_20872.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___179_20872.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20873
                            }  in
                          ((let uu___180_20887 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___180_20887.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___181_20898 = x  in
                            let uu____20899 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_20898.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_20898.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20899
                            }  in
                          ((let uu___182_20913 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___182_20913.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___183_20929 = x  in
                            let uu____20930 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___183_20929.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___183_20929.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20930
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___184_20937 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___184_20937.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20947 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20961 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20961 with
                                  | (p,wopt,e) ->
                                      let uu____20981 = norm_pat env1 p  in
                                      (match uu____20981 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____21006 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____21006
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____21012 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____21012)
                    in
                 let rec is_cons head1 =
                   let uu____21017 =
                     let uu____21018 = FStar_Syntax_Subst.compress head1  in
                     uu____21018.FStar_Syntax_Syntax.n  in
                   match uu____21017 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____21022) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____21027 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21028;
                         FStar_Syntax_Syntax.fv_delta = uu____21029;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21030;
                         FStar_Syntax_Syntax.fv_delta = uu____21031;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____21032);_}
                       -> true
                   | uu____21039 -> false  in
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
                   let uu____21184 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____21184 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____21271 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____21310 ->
                                 let uu____21311 =
                                   let uu____21312 = is_cons head1  in
                                   Prims.op_Negation uu____21312  in
                                 FStar_Util.Inr uu____21311)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____21337 =
                              let uu____21338 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____21338.FStar_Syntax_Syntax.n  in
                            (match uu____21337 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____21356 ->
                                 let uu____21357 =
                                   let uu____21358 = is_cons head1  in
                                   Prims.op_Negation uu____21358  in
                                 FStar_Util.Inr uu____21357))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____21427)::rest_a,(p1,uu____21430)::rest_p) ->
                       let uu____21474 = matches_pat t2 p1  in
                       (match uu____21474 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____21523 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21629 = matches_pat scrutinee1 p1  in
                       (match uu____21629 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____21669  ->
                                  let uu____21670 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21671 =
                                    let uu____21672 =
                                      FStar_List.map
                                        (fun uu____21682  ->
                                           match uu____21682 with
                                           | (uu____21687,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21672
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21670 uu____21671);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21718  ->
                                       match uu____21718 with
                                       | (bv,t2) ->
                                           let uu____21741 =
                                             let uu____21748 =
                                               let uu____21751 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21751
                                                in
                                             let uu____21752 =
                                               let uu____21753 =
                                                 let uu____21784 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21784, false)
                                                  in
                                               Clos uu____21753  in
                                             (uu____21748, uu____21752)  in
                                           uu____21741 :: env2) env1 s
                                 in
                              let uu____21901 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____21901)))
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
    let uu____21924 =
      let uu____21927 = FStar_ST.op_Bang plugins  in p :: uu____21927  in
    FStar_ST.op_Colon_Equals plugins uu____21924  in
  let retrieve uu____22025 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____22090  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_22123  ->
                  match uu___92_22123 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____22127 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____22133 -> d  in
        let uu____22136 = to_fsteps s  in
        let uu____22137 =
          let uu____22138 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____22139 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____22140 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____22141 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____22142 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____22138;
            primop = uu____22139;
            b380 = uu____22140;
            norm_delayed = uu____22141;
            print_normalized = uu____22142
          }  in
        let uu____22143 =
          let uu____22146 =
            let uu____22149 = retrieve_plugins ()  in
            FStar_List.append uu____22149 psteps  in
          add_steps built_in_primitive_steps uu____22146  in
        let uu____22152 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____22154 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____22154)
           in
        {
          steps = uu____22136;
          tcenv = e;
          debug = uu____22137;
          delta_level = d1;
          primitive_steps = uu____22143;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____22152
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
      fun t  -> let uu____22212 = config s e  in norm_comp uu____22212 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____22225 = config [] env  in norm_universe uu____22225 [] u
  
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
        let uu____22243 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22243  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____22250 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___185_22269 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___185_22269.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___185_22269.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____22276 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____22276
          then
            let ct1 =
              let uu____22278 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____22278 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____22285 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____22285
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___186_22289 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___186_22289.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___186_22289.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___186_22289.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___187_22291 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___187_22291.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___187_22291.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___187_22291.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___187_22291.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___188_22292 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___188_22292.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___188_22292.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____22294 -> c
  
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
        let uu____22306 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22306  in
      let uu____22313 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____22313
      then
        let uu____22314 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____22314 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____22320  ->
                 let uu____22321 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____22321)
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
            ((let uu____22338 =
                let uu____22343 =
                  let uu____22344 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22344
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22343)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____22338);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____22355 = config [AllowUnboundUniverses] env  in
          norm_comp uu____22355 [] c
        with
        | e ->
            ((let uu____22368 =
                let uu____22373 =
                  let uu____22374 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22374
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22373)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____22368);
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
                   let uu____22411 =
                     let uu____22412 =
                       let uu____22419 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____22419)  in
                     FStar_Syntax_Syntax.Tm_refine uu____22412  in
                   mk uu____22411 t01.FStar_Syntax_Syntax.pos
               | uu____22424 -> t2)
          | uu____22425 -> t2  in
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
        let uu____22465 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____22465 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____22494 ->
                 let uu____22501 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____22501 with
                  | (actuals,uu____22511,uu____22512) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____22526 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____22526 with
                         | (binders,args) ->
                             let uu____22543 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____22543
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
      | uu____22551 ->
          let uu____22552 = FStar_Syntax_Util.head_and_args t  in
          (match uu____22552 with
           | (head1,args) ->
               let uu____22589 =
                 let uu____22590 = FStar_Syntax_Subst.compress head1  in
                 uu____22590.FStar_Syntax_Syntax.n  in
               (match uu____22589 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____22593,thead) ->
                    let uu____22619 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____22619 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____22661 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___193_22669 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___193_22669.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___193_22669.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___193_22669.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___193_22669.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___193_22669.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___193_22669.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___193_22669.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___193_22669.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___193_22669.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___193_22669.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___193_22669.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___193_22669.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___193_22669.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___193_22669.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___193_22669.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___193_22669.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___193_22669.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___193_22669.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___193_22669.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___193_22669.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___193_22669.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___193_22669.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___193_22669.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___193_22669.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___193_22669.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___193_22669.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___193_22669.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___193_22669.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___193_22669.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___193_22669.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___193_22669.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___193_22669.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___193_22669.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____22661 with
                            | (uu____22670,ty,uu____22672) ->
                                eta_expand_with_type env t ty))
                | uu____22673 ->
                    let uu____22674 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___194_22682 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___194_22682.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___194_22682.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___194_22682.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___194_22682.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___194_22682.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___194_22682.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___194_22682.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___194_22682.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___194_22682.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___194_22682.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___194_22682.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___194_22682.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___194_22682.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___194_22682.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___194_22682.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___194_22682.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___194_22682.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___194_22682.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___194_22682.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___194_22682.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___194_22682.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___194_22682.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___194_22682.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___194_22682.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___194_22682.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___194_22682.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___194_22682.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___194_22682.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___194_22682.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___194_22682.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___194_22682.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___194_22682.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___194_22682.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____22674 with
                     | (uu____22683,ty,uu____22685) ->
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
      let uu___195_22742 = x  in
      let uu____22743 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___195_22742.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___195_22742.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____22743
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____22746 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____22771 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____22772 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____22773 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____22774 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____22781 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____22782 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____22783 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___196_22811 = rc  in
          let uu____22812 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____22819 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___196_22811.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____22812;
            FStar_Syntax_Syntax.residual_flags = uu____22819
          }  in
        let uu____22822 =
          let uu____22823 =
            let uu____22840 = elim_delayed_subst_binders bs  in
            let uu____22847 = elim_delayed_subst_term t2  in
            let uu____22848 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____22840, uu____22847, uu____22848)  in
          FStar_Syntax_Syntax.Tm_abs uu____22823  in
        mk1 uu____22822
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____22877 =
          let uu____22878 =
            let uu____22891 = elim_delayed_subst_binders bs  in
            let uu____22898 = elim_delayed_subst_comp c  in
            (uu____22891, uu____22898)  in
          FStar_Syntax_Syntax.Tm_arrow uu____22878  in
        mk1 uu____22877
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____22911 =
          let uu____22912 =
            let uu____22919 = elim_bv bv  in
            let uu____22920 = elim_delayed_subst_term phi  in
            (uu____22919, uu____22920)  in
          FStar_Syntax_Syntax.Tm_refine uu____22912  in
        mk1 uu____22911
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____22943 =
          let uu____22944 =
            let uu____22959 = elim_delayed_subst_term t2  in
            let uu____22960 = elim_delayed_subst_args args  in
            (uu____22959, uu____22960)  in
          FStar_Syntax_Syntax.Tm_app uu____22944  in
        mk1 uu____22943
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___197_23024 = p  in
              let uu____23025 =
                let uu____23026 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____23026  in
              {
                FStar_Syntax_Syntax.v = uu____23025;
                FStar_Syntax_Syntax.p =
                  (uu___197_23024.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___198_23028 = p  in
              let uu____23029 =
                let uu____23030 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____23030  in
              {
                FStar_Syntax_Syntax.v = uu____23029;
                FStar_Syntax_Syntax.p =
                  (uu___198_23028.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___199_23037 = p  in
              let uu____23038 =
                let uu____23039 =
                  let uu____23046 = elim_bv x  in
                  let uu____23047 = elim_delayed_subst_term t0  in
                  (uu____23046, uu____23047)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____23039  in
              {
                FStar_Syntax_Syntax.v = uu____23038;
                FStar_Syntax_Syntax.p =
                  (uu___199_23037.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___200_23066 = p  in
              let uu____23067 =
                let uu____23068 =
                  let uu____23081 =
                    FStar_List.map
                      (fun uu____23104  ->
                         match uu____23104 with
                         | (x,b) ->
                             let uu____23117 = elim_pat x  in
                             (uu____23117, b)) pats
                     in
                  (fv, uu____23081)  in
                FStar_Syntax_Syntax.Pat_cons uu____23068  in
              {
                FStar_Syntax_Syntax.v = uu____23067;
                FStar_Syntax_Syntax.p =
                  (uu___200_23066.FStar_Syntax_Syntax.p)
              }
          | uu____23130 -> p  in
        let elim_branch uu____23152 =
          match uu____23152 with
          | (pat,wopt,t3) ->
              let uu____23178 = elim_pat pat  in
              let uu____23181 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____23184 = elim_delayed_subst_term t3  in
              (uu____23178, uu____23181, uu____23184)
           in
        let uu____23189 =
          let uu____23190 =
            let uu____23213 = elim_delayed_subst_term t2  in
            let uu____23214 = FStar_List.map elim_branch branches  in
            (uu____23213, uu____23214)  in
          FStar_Syntax_Syntax.Tm_match uu____23190  in
        mk1 uu____23189
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____23323 =
          match uu____23323 with
          | (tc,topt) ->
              let uu____23358 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____23368 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____23368
                | FStar_Util.Inr c ->
                    let uu____23370 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____23370
                 in
              let uu____23371 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____23358, uu____23371)
           in
        let uu____23380 =
          let uu____23381 =
            let uu____23408 = elim_delayed_subst_term t2  in
            let uu____23409 = elim_ascription a  in
            (uu____23408, uu____23409, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____23381  in
        mk1 uu____23380
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___201_23454 = lb  in
          let uu____23455 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23458 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___201_23454.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___201_23454.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____23455;
            FStar_Syntax_Syntax.lbeff =
              (uu___201_23454.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____23458;
            FStar_Syntax_Syntax.lbattrs =
              (uu___201_23454.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___201_23454.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____23461 =
          let uu____23462 =
            let uu____23475 =
              let uu____23482 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____23482)  in
            let uu____23491 = elim_delayed_subst_term t2  in
            (uu____23475, uu____23491)  in
          FStar_Syntax_Syntax.Tm_let uu____23462  in
        mk1 uu____23461
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____23524 =
          let uu____23525 =
            let uu____23542 = elim_delayed_subst_term t2  in
            (uv, uu____23542)  in
          FStar_Syntax_Syntax.Tm_uvar uu____23525  in
        mk1 uu____23524
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____23560 =
          let uu____23561 =
            let uu____23568 = elim_delayed_subst_term tm  in
            (uu____23568, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____23561  in
        mk1 uu____23560
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____23575 =
          let uu____23576 =
            let uu____23583 = elim_delayed_subst_term t2  in
            let uu____23584 = elim_delayed_subst_meta md  in
            (uu____23583, uu____23584)  in
          FStar_Syntax_Syntax.Tm_meta uu____23576  in
        mk1 uu____23575

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_23591  ->
         match uu___93_23591 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____23595 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____23595
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
        let uu____23616 =
          let uu____23617 =
            let uu____23626 = elim_delayed_subst_term t  in
            (uu____23626, uopt)  in
          FStar_Syntax_Syntax.Total uu____23617  in
        mk1 uu____23616
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____23639 =
          let uu____23640 =
            let uu____23649 = elim_delayed_subst_term t  in
            (uu____23649, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____23640  in
        mk1 uu____23639
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___202_23654 = ct  in
          let uu____23655 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____23658 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____23667 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___202_23654.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___202_23654.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____23655;
            FStar_Syntax_Syntax.effect_args = uu____23658;
            FStar_Syntax_Syntax.flags = uu____23667
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_23670  ->
    match uu___94_23670 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____23682 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____23682
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____23715 =
          let uu____23722 = elim_delayed_subst_term t  in (m, uu____23722)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____23715
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____23730 =
          let uu____23739 = elim_delayed_subst_term t  in
          (m1, m2, uu____23739)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23730
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____23762  ->
         match uu____23762 with
         | (t,q) ->
             let uu____23773 = elim_delayed_subst_term t  in (uu____23773, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____23793  ->
         match uu____23793 with
         | (x,q) ->
             let uu____23804 =
               let uu___203_23805 = x  in
               let uu____23806 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___203_23805.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___203_23805.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____23806
               }  in
             (uu____23804, q)) bs

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
            | (uu____23882,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____23888,FStar_Util.Inl t) ->
                let uu____23894 =
                  let uu____23897 =
                    let uu____23898 =
                      let uu____23911 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____23911)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____23898  in
                  FStar_Syntax_Syntax.mk uu____23897  in
                uu____23894 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____23915 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____23915 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____23943 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23998 ->
                    let uu____23999 =
                      let uu____24008 =
                        let uu____24009 = FStar_Syntax_Subst.compress t4  in
                        uu____24009.FStar_Syntax_Syntax.n  in
                      (uu____24008, tc)  in
                    (match uu____23999 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____24034) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____24071) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____24110,FStar_Util.Inl uu____24111) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____24134 -> failwith "Impossible")
                 in
              (match uu____23943 with
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
          let uu____24239 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____24239 with
          | (univ_names1,binders1,tc) ->
              let uu____24297 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____24297)
  
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
          let uu____24332 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____24332 with
          | (univ_names1,binders1,tc) ->
              let uu____24392 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____24392)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____24425 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____24425 with
           | (univ_names1,binders1,typ1) ->
               let uu___204_24453 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_24453.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_24453.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_24453.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_24453.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___205_24474 = s  in
          let uu____24475 =
            let uu____24476 =
              let uu____24485 = FStar_List.map (elim_uvars env) sigs  in
              (uu____24485, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____24476  in
          {
            FStar_Syntax_Syntax.sigel = uu____24475;
            FStar_Syntax_Syntax.sigrng =
              (uu___205_24474.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___205_24474.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___205_24474.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___205_24474.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____24502 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24502 with
           | (univ_names1,uu____24520,typ1) ->
               let uu___206_24534 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___206_24534.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___206_24534.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___206_24534.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___206_24534.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____24540 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24540 with
           | (univ_names1,uu____24558,typ1) ->
               let uu___207_24572 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___207_24572.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___207_24572.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___207_24572.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___207_24572.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____24606 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____24606 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____24629 =
                            let uu____24630 =
                              let uu____24631 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____24631  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24630
                             in
                          elim_delayed_subst_term uu____24629  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___208_24634 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___208_24634.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___208_24634.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___208_24634.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___208_24634.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___209_24635 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___209_24635.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___209_24635.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___209_24635.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___209_24635.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___210_24647 = s  in
          let uu____24648 =
            let uu____24649 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____24649  in
          {
            FStar_Syntax_Syntax.sigel = uu____24648;
            FStar_Syntax_Syntax.sigrng =
              (uu___210_24647.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___210_24647.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___210_24647.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___210_24647.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____24653 = elim_uvars_aux_t env us [] t  in
          (match uu____24653 with
           | (us1,uu____24671,t1) ->
               let uu___211_24685 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_24685.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_24685.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_24685.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___211_24685.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24686 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24688 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____24688 with
           | (univs1,binders,signature) ->
               let uu____24716 =
                 let uu____24725 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____24725 with
                 | (univs_opening,univs2) ->
                     let uu____24752 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____24752)
                  in
               (match uu____24716 with
                | (univs_opening,univs_closing) ->
                    let uu____24769 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____24775 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____24776 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____24775, uu____24776)  in
                    (match uu____24769 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____24798 =
                           match uu____24798 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____24816 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____24816 with
                                | (us1,t1) ->
                                    let uu____24827 =
                                      let uu____24832 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____24839 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____24832, uu____24839)  in
                                    (match uu____24827 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____24852 =
                                           let uu____24857 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____24866 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____24857, uu____24866)  in
                                         (match uu____24852 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____24882 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____24882
                                                 in
                                              let uu____24883 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____24883 with
                                               | (uu____24904,uu____24905,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____24920 =
                                                       let uu____24921 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24921
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24920
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____24926 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____24926 with
                           | (uu____24939,uu____24940,t1) -> t1  in
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
                             | uu____25000 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____25017 =
                               let uu____25018 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____25018.FStar_Syntax_Syntax.n  in
                             match uu____25017 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____25077 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____25106 =
                               let uu____25107 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____25107.FStar_Syntax_Syntax.n  in
                             match uu____25106 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____25128) ->
                                 let uu____25149 = destruct_action_body body
                                    in
                                 (match uu____25149 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____25194 ->
                                 let uu____25195 = destruct_action_body t  in
                                 (match uu____25195 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____25244 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____25244 with
                           | (action_univs,t) ->
                               let uu____25253 = destruct_action_typ_templ t
                                  in
                               (match uu____25253 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___212_25294 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___212_25294.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___212_25294.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___213_25296 = ed  in
                           let uu____25297 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____25298 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____25299 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____25300 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____25301 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____25302 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____25303 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____25304 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____25305 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____25306 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____25307 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____25308 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____25309 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____25310 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___213_25296.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___213_25296.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____25297;
                             FStar_Syntax_Syntax.bind_wp = uu____25298;
                             FStar_Syntax_Syntax.if_then_else = uu____25299;
                             FStar_Syntax_Syntax.ite_wp = uu____25300;
                             FStar_Syntax_Syntax.stronger = uu____25301;
                             FStar_Syntax_Syntax.close_wp = uu____25302;
                             FStar_Syntax_Syntax.assert_p = uu____25303;
                             FStar_Syntax_Syntax.assume_p = uu____25304;
                             FStar_Syntax_Syntax.null_wp = uu____25305;
                             FStar_Syntax_Syntax.trivial = uu____25306;
                             FStar_Syntax_Syntax.repr = uu____25307;
                             FStar_Syntax_Syntax.return_repr = uu____25308;
                             FStar_Syntax_Syntax.bind_repr = uu____25309;
                             FStar_Syntax_Syntax.actions = uu____25310;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___213_25296.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___214_25313 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___214_25313.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___214_25313.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___214_25313.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___214_25313.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_25330 =
            match uu___95_25330 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____25357 = elim_uvars_aux_t env us [] t  in
                (match uu____25357 with
                 | (us1,uu____25381,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___215_25400 = sub_eff  in
            let uu____25401 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____25404 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___215_25400.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___215_25400.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____25401;
              FStar_Syntax_Syntax.lift = uu____25404
            }  in
          let uu___216_25407 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___216_25407.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_25407.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_25407.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_25407.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____25417 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____25417 with
           | (univ_names1,binders1,comp1) ->
               let uu___217_25451 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___217_25451.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___217_25451.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___217_25451.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___217_25451.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25462 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25463 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  