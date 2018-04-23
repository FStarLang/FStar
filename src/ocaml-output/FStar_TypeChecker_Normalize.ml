
open Prims
open FStar_Pervasives
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
| DoNotUnfoldPureLets
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
| Unascribe


let uu___is_Beta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Beta -> begin
true
end
| uu____35 -> begin
false
end))


let uu___is_Iota : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____41 -> begin
false
end))


let uu___is_Zeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____47 -> begin
false
end))


let uu___is_Exclude : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
true
end
| uu____54 -> begin
false
end))


let __proj__Exclude__item___0 : step  ->  step = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
_0
end))


let uu___is_Weak : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Weak -> begin
true
end
| uu____67 -> begin
false
end))


let uu___is_HNF : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HNF -> begin
true
end
| uu____73 -> begin
false
end))


let uu___is_Primops : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____79 -> begin
false
end))


let uu___is_Eager_unfolding : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding -> begin
true
end
| uu____85 -> begin
false
end))


let uu___is_Inlining : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____91 -> begin
false
end))


let uu___is_DoNotUnfoldPureLets : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DoNotUnfoldPureLets -> begin
true
end
| uu____97 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____104 -> begin
false
end))


let __proj__UnfoldUntil__item___0 : step  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
_0
end))


let uu___is_UnfoldOnly : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
true
end
| uu____120 -> begin
false
end))


let __proj__UnfoldOnly__item___0 : step  ->  FStar_Ident.lid Prims.list = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
_0
end))


let uu___is_UnfoldFully : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldFully (_0) -> begin
true
end
| uu____142 -> begin
false
end))


let __proj__UnfoldFully__item___0 : step  ->  FStar_Ident.lid Prims.list = (fun projectee -> (match (projectee) with
| UnfoldFully (_0) -> begin
_0
end))


let uu___is_UnfoldAttr : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
true
end
| uu____162 -> begin
false
end))


let __proj__UnfoldAttr__item___0 : step  ->  FStar_Syntax_Syntax.attribute = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
_0
end))


let uu___is_UnfoldTac : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldTac -> begin
true
end
| uu____175 -> begin
false
end))


let uu___is_PureSubtermsWithinComputations : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PureSubtermsWithinComputations -> begin
true
end
| uu____181 -> begin
false
end))


let uu___is_Simplify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simplify -> begin
true
end
| uu____187 -> begin
false
end))


let uu___is_EraseUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EraseUniverses -> begin
true
end
| uu____193 -> begin
false
end))


let uu___is_AllowUnboundUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AllowUnboundUniverses -> begin
true
end
| uu____199 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____205 -> begin
false
end))


let uu___is_CompressUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CompressUvars -> begin
true
end
| uu____211 -> begin
false
end))


let uu___is_NoFullNorm : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoFullNorm -> begin
true
end
| uu____217 -> begin
false
end))


let uu___is_CheckNoUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckNoUvars -> begin
true
end
| uu____223 -> begin
false
end))


let uu___is_Unmeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unmeta -> begin
true
end
| uu____229 -> begin
false
end))


let uu___is_Unascribe : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unascribe -> begin
true
end
| uu____235 -> begin
false
end))


type steps =
step Prims.list


let cases : 'Auu____248 'Auu____249 . ('Auu____248  ->  'Auu____249)  ->  'Auu____249  ->  'Auu____248 FStar_Pervasives_Native.option  ->  'Auu____249 = (fun f d uu___79_269 -> (match (uu___79_269) with
| FStar_Pervasives_Native.Some (x) -> begin
(f x)
end
| FStar_Pervasives_Native.None -> begin
d
end))

type fsteps =
{beta : Prims.bool; iota : Prims.bool; zeta : Prims.bool; weak : Prims.bool; hnf : Prims.bool; primops : Prims.bool; do_not_unfold_pure_lets : Prims.bool; unfold_until : FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option; unfold_only : FStar_Ident.lid Prims.list FStar_Pervasives_Native.option; unfold_fully : FStar_Ident.lid Prims.list FStar_Pervasives_Native.option; unfold_attr : FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option; unfold_tac : Prims.bool; pure_subterms_within_computations : Prims.bool; simplify : Prims.bool; erase_universes : Prims.bool; allow_unbound_universes : Prims.bool; reify_ : Prims.bool; compress_uvars : Prims.bool; no_full_norm : Prims.bool; check_no_uvars : Prims.bool; unmeta : Prims.bool; unascribe : Prims.bool; in_full_norm_request : Prims.bool; weakly_reduce_scrutinee : Prims.bool}


let __proj__Mkfsteps__item__beta : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__beta
end))


let __proj__Mkfsteps__item__iota : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__iota
end))


let __proj__Mkfsteps__item__zeta : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__zeta
end))


let __proj__Mkfsteps__item__weak : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__weak
end))


let __proj__Mkfsteps__item__hnf : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__hnf
end))


let __proj__Mkfsteps__item__primops : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__primops
end))


let __proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__do_not_unfold_pure_lets
end))


let __proj__Mkfsteps__item__unfold_until : fsteps  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unfold_until
end))


let __proj__Mkfsteps__item__unfold_only : fsteps  ->  FStar_Ident.lid Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unfold_only
end))


let __proj__Mkfsteps__item__unfold_fully : fsteps  ->  FStar_Ident.lid Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unfold_fully
end))


let __proj__Mkfsteps__item__unfold_attr : fsteps  ->  FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unfold_attr
end))


let __proj__Mkfsteps__item__unfold_tac : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unfold_tac
end))


let __proj__Mkfsteps__item__pure_subterms_within_computations : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__pure_subterms_within_computations
end))


let __proj__Mkfsteps__item__simplify : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__simplify
end))


let __proj__Mkfsteps__item__erase_universes : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__erase_universes
end))


let __proj__Mkfsteps__item__allow_unbound_universes : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__allow_unbound_universes
end))


let __proj__Mkfsteps__item__reify_ : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__reify_
end))


let __proj__Mkfsteps__item__compress_uvars : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__compress_uvars
end))


let __proj__Mkfsteps__item__no_full_norm : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__no_full_norm
end))


let __proj__Mkfsteps__item__check_no_uvars : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__check_no_uvars
end))


let __proj__Mkfsteps__item__unmeta : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unmeta
end))


let __proj__Mkfsteps__item__unascribe : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unascribe
end))


let __proj__Mkfsteps__item__in_full_norm_request : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__in_full_norm_request
end))


let __proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__weakly_reduce_scrutinee
end))


let default_steps : fsteps = {beta = true; iota = true; zeta = true; weak = false; hnf = false; primops = false; do_not_unfold_pure_lets = false; unfold_until = FStar_Pervasives_Native.None; unfold_only = FStar_Pervasives_Native.None; unfold_fully = FStar_Pervasives_Native.None; unfold_attr = FStar_Pervasives_Native.None; unfold_tac = false; pure_subterms_within_computations = false; simplify = false; erase_universes = false; allow_unbound_universes = false; reify_ = false; compress_uvars = false; no_full_norm = false; check_no_uvars = false; unmeta = false; unascribe = false; in_full_norm_request = false; weakly_reduce_scrutinee = true}


let fstep_add_one : step  ->  fsteps  ->  fsteps = (fun s fs -> (

let add_opt = (fun x uu___80_1503 -> (match (uu___80_1503) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some ((x)::[])
end
| FStar_Pervasives_Native.Some (xs) -> begin
FStar_Pervasives_Native.Some ((x)::xs)
end))
in (match (s) with
| Beta -> begin
(

let uu___98_1523 = fs
in {beta = true; iota = uu___98_1523.iota; zeta = uu___98_1523.zeta; weak = uu___98_1523.weak; hnf = uu___98_1523.hnf; primops = uu___98_1523.primops; do_not_unfold_pure_lets = uu___98_1523.do_not_unfold_pure_lets; unfold_until = uu___98_1523.unfold_until; unfold_only = uu___98_1523.unfold_only; unfold_fully = uu___98_1523.unfold_fully; unfold_attr = uu___98_1523.unfold_attr; unfold_tac = uu___98_1523.unfold_tac; pure_subterms_within_computations = uu___98_1523.pure_subterms_within_computations; simplify = uu___98_1523.simplify; erase_universes = uu___98_1523.erase_universes; allow_unbound_universes = uu___98_1523.allow_unbound_universes; reify_ = uu___98_1523.reify_; compress_uvars = uu___98_1523.compress_uvars; no_full_norm = uu___98_1523.no_full_norm; check_no_uvars = uu___98_1523.check_no_uvars; unmeta = uu___98_1523.unmeta; unascribe = uu___98_1523.unascribe; in_full_norm_request = uu___98_1523.in_full_norm_request; weakly_reduce_scrutinee = uu___98_1523.weakly_reduce_scrutinee})
end
| Iota -> begin
(

let uu___99_1524 = fs
in {beta = uu___99_1524.beta; iota = true; zeta = uu___99_1524.zeta; weak = uu___99_1524.weak; hnf = uu___99_1524.hnf; primops = uu___99_1524.primops; do_not_unfold_pure_lets = uu___99_1524.do_not_unfold_pure_lets; unfold_until = uu___99_1524.unfold_until; unfold_only = uu___99_1524.unfold_only; unfold_fully = uu___99_1524.unfold_fully; unfold_attr = uu___99_1524.unfold_attr; unfold_tac = uu___99_1524.unfold_tac; pure_subterms_within_computations = uu___99_1524.pure_subterms_within_computations; simplify = uu___99_1524.simplify; erase_universes = uu___99_1524.erase_universes; allow_unbound_universes = uu___99_1524.allow_unbound_universes; reify_ = uu___99_1524.reify_; compress_uvars = uu___99_1524.compress_uvars; no_full_norm = uu___99_1524.no_full_norm; check_no_uvars = uu___99_1524.check_no_uvars; unmeta = uu___99_1524.unmeta; unascribe = uu___99_1524.unascribe; in_full_norm_request = uu___99_1524.in_full_norm_request; weakly_reduce_scrutinee = uu___99_1524.weakly_reduce_scrutinee})
end
| Zeta -> begin
(

let uu___100_1525 = fs
in {beta = uu___100_1525.beta; iota = uu___100_1525.iota; zeta = true; weak = uu___100_1525.weak; hnf = uu___100_1525.hnf; primops = uu___100_1525.primops; do_not_unfold_pure_lets = uu___100_1525.do_not_unfold_pure_lets; unfold_until = uu___100_1525.unfold_until; unfold_only = uu___100_1525.unfold_only; unfold_fully = uu___100_1525.unfold_fully; unfold_attr = uu___100_1525.unfold_attr; unfold_tac = uu___100_1525.unfold_tac; pure_subterms_within_computations = uu___100_1525.pure_subterms_within_computations; simplify = uu___100_1525.simplify; erase_universes = uu___100_1525.erase_universes; allow_unbound_universes = uu___100_1525.allow_unbound_universes; reify_ = uu___100_1525.reify_; compress_uvars = uu___100_1525.compress_uvars; no_full_norm = uu___100_1525.no_full_norm; check_no_uvars = uu___100_1525.check_no_uvars; unmeta = uu___100_1525.unmeta; unascribe = uu___100_1525.unascribe; in_full_norm_request = uu___100_1525.in_full_norm_request; weakly_reduce_scrutinee = uu___100_1525.weakly_reduce_scrutinee})
end
| Exclude (Beta) -> begin
(

let uu___101_1526 = fs
in {beta = false; iota = uu___101_1526.iota; zeta = uu___101_1526.zeta; weak = uu___101_1526.weak; hnf = uu___101_1526.hnf; primops = uu___101_1526.primops; do_not_unfold_pure_lets = uu___101_1526.do_not_unfold_pure_lets; unfold_until = uu___101_1526.unfold_until; unfold_only = uu___101_1526.unfold_only; unfold_fully = uu___101_1526.unfold_fully; unfold_attr = uu___101_1526.unfold_attr; unfold_tac = uu___101_1526.unfold_tac; pure_subterms_within_computations = uu___101_1526.pure_subterms_within_computations; simplify = uu___101_1526.simplify; erase_universes = uu___101_1526.erase_universes; allow_unbound_universes = uu___101_1526.allow_unbound_universes; reify_ = uu___101_1526.reify_; compress_uvars = uu___101_1526.compress_uvars; no_full_norm = uu___101_1526.no_full_norm; check_no_uvars = uu___101_1526.check_no_uvars; unmeta = uu___101_1526.unmeta; unascribe = uu___101_1526.unascribe; in_full_norm_request = uu___101_1526.in_full_norm_request; weakly_reduce_scrutinee = uu___101_1526.weakly_reduce_scrutinee})
end
| Exclude (Iota) -> begin
(

let uu___102_1527 = fs
in {beta = uu___102_1527.beta; iota = false; zeta = uu___102_1527.zeta; weak = uu___102_1527.weak; hnf = uu___102_1527.hnf; primops = uu___102_1527.primops; do_not_unfold_pure_lets = uu___102_1527.do_not_unfold_pure_lets; unfold_until = uu___102_1527.unfold_until; unfold_only = uu___102_1527.unfold_only; unfold_fully = uu___102_1527.unfold_fully; unfold_attr = uu___102_1527.unfold_attr; unfold_tac = uu___102_1527.unfold_tac; pure_subterms_within_computations = uu___102_1527.pure_subterms_within_computations; simplify = uu___102_1527.simplify; erase_universes = uu___102_1527.erase_universes; allow_unbound_universes = uu___102_1527.allow_unbound_universes; reify_ = uu___102_1527.reify_; compress_uvars = uu___102_1527.compress_uvars; no_full_norm = uu___102_1527.no_full_norm; check_no_uvars = uu___102_1527.check_no_uvars; unmeta = uu___102_1527.unmeta; unascribe = uu___102_1527.unascribe; in_full_norm_request = uu___102_1527.in_full_norm_request; weakly_reduce_scrutinee = uu___102_1527.weakly_reduce_scrutinee})
end
| Exclude (Zeta) -> begin
(

let uu___103_1528 = fs
in {beta = uu___103_1528.beta; iota = uu___103_1528.iota; zeta = false; weak = uu___103_1528.weak; hnf = uu___103_1528.hnf; primops = uu___103_1528.primops; do_not_unfold_pure_lets = uu___103_1528.do_not_unfold_pure_lets; unfold_until = uu___103_1528.unfold_until; unfold_only = uu___103_1528.unfold_only; unfold_fully = uu___103_1528.unfold_fully; unfold_attr = uu___103_1528.unfold_attr; unfold_tac = uu___103_1528.unfold_tac; pure_subterms_within_computations = uu___103_1528.pure_subterms_within_computations; simplify = uu___103_1528.simplify; erase_universes = uu___103_1528.erase_universes; allow_unbound_universes = uu___103_1528.allow_unbound_universes; reify_ = uu___103_1528.reify_; compress_uvars = uu___103_1528.compress_uvars; no_full_norm = uu___103_1528.no_full_norm; check_no_uvars = uu___103_1528.check_no_uvars; unmeta = uu___103_1528.unmeta; unascribe = uu___103_1528.unascribe; in_full_norm_request = uu___103_1528.in_full_norm_request; weakly_reduce_scrutinee = uu___103_1528.weakly_reduce_scrutinee})
end
| Exclude (uu____1529) -> begin
(failwith "Bad exclude")
end
| Weak -> begin
(

let uu___104_1530 = fs
in {beta = uu___104_1530.beta; iota = uu___104_1530.iota; zeta = uu___104_1530.zeta; weak = true; hnf = uu___104_1530.hnf; primops = uu___104_1530.primops; do_not_unfold_pure_lets = uu___104_1530.do_not_unfold_pure_lets; unfold_until = uu___104_1530.unfold_until; unfold_only = uu___104_1530.unfold_only; unfold_fully = uu___104_1530.unfold_fully; unfold_attr = uu___104_1530.unfold_attr; unfold_tac = uu___104_1530.unfold_tac; pure_subterms_within_computations = uu___104_1530.pure_subterms_within_computations; simplify = uu___104_1530.simplify; erase_universes = uu___104_1530.erase_universes; allow_unbound_universes = uu___104_1530.allow_unbound_universes; reify_ = uu___104_1530.reify_; compress_uvars = uu___104_1530.compress_uvars; no_full_norm = uu___104_1530.no_full_norm; check_no_uvars = uu___104_1530.check_no_uvars; unmeta = uu___104_1530.unmeta; unascribe = uu___104_1530.unascribe; in_full_norm_request = uu___104_1530.in_full_norm_request; weakly_reduce_scrutinee = uu___104_1530.weakly_reduce_scrutinee})
end
| HNF -> begin
(

let uu___105_1531 = fs
in {beta = uu___105_1531.beta; iota = uu___105_1531.iota; zeta = uu___105_1531.zeta; weak = uu___105_1531.weak; hnf = true; primops = uu___105_1531.primops; do_not_unfold_pure_lets = uu___105_1531.do_not_unfold_pure_lets; unfold_until = uu___105_1531.unfold_until; unfold_only = uu___105_1531.unfold_only; unfold_fully = uu___105_1531.unfold_fully; unfold_attr = uu___105_1531.unfold_attr; unfold_tac = uu___105_1531.unfold_tac; pure_subterms_within_computations = uu___105_1531.pure_subterms_within_computations; simplify = uu___105_1531.simplify; erase_universes = uu___105_1531.erase_universes; allow_unbound_universes = uu___105_1531.allow_unbound_universes; reify_ = uu___105_1531.reify_; compress_uvars = uu___105_1531.compress_uvars; no_full_norm = uu___105_1531.no_full_norm; check_no_uvars = uu___105_1531.check_no_uvars; unmeta = uu___105_1531.unmeta; unascribe = uu___105_1531.unascribe; in_full_norm_request = uu___105_1531.in_full_norm_request; weakly_reduce_scrutinee = uu___105_1531.weakly_reduce_scrutinee})
end
| Primops -> begin
(

let uu___106_1532 = fs
in {beta = uu___106_1532.beta; iota = uu___106_1532.iota; zeta = uu___106_1532.zeta; weak = uu___106_1532.weak; hnf = uu___106_1532.hnf; primops = true; do_not_unfold_pure_lets = uu___106_1532.do_not_unfold_pure_lets; unfold_until = uu___106_1532.unfold_until; unfold_only = uu___106_1532.unfold_only; unfold_fully = uu___106_1532.unfold_fully; unfold_attr = uu___106_1532.unfold_attr; unfold_tac = uu___106_1532.unfold_tac; pure_subterms_within_computations = uu___106_1532.pure_subterms_within_computations; simplify = uu___106_1532.simplify; erase_universes = uu___106_1532.erase_universes; allow_unbound_universes = uu___106_1532.allow_unbound_universes; reify_ = uu___106_1532.reify_; compress_uvars = uu___106_1532.compress_uvars; no_full_norm = uu___106_1532.no_full_norm; check_no_uvars = uu___106_1532.check_no_uvars; unmeta = uu___106_1532.unmeta; unascribe = uu___106_1532.unascribe; in_full_norm_request = uu___106_1532.in_full_norm_request; weakly_reduce_scrutinee = uu___106_1532.weakly_reduce_scrutinee})
end
| Eager_unfolding -> begin
fs
end
| Inlining -> begin
fs
end
| DoNotUnfoldPureLets -> begin
(

let uu___107_1533 = fs
in {beta = uu___107_1533.beta; iota = uu___107_1533.iota; zeta = uu___107_1533.zeta; weak = uu___107_1533.weak; hnf = uu___107_1533.hnf; primops = uu___107_1533.primops; do_not_unfold_pure_lets = true; unfold_until = uu___107_1533.unfold_until; unfold_only = uu___107_1533.unfold_only; unfold_fully = uu___107_1533.unfold_fully; unfold_attr = uu___107_1533.unfold_attr; unfold_tac = uu___107_1533.unfold_tac; pure_subterms_within_computations = uu___107_1533.pure_subterms_within_computations; simplify = uu___107_1533.simplify; erase_universes = uu___107_1533.erase_universes; allow_unbound_universes = uu___107_1533.allow_unbound_universes; reify_ = uu___107_1533.reify_; compress_uvars = uu___107_1533.compress_uvars; no_full_norm = uu___107_1533.no_full_norm; check_no_uvars = uu___107_1533.check_no_uvars; unmeta = uu___107_1533.unmeta; unascribe = uu___107_1533.unascribe; in_full_norm_request = uu___107_1533.in_full_norm_request; weakly_reduce_scrutinee = uu___107_1533.weakly_reduce_scrutinee})
end
| UnfoldUntil (d) -> begin
(

let uu___108_1535 = fs
in {beta = uu___108_1535.beta; iota = uu___108_1535.iota; zeta = uu___108_1535.zeta; weak = uu___108_1535.weak; hnf = uu___108_1535.hnf; primops = uu___108_1535.primops; do_not_unfold_pure_lets = uu___108_1535.do_not_unfold_pure_lets; unfold_until = FStar_Pervasives_Native.Some (d); unfold_only = uu___108_1535.unfold_only; unfold_fully = uu___108_1535.unfold_fully; unfold_attr = uu___108_1535.unfold_attr; unfold_tac = uu___108_1535.unfold_tac; pure_subterms_within_computations = uu___108_1535.pure_subterms_within_computations; simplify = uu___108_1535.simplify; erase_universes = uu___108_1535.erase_universes; allow_unbound_universes = uu___108_1535.allow_unbound_universes; reify_ = uu___108_1535.reify_; compress_uvars = uu___108_1535.compress_uvars; no_full_norm = uu___108_1535.no_full_norm; check_no_uvars = uu___108_1535.check_no_uvars; unmeta = uu___108_1535.unmeta; unascribe = uu___108_1535.unascribe; in_full_norm_request = uu___108_1535.in_full_norm_request; weakly_reduce_scrutinee = uu___108_1535.weakly_reduce_scrutinee})
end
| UnfoldOnly (lids) -> begin
(

let uu___109_1539 = fs
in {beta = uu___109_1539.beta; iota = uu___109_1539.iota; zeta = uu___109_1539.zeta; weak = uu___109_1539.weak; hnf = uu___109_1539.hnf; primops = uu___109_1539.primops; do_not_unfold_pure_lets = uu___109_1539.do_not_unfold_pure_lets; unfold_until = uu___109_1539.unfold_until; unfold_only = FStar_Pervasives_Native.Some (lids); unfold_fully = uu___109_1539.unfold_fully; unfold_attr = uu___109_1539.unfold_attr; unfold_tac = uu___109_1539.unfold_tac; pure_subterms_within_computations = uu___109_1539.pure_subterms_within_computations; simplify = uu___109_1539.simplify; erase_universes = uu___109_1539.erase_universes; allow_unbound_universes = uu___109_1539.allow_unbound_universes; reify_ = uu___109_1539.reify_; compress_uvars = uu___109_1539.compress_uvars; no_full_norm = uu___109_1539.no_full_norm; check_no_uvars = uu___109_1539.check_no_uvars; unmeta = uu___109_1539.unmeta; unascribe = uu___109_1539.unascribe; in_full_norm_request = uu___109_1539.in_full_norm_request; weakly_reduce_scrutinee = uu___109_1539.weakly_reduce_scrutinee})
end
| UnfoldFully (lids) -> begin
(

let uu___110_1545 = fs
in {beta = uu___110_1545.beta; iota = uu___110_1545.iota; zeta = uu___110_1545.zeta; weak = uu___110_1545.weak; hnf = uu___110_1545.hnf; primops = uu___110_1545.primops; do_not_unfold_pure_lets = uu___110_1545.do_not_unfold_pure_lets; unfold_until = uu___110_1545.unfold_until; unfold_only = uu___110_1545.unfold_only; unfold_fully = FStar_Pervasives_Native.Some (lids); unfold_attr = uu___110_1545.unfold_attr; unfold_tac = uu___110_1545.unfold_tac; pure_subterms_within_computations = uu___110_1545.pure_subterms_within_computations; simplify = uu___110_1545.simplify; erase_universes = uu___110_1545.erase_universes; allow_unbound_universes = uu___110_1545.allow_unbound_universes; reify_ = uu___110_1545.reify_; compress_uvars = uu___110_1545.compress_uvars; no_full_norm = uu___110_1545.no_full_norm; check_no_uvars = uu___110_1545.check_no_uvars; unmeta = uu___110_1545.unmeta; unascribe = uu___110_1545.unascribe; in_full_norm_request = uu___110_1545.in_full_norm_request; weakly_reduce_scrutinee = uu___110_1545.weakly_reduce_scrutinee})
end
| UnfoldAttr (attr) -> begin
(

let uu___111_1549 = fs
in {beta = uu___111_1549.beta; iota = uu___111_1549.iota; zeta = uu___111_1549.zeta; weak = uu___111_1549.weak; hnf = uu___111_1549.hnf; primops = uu___111_1549.primops; do_not_unfold_pure_lets = uu___111_1549.do_not_unfold_pure_lets; unfold_until = uu___111_1549.unfold_until; unfold_only = uu___111_1549.unfold_only; unfold_fully = uu___111_1549.unfold_fully; unfold_attr = (add_opt attr fs.unfold_attr); unfold_tac = uu___111_1549.unfold_tac; pure_subterms_within_computations = uu___111_1549.pure_subterms_within_computations; simplify = uu___111_1549.simplify; erase_universes = uu___111_1549.erase_universes; allow_unbound_universes = uu___111_1549.allow_unbound_universes; reify_ = uu___111_1549.reify_; compress_uvars = uu___111_1549.compress_uvars; no_full_norm = uu___111_1549.no_full_norm; check_no_uvars = uu___111_1549.check_no_uvars; unmeta = uu___111_1549.unmeta; unascribe = uu___111_1549.unascribe; in_full_norm_request = uu___111_1549.in_full_norm_request; weakly_reduce_scrutinee = uu___111_1549.weakly_reduce_scrutinee})
end
| UnfoldTac -> begin
(

let uu___112_1550 = fs
in {beta = uu___112_1550.beta; iota = uu___112_1550.iota; zeta = uu___112_1550.zeta; weak = uu___112_1550.weak; hnf = uu___112_1550.hnf; primops = uu___112_1550.primops; do_not_unfold_pure_lets = uu___112_1550.do_not_unfold_pure_lets; unfold_until = uu___112_1550.unfold_until; unfold_only = uu___112_1550.unfold_only; unfold_fully = uu___112_1550.unfold_fully; unfold_attr = uu___112_1550.unfold_attr; unfold_tac = true; pure_subterms_within_computations = uu___112_1550.pure_subterms_within_computations; simplify = uu___112_1550.simplify; erase_universes = uu___112_1550.erase_universes; allow_unbound_universes = uu___112_1550.allow_unbound_universes; reify_ = uu___112_1550.reify_; compress_uvars = uu___112_1550.compress_uvars; no_full_norm = uu___112_1550.no_full_norm; check_no_uvars = uu___112_1550.check_no_uvars; unmeta = uu___112_1550.unmeta; unascribe = uu___112_1550.unascribe; in_full_norm_request = uu___112_1550.in_full_norm_request; weakly_reduce_scrutinee = uu___112_1550.weakly_reduce_scrutinee})
end
| PureSubtermsWithinComputations -> begin
(

let uu___113_1551 = fs
in {beta = uu___113_1551.beta; iota = uu___113_1551.iota; zeta = uu___113_1551.zeta; weak = uu___113_1551.weak; hnf = uu___113_1551.hnf; primops = uu___113_1551.primops; do_not_unfold_pure_lets = uu___113_1551.do_not_unfold_pure_lets; unfold_until = uu___113_1551.unfold_until; unfold_only = uu___113_1551.unfold_only; unfold_fully = uu___113_1551.unfold_fully; unfold_attr = uu___113_1551.unfold_attr; unfold_tac = uu___113_1551.unfold_tac; pure_subterms_within_computations = true; simplify = uu___113_1551.simplify; erase_universes = uu___113_1551.erase_universes; allow_unbound_universes = uu___113_1551.allow_unbound_universes; reify_ = uu___113_1551.reify_; compress_uvars = uu___113_1551.compress_uvars; no_full_norm = uu___113_1551.no_full_norm; check_no_uvars = uu___113_1551.check_no_uvars; unmeta = uu___113_1551.unmeta; unascribe = uu___113_1551.unascribe; in_full_norm_request = uu___113_1551.in_full_norm_request; weakly_reduce_scrutinee = uu___113_1551.weakly_reduce_scrutinee})
end
| Simplify -> begin
(

let uu___114_1552 = fs
in {beta = uu___114_1552.beta; iota = uu___114_1552.iota; zeta = uu___114_1552.zeta; weak = uu___114_1552.weak; hnf = uu___114_1552.hnf; primops = uu___114_1552.primops; do_not_unfold_pure_lets = uu___114_1552.do_not_unfold_pure_lets; unfold_until = uu___114_1552.unfold_until; unfold_only = uu___114_1552.unfold_only; unfold_fully = uu___114_1552.unfold_fully; unfold_attr = uu___114_1552.unfold_attr; unfold_tac = uu___114_1552.unfold_tac; pure_subterms_within_computations = uu___114_1552.pure_subterms_within_computations; simplify = true; erase_universes = uu___114_1552.erase_universes; allow_unbound_universes = uu___114_1552.allow_unbound_universes; reify_ = uu___114_1552.reify_; compress_uvars = uu___114_1552.compress_uvars; no_full_norm = uu___114_1552.no_full_norm; check_no_uvars = uu___114_1552.check_no_uvars; unmeta = uu___114_1552.unmeta; unascribe = uu___114_1552.unascribe; in_full_norm_request = uu___114_1552.in_full_norm_request; weakly_reduce_scrutinee = uu___114_1552.weakly_reduce_scrutinee})
end
| EraseUniverses -> begin
(

let uu___115_1553 = fs
in {beta = uu___115_1553.beta; iota = uu___115_1553.iota; zeta = uu___115_1553.zeta; weak = uu___115_1553.weak; hnf = uu___115_1553.hnf; primops = uu___115_1553.primops; do_not_unfold_pure_lets = uu___115_1553.do_not_unfold_pure_lets; unfold_until = uu___115_1553.unfold_until; unfold_only = uu___115_1553.unfold_only; unfold_fully = uu___115_1553.unfold_fully; unfold_attr = uu___115_1553.unfold_attr; unfold_tac = uu___115_1553.unfold_tac; pure_subterms_within_computations = uu___115_1553.pure_subterms_within_computations; simplify = uu___115_1553.simplify; erase_universes = true; allow_unbound_universes = uu___115_1553.allow_unbound_universes; reify_ = uu___115_1553.reify_; compress_uvars = uu___115_1553.compress_uvars; no_full_norm = uu___115_1553.no_full_norm; check_no_uvars = uu___115_1553.check_no_uvars; unmeta = uu___115_1553.unmeta; unascribe = uu___115_1553.unascribe; in_full_norm_request = uu___115_1553.in_full_norm_request; weakly_reduce_scrutinee = uu___115_1553.weakly_reduce_scrutinee})
end
| AllowUnboundUniverses -> begin
(

let uu___116_1554 = fs
in {beta = uu___116_1554.beta; iota = uu___116_1554.iota; zeta = uu___116_1554.zeta; weak = uu___116_1554.weak; hnf = uu___116_1554.hnf; primops = uu___116_1554.primops; do_not_unfold_pure_lets = uu___116_1554.do_not_unfold_pure_lets; unfold_until = uu___116_1554.unfold_until; unfold_only = uu___116_1554.unfold_only; unfold_fully = uu___116_1554.unfold_fully; unfold_attr = uu___116_1554.unfold_attr; unfold_tac = uu___116_1554.unfold_tac; pure_subterms_within_computations = uu___116_1554.pure_subterms_within_computations; simplify = uu___116_1554.simplify; erase_universes = uu___116_1554.erase_universes; allow_unbound_universes = true; reify_ = uu___116_1554.reify_; compress_uvars = uu___116_1554.compress_uvars; no_full_norm = uu___116_1554.no_full_norm; check_no_uvars = uu___116_1554.check_no_uvars; unmeta = uu___116_1554.unmeta; unascribe = uu___116_1554.unascribe; in_full_norm_request = uu___116_1554.in_full_norm_request; weakly_reduce_scrutinee = uu___116_1554.weakly_reduce_scrutinee})
end
| Reify -> begin
(

let uu___117_1555 = fs
in {beta = uu___117_1555.beta; iota = uu___117_1555.iota; zeta = uu___117_1555.zeta; weak = uu___117_1555.weak; hnf = uu___117_1555.hnf; primops = uu___117_1555.primops; do_not_unfold_pure_lets = uu___117_1555.do_not_unfold_pure_lets; unfold_until = uu___117_1555.unfold_until; unfold_only = uu___117_1555.unfold_only; unfold_fully = uu___117_1555.unfold_fully; unfold_attr = uu___117_1555.unfold_attr; unfold_tac = uu___117_1555.unfold_tac; pure_subterms_within_computations = uu___117_1555.pure_subterms_within_computations; simplify = uu___117_1555.simplify; erase_universes = uu___117_1555.erase_universes; allow_unbound_universes = uu___117_1555.allow_unbound_universes; reify_ = true; compress_uvars = uu___117_1555.compress_uvars; no_full_norm = uu___117_1555.no_full_norm; check_no_uvars = uu___117_1555.check_no_uvars; unmeta = uu___117_1555.unmeta; unascribe = uu___117_1555.unascribe; in_full_norm_request = uu___117_1555.in_full_norm_request; weakly_reduce_scrutinee = uu___117_1555.weakly_reduce_scrutinee})
end
| CompressUvars -> begin
(

let uu___118_1556 = fs
in {beta = uu___118_1556.beta; iota = uu___118_1556.iota; zeta = uu___118_1556.zeta; weak = uu___118_1556.weak; hnf = uu___118_1556.hnf; primops = uu___118_1556.primops; do_not_unfold_pure_lets = uu___118_1556.do_not_unfold_pure_lets; unfold_until = uu___118_1556.unfold_until; unfold_only = uu___118_1556.unfold_only; unfold_fully = uu___118_1556.unfold_fully; unfold_attr = uu___118_1556.unfold_attr; unfold_tac = uu___118_1556.unfold_tac; pure_subterms_within_computations = uu___118_1556.pure_subterms_within_computations; simplify = uu___118_1556.simplify; erase_universes = uu___118_1556.erase_universes; allow_unbound_universes = uu___118_1556.allow_unbound_universes; reify_ = uu___118_1556.reify_; compress_uvars = true; no_full_norm = uu___118_1556.no_full_norm; check_no_uvars = uu___118_1556.check_no_uvars; unmeta = uu___118_1556.unmeta; unascribe = uu___118_1556.unascribe; in_full_norm_request = uu___118_1556.in_full_norm_request; weakly_reduce_scrutinee = uu___118_1556.weakly_reduce_scrutinee})
end
| NoFullNorm -> begin
(

let uu___119_1557 = fs
in {beta = uu___119_1557.beta; iota = uu___119_1557.iota; zeta = uu___119_1557.zeta; weak = uu___119_1557.weak; hnf = uu___119_1557.hnf; primops = uu___119_1557.primops; do_not_unfold_pure_lets = uu___119_1557.do_not_unfold_pure_lets; unfold_until = uu___119_1557.unfold_until; unfold_only = uu___119_1557.unfold_only; unfold_fully = uu___119_1557.unfold_fully; unfold_attr = uu___119_1557.unfold_attr; unfold_tac = uu___119_1557.unfold_tac; pure_subterms_within_computations = uu___119_1557.pure_subterms_within_computations; simplify = uu___119_1557.simplify; erase_universes = uu___119_1557.erase_universes; allow_unbound_universes = uu___119_1557.allow_unbound_universes; reify_ = uu___119_1557.reify_; compress_uvars = uu___119_1557.compress_uvars; no_full_norm = true; check_no_uvars = uu___119_1557.check_no_uvars; unmeta = uu___119_1557.unmeta; unascribe = uu___119_1557.unascribe; in_full_norm_request = uu___119_1557.in_full_norm_request; weakly_reduce_scrutinee = uu___119_1557.weakly_reduce_scrutinee})
end
| CheckNoUvars -> begin
(

let uu___120_1558 = fs
in {beta = uu___120_1558.beta; iota = uu___120_1558.iota; zeta = uu___120_1558.zeta; weak = uu___120_1558.weak; hnf = uu___120_1558.hnf; primops = uu___120_1558.primops; do_not_unfold_pure_lets = uu___120_1558.do_not_unfold_pure_lets; unfold_until = uu___120_1558.unfold_until; unfold_only = uu___120_1558.unfold_only; unfold_fully = uu___120_1558.unfold_fully; unfold_attr = uu___120_1558.unfold_attr; unfold_tac = uu___120_1558.unfold_tac; pure_subterms_within_computations = uu___120_1558.pure_subterms_within_computations; simplify = uu___120_1558.simplify; erase_universes = uu___120_1558.erase_universes; allow_unbound_universes = uu___120_1558.allow_unbound_universes; reify_ = uu___120_1558.reify_; compress_uvars = uu___120_1558.compress_uvars; no_full_norm = uu___120_1558.no_full_norm; check_no_uvars = true; unmeta = uu___120_1558.unmeta; unascribe = uu___120_1558.unascribe; in_full_norm_request = uu___120_1558.in_full_norm_request; weakly_reduce_scrutinee = uu___120_1558.weakly_reduce_scrutinee})
end
| Unmeta -> begin
(

let uu___121_1559 = fs
in {beta = uu___121_1559.beta; iota = uu___121_1559.iota; zeta = uu___121_1559.zeta; weak = uu___121_1559.weak; hnf = uu___121_1559.hnf; primops = uu___121_1559.primops; do_not_unfold_pure_lets = uu___121_1559.do_not_unfold_pure_lets; unfold_until = uu___121_1559.unfold_until; unfold_only = uu___121_1559.unfold_only; unfold_fully = uu___121_1559.unfold_fully; unfold_attr = uu___121_1559.unfold_attr; unfold_tac = uu___121_1559.unfold_tac; pure_subterms_within_computations = uu___121_1559.pure_subterms_within_computations; simplify = uu___121_1559.simplify; erase_universes = uu___121_1559.erase_universes; allow_unbound_universes = uu___121_1559.allow_unbound_universes; reify_ = uu___121_1559.reify_; compress_uvars = uu___121_1559.compress_uvars; no_full_norm = uu___121_1559.no_full_norm; check_no_uvars = uu___121_1559.check_no_uvars; unmeta = true; unascribe = uu___121_1559.unascribe; in_full_norm_request = uu___121_1559.in_full_norm_request; weakly_reduce_scrutinee = uu___121_1559.weakly_reduce_scrutinee})
end
| Unascribe -> begin
(

let uu___122_1560 = fs
in {beta = uu___122_1560.beta; iota = uu___122_1560.iota; zeta = uu___122_1560.zeta; weak = uu___122_1560.weak; hnf = uu___122_1560.hnf; primops = uu___122_1560.primops; do_not_unfold_pure_lets = uu___122_1560.do_not_unfold_pure_lets; unfold_until = uu___122_1560.unfold_until; unfold_only = uu___122_1560.unfold_only; unfold_fully = uu___122_1560.unfold_fully; unfold_attr = uu___122_1560.unfold_attr; unfold_tac = uu___122_1560.unfold_tac; pure_subterms_within_computations = uu___122_1560.pure_subterms_within_computations; simplify = uu___122_1560.simplify; erase_universes = uu___122_1560.erase_universes; allow_unbound_universes = uu___122_1560.allow_unbound_universes; reify_ = uu___122_1560.reify_; compress_uvars = uu___122_1560.compress_uvars; no_full_norm = uu___122_1560.no_full_norm; check_no_uvars = uu___122_1560.check_no_uvars; unmeta = uu___122_1560.unmeta; unascribe = true; in_full_norm_request = uu___122_1560.in_full_norm_request; weakly_reduce_scrutinee = uu___122_1560.weakly_reduce_scrutinee})
end)))


let rec to_fsteps : step Prims.list  ->  fsteps = (fun s -> (FStar_List.fold_right fstep_add_one s default_steps))

type psc =
{psc_range : FStar_Range.range; psc_subst : unit  ->  FStar_Syntax_Syntax.subst_t}


let __proj__Mkpsc__item__psc_range : psc  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {psc_range = __fname__psc_range; psc_subst = __fname__psc_subst} -> begin
__fname__psc_range
end))


let __proj__Mkpsc__item__psc_subst : psc  ->  unit  ->  FStar_Syntax_Syntax.subst_t = (fun projectee -> (match (projectee) with
| {psc_range = __fname__psc_range; psc_subst = __fname__psc_subst} -> begin
__fname__psc_subst
end))


let null_psc : psc = {psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1613 -> [])}


let psc_range : psc  ->  FStar_Range.range = (fun psc -> psc.psc_range)


let psc_subst : psc  ->  FStar_Syntax_Syntax.subst_t = (fun psc -> (psc.psc_subst ()))

type primitive_step =
{name : FStar_Ident.lid; arity : Prims.int; auto_reflect : Prims.int FStar_Pervasives_Native.option; strong_reduction_ok : Prims.bool; requires_binder_substitution : Prims.bool; interpretation : psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option}


let __proj__Mkprimitive_step__item__name : primitive_step  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__name
end))


let __proj__Mkprimitive_step__item__arity : primitive_step  ->  Prims.int = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__arity
end))


let __proj__Mkprimitive_step__item__auto_reflect : primitive_step  ->  Prims.int FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__auto_reflect
end))


let __proj__Mkprimitive_step__item__strong_reduction_ok : primitive_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__strong_reduction_ok
end))


let __proj__Mkprimitive_step__item__requires_binder_substitution : primitive_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__requires_binder_substitution
end))


let __proj__Mkprimitive_step__item__interpretation : primitive_step  ->  psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__interpretation
end))

type closure =
| Clos of ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy


let uu___is_Clos : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
true
end
| uu____1902 -> begin
false
end))


let __proj__Clos__item___0 : closure  ->  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool) = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
_0
end))


let uu___is_Univ : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Univ (_0) -> begin
true
end
| uu____2006 -> begin
false
end))


let __proj__Univ__item___0 : closure  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| Univ (_0) -> begin
_0
end))


let uu___is_Dummy : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Dummy -> begin
true
end
| uu____2019 -> begin
false
end))


type env =
(FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list


let dummy : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) = ((FStar_Pervasives_Native.None), (Dummy))

type debug_switches =
{gen : Prims.bool; primop : Prims.bool; b380 : Prims.bool; norm_delayed : Prims.bool; print_normalized : Prims.bool}


let __proj__Mkdebug_switches__item__gen : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380; norm_delayed = __fname__norm_delayed; print_normalized = __fname__print_normalized} -> begin
__fname__gen
end))


let __proj__Mkdebug_switches__item__primop : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380; norm_delayed = __fname__norm_delayed; print_normalized = __fname__print_normalized} -> begin
__fname__primop
end))


let __proj__Mkdebug_switches__item__b380 : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380; norm_delayed = __fname__norm_delayed; print_normalized = __fname__print_normalized} -> begin
__fname__b380
end))


let __proj__Mkdebug_switches__item__norm_delayed : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380; norm_delayed = __fname__norm_delayed; print_normalized = __fname__print_normalized} -> begin
__fname__norm_delayed
end))


let __proj__Mkdebug_switches__item__print_normalized : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380; norm_delayed = __fname__norm_delayed; print_normalized = __fname__print_normalized} -> begin
__fname__print_normalized
end))

type cfg =
{steps : fsteps; tcenv : FStar_TypeChecker_Env.env; debug : debug_switches; delta_level : FStar_TypeChecker_Env.delta_level Prims.list; primitive_steps : primitive_step FStar_Util.psmap; strong : Prims.bool; memoize_lazy : Prims.bool; normalize_pure_lets : Prims.bool}


let __proj__Mkcfg__item__steps : cfg  ->  fsteps = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__steps
end))


let __proj__Mkcfg__item__tcenv : cfg  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__tcenv
end))


let __proj__Mkcfg__item__debug : cfg  ->  debug_switches = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__debug
end))


let __proj__Mkcfg__item__delta_level : cfg  ->  FStar_TypeChecker_Env.delta_level Prims.list = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__delta_level
end))


let __proj__Mkcfg__item__primitive_steps : cfg  ->  primitive_step FStar_Util.psmap = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__primitive_steps
end))


let __proj__Mkcfg__item__strong : cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__strong
end))


let __proj__Mkcfg__item__memoize_lazy : cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__memoize_lazy
end))


let __proj__Mkcfg__item__normalize_pure_lets : cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__normalize_pure_lets
end))


let add_steps : primitive_step FStar_Util.psmap  ->  primitive_step Prims.list  ->  primitive_step FStar_Util.psmap = (fun m l -> (FStar_List.fold_right (fun p m1 -> (

let uu____2330 = (FStar_Ident.text_of_lid p.name)
in (FStar_Util.psmap_add m1 uu____2330 p))) l m))


let prim_from_list : primitive_step Prims.list  ->  primitive_step FStar_Util.psmap = (fun l -> (

let uu____2344 = (FStar_Util.psmap_empty ())
in (add_steps uu____2344 l)))


let find_prim_step : cfg  ->  FStar_Syntax_Syntax.fv  ->  primitive_step FStar_Pervasives_Native.option = (fun cfg fv -> (

let uu____2359 = (FStar_Ident.text_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.psmap_try_find cfg.primitive_steps uu____2359)))


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list

type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * cfg * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option * FStar_Range.range)
| App of (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Cfg of cfg
| Debug of (FStar_Syntax_Syntax.term * FStar_Util.time)


let uu___is_Arg : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
true
end
| uu____2517 -> begin
false
end))


let __proj__Arg__item___0 : stack_elt  ->  (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
_0
end))


let uu___is_UnivArgs : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnivArgs (_0) -> begin
true
end
| uu____2555 -> begin
false
end))


let __proj__UnivArgs__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| UnivArgs (_0) -> begin
_0
end))


let uu___is_MemoLazy : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MemoLazy (_0) -> begin
true
end
| uu____2593 -> begin
false
end))


let __proj__MemoLazy__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| MemoLazy (_0) -> begin
_0
end))


let uu___is_Match : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
true
end
| uu____2666 -> begin
false
end))


let __proj__Match__item___0 : stack_elt  ->  (env * branches * cfg * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
_0
end))


let uu___is_Abs : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
true
end
| uu____2716 -> begin
false
end))


let __proj__Abs__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
_0
end))


let uu___is_App : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| App (_0) -> begin
true
end
| uu____2774 -> begin
false
end))


let __proj__App__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| App (_0) -> begin
_0
end))


let uu___is_Meta : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
true
end
| uu____2818 -> begin
false
end))


let __proj__Meta__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.metadata * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
_0
end))


let uu___is_Let : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
true
end
| uu____2858 -> begin
false
end))


let __proj__Let__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
_0
end))


let uu___is_Cfg : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cfg (_0) -> begin
true
end
| uu____2896 -> begin
false
end))


let __proj__Cfg__item___0 : stack_elt  ->  cfg = (fun projectee -> (match (projectee) with
| Cfg (_0) -> begin
_0
end))


let uu___is_Debug : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
true
end
| uu____2914 -> begin
false
end))


let __proj__Debug__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Util.time) = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
_0
end))


type stack =
stack_elt Prims.list


let head_of : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____2941 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____2941) with
| (hd1, uu____2955) -> begin
hd1
end)))


let mk : 'Auu____2978 . 'Auu____2978  ->  FStar_Range.range  ->  'Auu____2978 FStar_Syntax_Syntax.syntax = (fun t r -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r))


let set_memo : 'a . cfg  ->  'a FStar_Syntax_Syntax.memo  ->  'a  ->  unit = (fun cfg r t -> (match (cfg.memoize_lazy) with
| true -> begin
(

let uu____3041 = (FStar_ST.op_Bang r)
in (match (uu____3041) with
| FStar_Pervasives_Native.Some (uu____3093) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some (t)))
end))
end
| uu____3143 -> begin
()
end))


let rec env_to_string : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list  ->  Prims.string = (fun env -> (

let uu____3169 = (FStar_List.map (fun uu____3183 -> (match (uu____3183) with
| (bopt, c) -> begin
(

let uu____3196 = (match (bopt) with
| FStar_Pervasives_Native.None -> begin
"."
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.binder_to_string x)
end)
in (

let uu____3198 = (closure_to_string c)
in (FStar_Util.format2 "(%s, %s)" uu____3196 uu____3198)))
end)) env)
in (FStar_All.pipe_right uu____3169 (FStar_String.concat "; "))))
and closure_to_string : closure  ->  Prims.string = (fun uu___81_3201 -> (match (uu___81_3201) with
| Clos (env, t, uu____3204, uu____3205) -> begin
(

let uu____3250 = (FStar_All.pipe_right (FStar_List.length env) FStar_Util.string_of_int)
in (

let uu____3257 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(env=%s elts; %s)" uu____3250 uu____3257)))
end
| Univ (uu____3258) -> begin
"Univ"
end
| Dummy -> begin
"dummy"
end))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___82_3263 -> (match (uu___82_3263) with
| Arg (c, uu____3265, uu____3266) -> begin
(

let uu____3267 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" uu____3267))
end
| MemoLazy (uu____3268) -> begin
"MemoLazy"
end
| Abs (uu____3275, bs, uu____3277, uu____3278, uu____3279) -> begin
(

let uu____3284 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" uu____3284))
end
| UnivArgs (uu____3289) -> begin
"UnivArgs"
end
| Match (uu____3296) -> begin
"Match"
end
| App (uu____3305, t, uu____3307, uu____3308) -> begin
(

let uu____3309 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" uu____3309))
end
| Meta (uu____3310, m, uu____3312) -> begin
"Meta"
end
| Let (uu____3313) -> begin
"Let"
end
| Cfg (uu____3322) -> begin
"Cfg"
end
| Debug (t, uu____3324) -> begin
(

let uu____3325 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" uu____3325))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (

let uu____3335 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right uu____3335 (FStar_String.concat "; "))))


let log : cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (match (cfg.debug.gen) with
| true -> begin
(f ())
end
| uu____3355 -> begin
()
end))


let log_primops : cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (match (cfg.debug.primop) with
| true -> begin
(f ())
end
| uu____3371 -> begin
()
end))


let is_empty : 'Auu____3376 . 'Auu____3376 Prims.list  ->  Prims.bool = (fun uu___83_3383 -> (match (uu___83_3383) with
| [] -> begin
true
end
| uu____3386 -> begin
false
end))


let lookup_bvar : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.bv  ->  closure = (fun env x -> (FStar_All.try_with (fun uu___124_3417 -> (match (()) with
| () -> begin
(

let uu____3418 = (FStar_List.nth env x.FStar_Syntax_Syntax.index)
in (FStar_Pervasives_Native.snd uu____3418))
end)) (fun uu___123_3436 -> (match (uu___123_3436) with
| uu____3437 -> begin
(

let uu____3438 = (

let uu____3439 = (FStar_Syntax_Print.db_to_string x)
in (

let uu____3440 = (env_to_string env)
in (FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3439 uu____3440)))
in (failwith uu____3438))
end))))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun l -> (

let uu____3448 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid)
in (match (uu____3448) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Pure_lid)
end
| uu____3451 -> begin
(

let uu____3452 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid)
in (match (uu____3452) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Tot_lid)
end
| uu____3455 -> begin
(

let uu____3456 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid)
in (match (uu____3456) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_PURE_lid)
end
| uu____3459 -> begin
FStar_Pervasives_Native.None
end))
end))
end)))


let norm_universe : cfg  ->  env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us1 = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let uu____3490 = (FStar_List.fold_left (fun uu____3516 u1 -> (match (uu____3516) with
| (cur_kernel, cur_max, out) -> begin
(

let uu____3541 = (FStar_Syntax_Util.univ_kernel u1)
in (match (uu____3541) with
| (k_u, n1) -> begin
(

let uu____3556 = (FStar_Syntax_Util.eq_univs cur_kernel k_u)
in (match (uu____3556) with
| true -> begin
((cur_kernel), (u1), (out))
end
| uu____3567 -> begin
((k_u), (u1), ((cur_max)::out))
end))
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us1)
in (match (uu____3490) with
| (uu____3574, u1, out) -> begin
(FStar_List.rev ((u1)::out))
end))))
in (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun uu___126_3598 -> (match (()) with
| () -> begin
(

let uu____3601 = (

let uu____3602 = (FStar_List.nth env x)
in (FStar_Pervasives_Native.snd uu____3602))
in (match (uu____3601) with
| Univ (u3) -> begin
(aux u3)
end
| Dummy -> begin
(u2)::[]
end
| uu____3620 -> begin
(failwith "Impossible: universe variable bound to a term")
end))
end)) (fun uu___125_3625 -> (match (uu___125_3625) with
| uu____3628 -> begin
(match (cfg.steps.allow_unbound_universes) with
| true -> begin
(FStar_Syntax_Syntax.U_unknown)::[]
end
| uu____3631 -> begin
(failwith "Universe variable not found")
end)
end)))
end
| FStar_Syntax_Syntax.U_unif (uu____3634) when cfg.steps.check_no_uvars -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_zero -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unif (uu____3643) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_name (uu____3652) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unknown -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_max ([]) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let us1 = (

let uu____3659 = (FStar_List.collect aux us)
in (FStar_All.pipe_right uu____3659 norm_univs))
in (match (us1) with
| (u_k)::(hd1)::rest -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3676 = (FStar_Syntax_Util.univ_kernel u_k)
in (match (uu____3676) with
| (FStar_Syntax_Syntax.U_zero, n1) -> begin
(

let uu____3684 = (FStar_All.pipe_right rest1 (FStar_List.for_all (fun u3 -> (

let uu____3692 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____3692) with
| (uu____3697, m) -> begin
(n1 <= m)
end)))))
in (match (uu____3684) with
| true -> begin
rest1
end
| uu____3701 -> begin
us1
end))
end
| uu____3702 -> begin
us1
end)))
end
| uu____3707 -> begin
us1
end))
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____3711 = (aux u3)
in (FStar_List.map (fun _0_17 -> FStar_Syntax_Syntax.U_succ (_0_17)) uu____3711))
end)))
in (match (cfg.steps.erase_universes) with
| true -> begin
FStar_Syntax_Syntax.U_unknown
end
| uu____3714 -> begin
(

let uu____3715 = (aux u)
in (match (uu____3715) with
| [] -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::[] -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::(u1)::[] -> begin
u1
end
| (FStar_Syntax_Syntax.U_zero)::us -> begin
FStar_Syntax_Syntax.U_max (us)
end
| (u1)::[] -> begin
u1
end
| us -> begin
FStar_Syntax_Syntax.U_max (us)
end))
end))))


let rec inline_closure_env : cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env stack t -> ((log cfg (fun uu____3857 -> (

let uu____3858 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____3859 = (env_to_string env)
in (

let uu____3860 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n" uu____3858 uu____3859 uu____3860))))));
(match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation cfg.steps.compress_uvars) -> begin
(rebuild_closure cfg env stack t)
end
| uu____3869 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3872) -> begin
(

let uu____3897 = (FStar_Syntax_Subst.compress t)
in (inline_closure_env cfg env stack uu____3897))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_constant (uu____3898) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_name (uu____3899) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_lazy (uu____3900) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____3901) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3902) -> begin
(match (cfg.steps.check_no_uvars) with
| true -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____3908) -> begin
(

let uu____3909 = (

let uu____3910 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____3911 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s): CheckNoUvars: Unexpected unification variable remains: %s" uu____3910 uu____3911)))
in (failwith uu____3909))
end
| uu____3914 -> begin
(inline_closure_env cfg env stack t1)
end))
end
| uu____3915 -> begin
(rebuild_closure cfg env stack t)
end)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let t1 = (

let uu____3920 = (

let uu____3921 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (uu____3921))
in (mk uu____3920 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let t1 = (

let uu____3929 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3929))
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____3931 = (lookup_bvar env x)
in (match (uu____3931) with
| Univ (uu____3934) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(

let x1 = (

let uu___127_3938 = x
in {FStar_Syntax_Syntax.ppname = uu___127_3938.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___127_3938.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun})
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_bvar (x1)) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))
end
| Clos (env1, t0, uu____3944, uu____3945) -> begin
(inline_closure_env cfg env1 stack t0)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____4030 stack1 -> (match (uu____4030) with
| (a, aq) -> begin
(

let uu____4042 = (

let uu____4043 = (

let uu____4050 = (

let uu____4051 = (

let uu____4082 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____4082), (false)))
in Clos (uu____4051))
in ((uu____4050), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (uu____4043))
in (uu____4042)::stack1)
end)) args))
in (inline_closure_env cfg env stack1 head1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let env' = (FStar_All.pipe_right env (FStar_List.fold_right (fun _b env1 -> (((FStar_Pervasives_Native.None), (Dummy)))::env1) bs))
in (

let stack1 = (Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack
in (inline_closure_env cfg env' stack1 body)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4266 = (close_binders cfg env bs)
in (match (uu____4266) with
| (bs1, env') -> begin
(

let c1 = (close_comp cfg env' c)
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_arrow (((bs1), (c1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____4313 = (

let uu____4324 = (

let uu____4327 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4327)::[])
in (close_binders cfg env uu____4324))
in (match (uu____4313) with
| (x1, env1) -> begin
(

let phi1 = (non_tail_inline_closure_env cfg env1 phi)
in (

let t1 = (

let uu____4350 = (

let uu____4351 = (

let uu____4358 = (

let uu____4359 = (FStar_List.hd x1)
in (FStar_All.pipe_right uu____4359 FStar_Pervasives_Native.fst))
in ((uu____4358), (phi1)))
in FStar_Syntax_Syntax.Tm_refine (uu____4351))
in (mk uu____4350 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env1 stack t1)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, (annot, tacopt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____4450 = (non_tail_inline_closure_env cfg env t2)
in FStar_Util.Inl (uu____4450))
end
| FStar_Util.Inr (c) -> begin
(

let uu____4464 = (close_comp cfg env c)
in FStar_Util.Inr (uu____4464))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (non_tail_inline_closure_env cfg env))
in (

let t2 = (

let uu____4483 = (

let uu____4484 = (

let uu____4511 = (non_tail_inline_closure_env cfg env t1)
in ((uu____4511), (((annot1), (tacopt1))), (lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____4484))
in (mk uu____4483 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env stack t2))))
end
| FStar_Syntax_Syntax.Tm_quoted (t', qi) -> begin
(

let t1 = (match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____4557 = (

let uu____4558 = (

let uu____4565 = (non_tail_inline_closure_env cfg env t')
in ((uu____4565), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____4558))
in (mk uu____4557 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (non_tail_inline_closure_env cfg env) qi)
in (mk (FStar_Syntax_Syntax.Tm_quoted (((t'), (qi1)))) t.FStar_Syntax_Syntax.pos))
end)
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(

let stack1 = (Meta (((env), (m), (t.FStar_Syntax_Syntax.pos))))::stack
in (inline_closure_env cfg env stack1 t'))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env1 = (FStar_List.fold_left (fun env1 uu____4617 -> (dummy)::env1) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (non_tail_inline_closure_env cfg env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (non_tail_inline_closure_env cfg env1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____4638 = (

let uu____4649 = (FStar_Syntax_Syntax.is_top_level ((lb)::[]))
in (match (uu____4649) with
| true -> begin
((lb.FStar_Syntax_Syntax.lbname), (body))
end
| uu____4666 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4668 = (non_tail_inline_closure_env cfg ((dummy)::env0) body)
in ((FStar_Util.Inl ((

let uu___128_4684 = x
in {FStar_Syntax_Syntax.ppname = uu___128_4684.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___128_4684.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = typ}))), (uu____4668))))
end))
in (match (uu____4638) with
| (nm, body1) -> begin
(

let lb1 = (

let uu___129_4702 = lb
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___129_4702.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___129_4702.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___129_4702.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___129_4702.FStar_Syntax_Syntax.lbpos})
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (body1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env0 stack t1)))
end))))))
end
| FStar_Syntax_Syntax.Tm_let ((uu____4716, lbs), body) -> begin
(

let norm_one_lb = (fun env1 lb -> (

let env_univs = (FStar_List.fold_right (fun uu____4779 env2 -> (dummy)::env2) lb.FStar_Syntax_Syntax.lbunivs env1)
in (

let env2 = (

let uu____4804 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____4804) with
| true -> begin
env_univs
end
| uu____4813 -> begin
(FStar_List.fold_right (fun uu____4824 env2 -> (dummy)::env2) lbs env_univs)
end))
in (

let ty = (non_tail_inline_closure_env cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (

let nm = (

let uu____4848 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____4848) with
| true -> begin
lb.FStar_Syntax_Syntax.lbname
end
| uu____4853 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in FStar_Util.Inl ((

let uu___130_4856 = x
in {FStar_Syntax_Syntax.ppname = uu___130_4856.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___130_4856.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
end))
in (

let uu___131_4857 = lb
in (

let uu____4858 = (non_tail_inline_closure_env cfg env2 lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___131_4857.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___131_4857.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____4858; FStar_Syntax_Syntax.lbattrs = uu___131_4857.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___131_4857.FStar_Syntax_Syntax.lbpos})))))))
in (

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body1 = (

let body_env = (FStar_List.fold_right (fun uu____4890 env1 -> (dummy)::env1) lbs1 env)
in (non_tail_inline_closure_env cfg body_env body))
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs1))), (body1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack1 = (Match (((env), (branches), (cfg), (t.FStar_Syntax_Syntax.pos))))::stack
in (inline_closure_env cfg env stack1 head1))
end)
end);
))
and non_tail_inline_closure_env : cfg  ->  env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env t -> (inline_closure_env cfg env [] t))
and rebuild_closure : cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env stack t -> ((log cfg (fun uu____4977 -> (

let uu____4978 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____4979 = (env_to_string env)
in (

let uu____4980 = (stack_to_string stack)
in (

let uu____4981 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print4 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n" uu____4978 uu____4979 uu____4980 uu____4981)))))));
(match (stack) with
| [] -> begin
t
end
| (Arg (Clos (env_arg, tm, uu____4986, uu____4987), aq, r))::stack1 -> begin
(

let stack2 = (App (((env), (t), (aq), (r))))::stack1
in (inline_closure_env cfg env_arg stack2 tm))
end
| (App (env1, head1, aq, r))::stack1 -> begin
(

let t1 = (FStar_Syntax_Syntax.extend_app head1 ((t), (aq)) FStar_Pervasives_Native.None r)
in (rebuild_closure cfg env1 stack1 t1))
end
| (Abs (env', bs, env'', lopt, r))::stack1 -> begin
(

let uu____5064 = (close_binders cfg env' bs)
in (match (uu____5064) with
| (bs1, uu____5078) -> begin
(

let lopt1 = (close_lcomp_opt cfg env'' lopt)
in (

let uu____5094 = (

let uu___132_5095 = (FStar_Syntax_Util.abs bs1 t lopt1)
in {FStar_Syntax_Syntax.n = uu___132_5095.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___132_5095.FStar_Syntax_Syntax.vars})
in (rebuild_closure cfg env stack1 uu____5094)))
end))
end
| (Match (env1, branches, cfg1, r))::stack1 -> begin
(

let close_one_branch = (fun env2 uu____5151 -> (match (uu____5151) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env3 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____5266) -> begin
((p), (env3))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____5295 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____5379 uu____5380 -> (match (((uu____5379), (uu____5380))) with
| ((pats1, env4), (p1, b)) -> begin
(

let uu____5519 = (norm_pat env4 p1)
in (match (uu____5519) with
| (p2, env5) -> begin
(((((p2), (b)))::pats1), (env5))
end))
end)) (([]), (env3))))
in (match (uu____5295) with
| (pats1, env4) -> begin
(((

let uu___133_5681 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___133_5681.FStar_Syntax_Syntax.p})), (env4))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___134_5700 = x
in (

let uu____5701 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___134_5700.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___134_5700.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5701}))
in (((

let uu___135_5715 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___135_5715.FStar_Syntax_Syntax.p})), ((dummy)::env3)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___136_5726 = x
in (

let uu____5727 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___136_5726.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___136_5726.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5727}))
in (((

let uu___137_5741 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___137_5741.FStar_Syntax_Syntax.p})), ((dummy)::env3)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t1) -> begin
(

let x1 = (

let uu___138_5757 = x
in (

let uu____5758 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___138_5757.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___138_5757.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5758}))
in (

let t2 = (non_tail_inline_closure_env cfg1 env3 t1)
in (((

let uu___139_5775 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t2))); FStar_Syntax_Syntax.p = uu___139_5775.FStar_Syntax_Syntax.p})), (env3))))
end))
in (

let uu____5780 = (norm_pat env2 pat)
in (match (uu____5780) with
| (pat1, env3) -> begin
(

let w_opt1 = (match (w_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____5849 = (non_tail_inline_closure_env cfg1 env3 w)
in FStar_Pervasives_Native.Some (uu____5849))
end)
in (

let tm1 = (non_tail_inline_closure_env cfg1 env3 tm)
in ((pat1), (w_opt1), (tm1))))
end)))
end))
in (

let t1 = (

let uu____5868 = (

let uu____5869 = (

let uu____5892 = (FStar_All.pipe_right branches (FStar_List.map (close_one_branch env1)))
in ((t), (uu____5892)))
in FStar_Syntax_Syntax.Tm_match (uu____5869))
in (mk uu____5868 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg1 env1 stack1 t1)))
end
| (Meta (env_m, m, r))::stack1 -> begin
(

let m1 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let uu____5989 = (FStar_All.pipe_right args (FStar_List.map (fun args1 -> (FStar_All.pipe_right args1 (FStar_List.map (fun uu____6078 -> (match (uu____6078) with
| (a, q) -> begin
(

let uu____6097 = (non_tail_inline_closure_env cfg env_m a)
in ((uu____6097), (q)))
end)))))))
in FStar_Syntax_Syntax.Meta_pattern (uu____5989))
end
| FStar_Syntax_Syntax.Meta_monadic (m1, tbody) -> begin
(

let uu____6108 = (

let uu____6115 = (non_tail_inline_closure_env cfg env_m tbody)
in ((m1), (uu____6115)))
in FStar_Syntax_Syntax.Meta_monadic (uu____6108))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody) -> begin
(

let uu____6127 = (

let uu____6136 = (non_tail_inline_closure_env cfg env_m tbody)
in ((m1), (m2), (uu____6136)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____6127))
end
| uu____6141 -> begin
m
end)
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m1)))) r)
in (rebuild_closure cfg env stack1 t1)))
end
| uu____6147 -> begin
(failwith "Impossible: unexpected stack element")
end);
))
and close_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * env) = (fun cfg env bs -> (

let uu____6157 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____6230 uu____6231 -> (match (((uu____6230), (uu____6231))) with
| ((env1, out), (b, imp)) -> begin
(

let b1 = (

let uu___140_6349 = b
in (

let uu____6350 = (inline_closure_env cfg env1 [] b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___140_6349.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_6349.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6350}))
in (

let env2 = (dummy)::env1
in ((env2), ((((b1), (imp)))::out))))
end)) ((env), ([]))))
in (match (uu____6157) with
| (env1, bs1) -> begin
(((FStar_List.rev bs1)), (env1))
end)))
and close_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation cfg.steps.compress_uvars) -> begin
c
end
| uu____6467 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____6480 = (inline_closure_env cfg env [] t)
in (

let uu____6481 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____6480 uu____6481)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____6494 = (inline_closure_env cfg env [] t)
in (

let uu____6495 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____6494 uu____6495)))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let rt = (inline_closure_env cfg env [] c1.FStar_Syntax_Syntax.result_typ)
in (

let args = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun uu____6541 -> (match (uu____6541) with
| (a, q) -> begin
(

let uu____6554 = (inline_closure_env cfg env [] a)
in ((uu____6554), (q)))
end))))
in (

let flags1 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___84_6569 -> (match (uu___84_6569) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____6573 = (inline_closure_env cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____6573))
end
| f -> begin
f
end))))
in (

let uu____6577 = (

let uu___141_6578 = c1
in (

let uu____6579 = (FStar_List.map (norm_universe cfg env) c1.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = uu____6579; FStar_Syntax_Syntax.effect_name = uu___141_6578.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags1}))
in (FStar_Syntax_Syntax.mk_Comp uu____6577)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun flags1 -> (FStar_All.pipe_right flags1 (FStar_List.filter (fun uu___85_6589 -> (match (uu___85_6589) with
| FStar_Syntax_Syntax.DECREASES (uu____6590) -> begin
false
end
| uu____6593 -> begin
true
end)))))
and close_lcomp_opt : cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags1 = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.filter (fun uu___86_6611 -> (match (uu___86_6611) with
| FStar_Syntax_Syntax.DECREASES (uu____6612) -> begin
false
end
| uu____6615 -> begin
true
end))))
in (

let rc1 = (

let uu___142_6617 = rc
in (

let uu____6618 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inline_closure_env cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___142_6617.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____6618; FStar_Syntax_Syntax.residual_flags = flags1}))
in FStar_Pervasives_Native.Some (rc1)))
end
| uu____6627 -> begin
lopt
end))


let closure_as_term : cfg  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (non_tail_inline_closure_env cfg env t))


let built_in_primitive_steps : primitive_step FStar_Util.psmap = (

let arg_as_int = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_int)))
in (

let arg_as_bool = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_bool)))
in (

let arg_as_char = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_char)))
in (

let arg_as_string = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_string)))
in (

let arg_as_list = (fun e a -> (

let uu____6732 = (

let uu____6741 = (FStar_Syntax_Embeddings.e_list e)
in (FStar_Syntax_Embeddings.try_unembed uu____6741))
in (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6732)))
in (

let arg_as_bounded_int = (fun uu____6767 -> (match (uu____6767) with
| (a, uu____6779) -> begin
(

let uu____6786 = (

let uu____6787 = (FStar_Syntax_Subst.compress a)
in uu____6787.FStar_Syntax_Syntax.n)
in (match (uu____6786) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.pos = uu____6797; FStar_Syntax_Syntax.vars = uu____6798}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)); FStar_Syntax_Syntax.pos = uu____6800; FStar_Syntax_Syntax.vars = uu____6801}, uu____6802))::[]) when (

let uu____6841 = (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.ends_with uu____6841 "int_to_t")) -> begin
(

let uu____6842 = (

let uu____6847 = (FStar_BigInt.big_int_of_string i)
in ((fv1), (uu____6847)))
in FStar_Pervasives_Native.Some (uu____6842))
end
| uu____6852 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let lift_unary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a))::[] -> begin
(

let uu____6900 = (f a)
in FStar_Pervasives_Native.Some (uu____6900))
end
| uu____6901 -> begin
FStar_Pervasives_Native.None
end))
in (

let lift_binary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a0))::(FStar_Pervasives_Native.Some (a1))::[] -> begin
(

let uu____6957 = (f a0 a1)
in FStar_Pervasives_Native.Some (uu____6957))
end
| uu____6958 -> begin
FStar_Pervasives_Native.None
end))
in (

let unary_op = (fun as_a f res args -> (

let uu____7016 = (FStar_List.map as_a args)
in (lift_unary (f res.psc_range) uu____7016)))
in (

let binary_op = (fun as_a f res args -> (

let uu____7087 = (FStar_List.map as_a args)
in (lift_binary (f res.psc_range) uu____7087)))
in (

let as_primitive_step = (fun is_strong uu____7124 -> (match (uu____7124) with
| (l, arity, f) -> begin
{name = l; arity = arity; auto_reflect = FStar_Pervasives_Native.None; strong_reduction_ok = is_strong; requires_binder_substitution = false; interpretation = f}
end))
in (

let unary_int_op = (fun f -> (unary_op arg_as_int (fun r x -> (

let uu____7184 = (f x)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r uu____7184)))))
in (

let binary_int_op = (fun f -> (binary_op arg_as_int (fun r x y -> (

let uu____7220 = (f x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r uu____7220)))))
in (

let unary_bool_op = (fun f -> (unary_op arg_as_bool (fun r x -> (

let uu____7249 = (f x)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____7249)))))
in (

let binary_bool_op = (fun f -> (binary_op arg_as_bool (fun r x y -> (

let uu____7285 = (f x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____7285)))))
in (

let binary_string_op = (fun f -> (binary_op arg_as_string (fun r x y -> (

let uu____7321 = (f x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r uu____7321)))))
in (

let mixed_binary_op = (fun as_a as_b embed_c f res args -> (match (args) with
| (a)::(b)::[] -> begin
(

let uu____7453 = (

let uu____7462 = (as_a a)
in (

let uu____7465 = (as_b b)
in ((uu____7462), (uu____7465))))
in (match (uu____7453) with
| (FStar_Pervasives_Native.Some (a1), FStar_Pervasives_Native.Some (b1)) -> begin
(

let uu____7480 = (

let uu____7481 = (f res.psc_range a1 b1)
in (embed_c res.psc_range uu____7481))
in FStar_Pervasives_Native.Some (uu____7480))
end
| uu____7482 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7491 -> begin
FStar_Pervasives_Native.None
end))
in (

let list_of_string' = (fun rng s -> (

let name = (fun l -> (

let uu____7511 = (

let uu____7512 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____7512))
in (mk uu____7511 rng)))
in (

let char_t = (name FStar_Parser_Const.char_lid)
in (

let charterm = (fun c -> (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))) rng))
in (

let uu____7524 = (

let uu____7527 = (FStar_String.list_of_string s)
in (FStar_List.map charterm uu____7527))
in (FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7524))))))
in (

let string_of_list' = (fun rng l -> (

let s = (FStar_String.string_of_list l)
in (FStar_Syntax_Util.exp_string s)))
in (

let string_compare' = (fun rng s1 s2 -> (

let r = (FStar_String.compare s1 s2)
in (

let uu____7571 = (

let uu____7572 = (FStar_Util.string_of_int r)
in (FStar_BigInt.big_int_of_string uu____7572))
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng uu____7571))))
in (

let string_concat' = (fun psc args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7594 = (arg_as_string a1)
in (match (uu____7594) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____7600 = (arg_as_list FStar_Syntax_Embeddings.e_string a2)
in (match (uu____7600) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.concat s1 s2)
in (

let uu____7613 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____7613)))
end
| uu____7614 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7619 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7622 -> begin
FStar_Pervasives_Native.None
end))
in (

let string_of_int1 = (fun rng i -> (

let uu____7636 = (FStar_BigInt.string_of_big_int i)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng uu____7636)))
in (

let string_of_bool1 = (fun rng b -> (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng (match (b) with
| true -> begin
"true"
end
| uu____7648 -> begin
"false"
end)))
in (

let mk_range1 = (fun psc args -> (match (args) with
| (fn)::(from_line)::(from_col)::(to_line)::(to_col)::[] -> begin
(

let uu____7673 = (

let uu____7694 = (arg_as_string fn)
in (

let uu____7697 = (arg_as_int from_line)
in (

let uu____7700 = (arg_as_int from_col)
in (

let uu____7703 = (arg_as_int to_line)
in (

let uu____7706 = (arg_as_int to_col)
in ((uu____7694), (uu____7697), (uu____7700), (uu____7703), (uu____7706)))))))
in (match (uu____7673) with
| (FStar_Pervasives_Native.Some (fn1), FStar_Pervasives_Native.Some (from_l), FStar_Pervasives_Native.Some (from_c), FStar_Pervasives_Native.Some (to_l), FStar_Pervasives_Native.Some (to_c)) -> begin
(

let r = (

let uu____7737 = (

let uu____7738 = (FStar_BigInt.to_int_fs from_l)
in (

let uu____7739 = (FStar_BigInt.to_int_fs from_c)
in (FStar_Range.mk_pos uu____7738 uu____7739)))
in (

let uu____7740 = (

let uu____7741 = (FStar_BigInt.to_int_fs to_l)
in (

let uu____7742 = (FStar_BigInt.to_int_fs to_c)
in (FStar_Range.mk_pos uu____7741 uu____7742)))
in (FStar_Range.mk_range fn1 uu____7737 uu____7740)))
in (

let uu____7743 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____7743)))
end
| uu____7744 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7765 -> begin
FStar_Pervasives_Native.None
end))
in (

let decidable_eq = (fun neg psc args -> (

let r = psc.psc_range
in (

let tru = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) r)
in (

let fal = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) r)
in (match (args) with
| ((_typ, uu____7798))::((a1, uu____7800))::((a2, uu____7802))::[] -> begin
(

let uu____7839 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____7839) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
fal
end
| uu____7842 -> begin
tru
end))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
tru
end
| uu____7843 -> begin
fal
end))
end
| uu____7844 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7845 -> begin
(failwith "Unexpected number of arguments")
end)))))
in (

let prims_to_fstar_range_step = (fun psc args -> (match (args) with
| ((a1, uu____7876))::[] -> begin
(

let uu____7885 = (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range a1)
in (match (uu____7885) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____7891 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____7891))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7892 -> begin
(failwith "Unexpected number of arguments")
end))
in (

let basic_ops = (

let uu____7918 = (

let uu____7935 = (

let uu____7952 = (

let uu____7969 = (

let uu____7986 = (

let uu____8003 = (

let uu____8020 = (

let uu____8037 = (

let uu____8054 = (

let uu____8071 = (

let uu____8088 = (

let uu____8105 = (

let uu____8122 = (

let uu____8139 = (

let uu____8156 = (

let uu____8173 = (

let uu____8190 = (

let uu____8207 = (

let uu____8224 = (

let uu____8241 = (

let uu____8258 = (

let uu____8275 = (

let uu____8290 = (FStar_Parser_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((uu____8290), ((Prims.parse_int "1")), ((unary_op arg_as_string list_of_string'))))
in (

let uu____8299 = (

let uu____8316 = (

let uu____8331 = (FStar_Parser_Const.p2l (("FStar")::("String")::("string_of_list")::[]))
in ((uu____8331), ((Prims.parse_int "1")), ((unary_op (arg_as_list FStar_Syntax_Embeddings.e_char) string_of_list'))))
in (

let uu____8344 = (

let uu____8361 = (

let uu____8376 = (FStar_Parser_Const.p2l (("FStar")::("String")::("concat")::[]))
in ((uu____8376), ((Prims.parse_int "2")), (string_concat')))
in (

let uu____8387 = (

let uu____8404 = (

let uu____8419 = (FStar_Parser_Const.p2l (("Prims")::("mk_range")::[]))
in ((uu____8419), ((Prims.parse_int "5")), (mk_range1)))
in (uu____8404)::[])
in (uu____8361)::uu____8387))
in (uu____8316)::uu____8344))
in (uu____8275)::uu____8299))
in (((FStar_Parser_Const.op_notEq), ((Prims.parse_int "3")), ((decidable_eq true))))::uu____8258)
in (((FStar_Parser_Const.op_Eq), ((Prims.parse_int "3")), ((decidable_eq false))))::uu____8241)
in (((FStar_Parser_Const.string_compare), ((Prims.parse_int "2")), ((binary_op arg_as_string string_compare'))))::uu____8224)
in (((FStar_Parser_Const.string_of_bool_lid), ((Prims.parse_int "1")), ((unary_op arg_as_bool string_of_bool1))))::uu____8207)
in (((FStar_Parser_Const.string_of_int_lid), ((Prims.parse_int "1")), ((unary_op arg_as_int string_of_int1))))::uu____8190)
in (((FStar_Parser_Const.str_make_lid), ((Prims.parse_int "2")), ((mixed_binary_op arg_as_int arg_as_char (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string) (fun r x y -> (

let uu____8641 = (FStar_BigInt.to_int_fs x)
in (FStar_String.make uu____8641 y)))))))::uu____8173)
in (((FStar_Parser_Const.strcat_lid'), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____8156)
in (((FStar_Parser_Const.strcat_lid), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____8139)
in (((FStar_Parser_Const.op_Or), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x || y))))))::uu____8122)
in (((FStar_Parser_Const.op_And), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x && y))))))::uu____8105)
in (((FStar_Parser_Const.op_Negation), ((Prims.parse_int "1")), ((unary_bool_op (fun x -> (not (x)))))))::uu____8088)
in (((FStar_Parser_Const.op_Modulus), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.mod_big_int x y))))))::uu____8071)
in (((FStar_Parser_Const.op_GTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____8836 = (FStar_BigInt.ge_big_int x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____8836)))))))::uu____8054)
in (((FStar_Parser_Const.op_GT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____8866 = (FStar_BigInt.gt_big_int x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____8866)))))))::uu____8037)
in (((FStar_Parser_Const.op_LTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____8896 = (FStar_BigInt.le_big_int x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____8896)))))))::uu____8020)
in (((FStar_Parser_Const.op_LT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____8926 = (FStar_BigInt.lt_big_int x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____8926)))))))::uu____8003)
in (((FStar_Parser_Const.op_Division), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.div_big_int x y))))))::uu____7986)
in (((FStar_Parser_Const.op_Multiply), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.mult_big_int x y))))))::uu____7969)
in (((FStar_Parser_Const.op_Subtraction), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.sub_big_int x y))))))::uu____7952)
in (((FStar_Parser_Const.op_Addition), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.add_big_int x y))))))::uu____7935)
in (((FStar_Parser_Const.op_Minus), ((Prims.parse_int "1")), ((unary_int_op (fun x -> (FStar_BigInt.minus_big_int x))))))::uu____7918)
in (

let weak_ops = (

let uu____9087 = (

let uu____9108 = (FStar_Parser_Const.p2l (("FStar")::("Range")::("prims_to_fstar_range")::[]))
in ((uu____9108), ((Prims.parse_int "1")), (prims_to_fstar_range_step)))
in (uu____9087)::[])
in (

let bounded_arith_ops = (

let bounded_signed_int_types = ("Int8")::("Int16")::("Int32")::("Int64")::[]
in (

let bounded_unsigned_int_types = ("UInt8")::("UInt16")::("UInt32")::("UInt64")::("UInt128")::[]
in (

let int_as_bounded = (fun r int_to_t1 n1 -> (

let c = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1)
in (

let int_to_t2 = (FStar_Syntax_Syntax.fv_to_tm int_to_t1)
in (

let uu____9206 = (

let uu____9211 = (

let uu____9212 = (FStar_Syntax_Syntax.as_arg c)
in (uu____9212)::[])
in (FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9211))
in (uu____9206 FStar_Pervasives_Native.None r)))))
in (

let add_sub_mul_v = (FStar_All.pipe_right (FStar_List.append bounded_signed_int_types bounded_unsigned_int_types) (FStar_List.collect (fun m -> (

let uu____9286 = (

let uu____9301 = (FStar_Parser_Const.p2l (("FStar")::(m)::("add")::[]))
in ((uu____9301), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____9323 uu____9324 -> (match (((uu____9323), (uu____9324))) with
| ((int_to_t1, x), (uu____9343, y)) -> begin
(

let uu____9353 = (FStar_BigInt.add_big_int x y)
in (int_as_bounded r int_to_t1 uu____9353))
end))))))
in (

let uu____9354 = (

let uu____9371 = (

let uu____9386 = (FStar_Parser_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((uu____9386), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____9408 uu____9409 -> (match (((uu____9408), (uu____9409))) with
| ((int_to_t1, x), (uu____9428, y)) -> begin
(

let uu____9438 = (FStar_BigInt.sub_big_int x y)
in (int_as_bounded r int_to_t1 uu____9438))
end))))))
in (

let uu____9439 = (

let uu____9456 = (

let uu____9471 = (FStar_Parser_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((uu____9471), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____9493 uu____9494 -> (match (((uu____9493), (uu____9494))) with
| ((int_to_t1, x), (uu____9513, y)) -> begin
(

let uu____9523 = (FStar_BigInt.mult_big_int x y)
in (int_as_bounded r int_to_t1 uu____9523))
end))))))
in (

let uu____9524 = (

let uu____9541 = (

let uu____9556 = (FStar_Parser_Const.p2l (("FStar")::(m)::("v")::[]))
in ((uu____9556), ((Prims.parse_int "1")), ((unary_op arg_as_bounded_int (fun r uu____9574 -> (match (uu____9574) with
| (int_to_t1, x) -> begin
(FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r x)
end))))))
in (uu____9541)::[])
in (uu____9456)::uu____9524))
in (uu____9371)::uu____9439))
in (uu____9286)::uu____9354)))))
in (

let div_mod_unsigned = (FStar_All.pipe_right bounded_unsigned_int_types (FStar_List.collect (fun m -> (

let uu____9704 = (

let uu____9719 = (FStar_Parser_Const.p2l (("FStar")::(m)::("div")::[]))
in ((uu____9719), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____9741 uu____9742 -> (match (((uu____9741), (uu____9742))) with
| ((int_to_t1, x), (uu____9761, y)) -> begin
(

let uu____9771 = (FStar_BigInt.div_big_int x y)
in (int_as_bounded r int_to_t1 uu____9771))
end))))))
in (

let uu____9772 = (

let uu____9789 = (

let uu____9804 = (FStar_Parser_Const.p2l (("FStar")::(m)::("rem")::[]))
in ((uu____9804), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____9826 uu____9827 -> (match (((uu____9826), (uu____9827))) with
| ((int_to_t1, x), (uu____9846, y)) -> begin
(

let uu____9856 = (FStar_BigInt.mod_big_int x y)
in (int_as_bounded r int_to_t1 uu____9856))
end))))))
in (uu____9789)::[])
in (uu____9704)::uu____9772)))))
in (FStar_List.append add_sub_mul_v div_mod_unsigned))))))
in (

let strong_steps = (FStar_List.map (as_primitive_step true) (FStar_List.append basic_ops bounded_arith_ops))
in (

let weak_steps = (FStar_List.map (as_primitive_step false) weak_ops)
in (FStar_All.pipe_left prim_from_list (FStar_List.append strong_steps weak_steps)))))))))))))))))))))))))))))))))


let equality_ops : primitive_step FStar_Util.psmap = (

let interp_prop = (fun psc args -> (

let r = psc.psc_range
in (match (args) with
| ((_typ, uu____9992))::((a1, uu____9994))::((a2, uu____9996))::[] -> begin
(

let uu____10033 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____10033) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___143_10037 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___143_10037.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___143_10037.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___144_10039 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___144_10039.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___144_10039.FStar_Syntax_Syntax.vars}))
end
| uu____10040 -> begin
FStar_Pervasives_Native.None
end))
end
| ((_typ, uu____10042))::(uu____10043)::((a1, uu____10045))::((a2, uu____10047))::[] -> begin
(

let uu____10096 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____10096) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___143_10100 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___143_10100.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___143_10100.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___144_10102 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___144_10102.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___144_10102.FStar_Syntax_Syntax.vars}))
end
| uu____10103 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____10104 -> begin
(failwith "Unexpected number of arguments")
end)))
in (

let propositional_equality = {name = FStar_Parser_Const.eq2_lid; arity = (Prims.parse_int "3"); auto_reflect = FStar_Pervasives_Native.None; strong_reduction_ok = true; requires_binder_substitution = false; interpretation = interp_prop}
in (

let hetero_propositional_equality = {name = FStar_Parser_Const.eq3_lid; arity = (Prims.parse_int "4"); auto_reflect = FStar_Pervasives_Native.None; strong_reduction_ok = true; requires_binder_substitution = false; interpretation = interp_prop}
in (prim_from_list ((propositional_equality)::(hetero_propositional_equality)::[])))))


let unembed_binder_knot : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let unembed_binder : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option = (fun t -> (

let uu____10158 = (FStar_ST.op_Bang unembed_binder_knot)
in (match (uu____10158) with
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Embeddings.unembed e t)
end
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_UnembedBinderKnot), ("unembed_binder_knot is unset!")));
FStar_Pervasives_Native.None;
)
end)))


let mk_psc_subst : 'Auu____10210 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____10210) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun cfg env -> (FStar_List.fold_right (fun uu____10272 subst1 -> (match (uu____10272) with
| (binder_opt, closure) -> begin
(match (((binder_opt), (closure))) with
| (FStar_Pervasives_Native.Some (b), Clos (env1, term, uu____10313, uu____10314)) -> begin
(

let uu____10373 = b
in (match (uu____10373) with
| (bv, uu____10381) -> begin
(

let uu____10382 = (

let uu____10383 = (FStar_Syntax_Util.is_constructed_typ bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.binder_lid)
in (not (uu____10383)))
in (match (uu____10382) with
| true -> begin
subst1
end
| uu____10386 -> begin
(

let term1 = (closure_as_term cfg env1 term)
in (

let uu____10388 = (unembed_binder term1)
in (match (uu____10388) with
| FStar_Pervasives_Native.None -> begin
subst1
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let b1 = (

let uu____10395 = (

let uu___145_10396 = bv
in (

let uu____10397 = (FStar_Syntax_Subst.subst subst1 (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___145_10396.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___145_10396.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10397}))
in (FStar_Syntax_Syntax.freshen_bv uu____10395))
in (

let b_for_x = (

let uu____10401 = (

let uu____10408 = (FStar_Syntax_Syntax.bv_to_name b1)
in (((FStar_Pervasives_Native.fst x)), (uu____10408)))
in FStar_Syntax_Syntax.NT (uu____10401))
in (

let subst2 = (FStar_List.filter (fun uu___87_10422 -> (match (uu___87_10422) with
| FStar_Syntax_Syntax.NT (uu____10423, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (b'); FStar_Syntax_Syntax.pos = uu____10425; FStar_Syntax_Syntax.vars = uu____10426}) -> begin
(

let uu____10431 = (FStar_Ident.ident_equals b1.FStar_Syntax_Syntax.ppname b'.FStar_Syntax_Syntax.ppname)
in (not (uu____10431)))
end
| uu____10432 -> begin
true
end)) subst1)
in (b_for_x)::subst2)))
end)))
end))
end))
end
| uu____10433 -> begin
subst1
end)
end)) env []))


let reduce_primops : 'Auu____10456 'Auu____10457 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____10456) FStar_Pervasives_Native.option * closure) Prims.list  ->  'Auu____10457  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (match ((not (cfg.steps.primops))) with
| true -> begin
tm
end
| uu____10502 -> begin
(

let uu____10503 = (FStar_Syntax_Util.head_and_args tm)
in (match (uu____10503) with
| (head1, args) -> begin
(

let uu____10540 = (

let uu____10541 = (FStar_Syntax_Util.un_uinst head1)
in uu____10541.FStar_Syntax_Syntax.n)
in (match (uu____10540) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____10545 = (find_prim_step cfg fv)
in (match (uu____10545) with
| FStar_Pervasives_Native.Some (prim_step) when (prim_step.strong_reduction_ok || (not (cfg.strong))) -> begin
(

let l = (FStar_List.length args)
in (match ((l < prim_step.arity)) with
| true -> begin
((log_primops cfg (fun uu____10567 -> (

let uu____10568 = (FStar_Syntax_Print.lid_to_string prim_step.name)
in (

let uu____10569 = (FStar_Util.string_of_int l)
in (

let uu____10576 = (FStar_Util.string_of_int prim_step.arity)
in (FStar_Util.print3 "primop: found partially applied %s (%s/%s args)\n" uu____10568 uu____10569 uu____10576))))));
tm;
)
end
| uu____10577 -> begin
(

let uu____10578 = (match ((Prims.op_Equality l prim_step.arity)) with
| true -> begin
((args), ([]))
end
| uu____10645 -> begin
(FStar_List.splitAt prim_step.arity args)
end)
in (match (uu____10578) with
| (args_1, args_2) -> begin
((log_primops cfg (fun uu____10689 -> (

let uu____10690 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: trying to reduce <%s>\n" uu____10690))));
(

let psc = {psc_range = head1.FStar_Syntax_Syntax.pos; psc_subst = (fun uu____10693 -> (match (prim_step.requires_binder_substitution) with
| true -> begin
(mk_psc_subst cfg env)
end
| uu____10694 -> begin
[]
end))}
in (

let uu____10695 = (prim_step.interpretation psc args_1)
in (match (uu____10695) with
| FStar_Pervasives_Native.None -> begin
((log_primops cfg (fun uu____10701 -> (

let uu____10702 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: <%s> did not reduce\n" uu____10702))));
tm;
)
end
| FStar_Pervasives_Native.Some (reduced) -> begin
((log_primops cfg (fun uu____10708 -> (

let uu____10709 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____10710 = (FStar_Syntax_Print.term_to_string reduced)
in (FStar_Util.print2 "primop: <%s> reduced to <%s>\n" uu____10709 uu____10710)))));
(FStar_Syntax_Util.mk_app reduced args_2);
)
end)));
)
end))
end))
end
| FStar_Pervasives_Native.Some (uu____10711) -> begin
((log_primops cfg (fun uu____10715 -> (

let uu____10716 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: not reducing <%s> since we\'re doing strong reduction\n" uu____10716))));
tm;
)
end
| FStar_Pervasives_Native.None -> begin
tm
end))
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of) when (not (cfg.strong)) -> begin
((log_primops cfg (fun uu____10720 -> (

let uu____10721 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: reducing <%s>\n" uu____10721))));
(match (args) with
| ((a1, uu____10723))::[] -> begin
(FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range tm.FStar_Syntax_Syntax.pos a1.FStar_Syntax_Syntax.pos)
end
| uu____10740 -> begin
tm
end);
)
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of) when (not (cfg.strong)) -> begin
((log_primops cfg (fun uu____10752 -> (

let uu____10753 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: reducing <%s>\n" uu____10753))));
(match (args) with
| ((t, uu____10755))::((r, uu____10757))::[] -> begin
(

let uu____10784 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_range r)
in (match (uu____10784) with
| FStar_Pervasives_Native.Some (rng) -> begin
(

let uu___146_10788 = t
in {FStar_Syntax_Syntax.n = uu___146_10788.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___146_10788.FStar_Syntax_Syntax.vars})
end
| FStar_Pervasives_Native.None -> begin
tm
end))
end
| uu____10791 -> begin
tm
end);
)
end
| uu____10800 -> begin
tm
end))
end))
end))


let reduce_equality : 'Auu____10811 'Auu____10812 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____10811) FStar_Pervasives_Native.option * closure) Prims.list  ->  'Auu____10812  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (reduce_primops (

let uu___147_10856 = cfg
in {steps = (

let uu___148_10859 = default_steps
in {beta = uu___148_10859.beta; iota = uu___148_10859.iota; zeta = uu___148_10859.zeta; weak = uu___148_10859.weak; hnf = uu___148_10859.hnf; primops = true; do_not_unfold_pure_lets = uu___148_10859.do_not_unfold_pure_lets; unfold_until = uu___148_10859.unfold_until; unfold_only = uu___148_10859.unfold_only; unfold_fully = uu___148_10859.unfold_fully; unfold_attr = uu___148_10859.unfold_attr; unfold_tac = uu___148_10859.unfold_tac; pure_subterms_within_computations = uu___148_10859.pure_subterms_within_computations; simplify = uu___148_10859.simplify; erase_universes = uu___148_10859.erase_universes; allow_unbound_universes = uu___148_10859.allow_unbound_universes; reify_ = uu___148_10859.reify_; compress_uvars = uu___148_10859.compress_uvars; no_full_norm = uu___148_10859.no_full_norm; check_no_uvars = uu___148_10859.check_no_uvars; unmeta = uu___148_10859.unmeta; unascribe = uu___148_10859.unascribe; in_full_norm_request = uu___148_10859.in_full_norm_request; weakly_reduce_scrutinee = uu___148_10859.weakly_reduce_scrutinee}); tcenv = uu___147_10856.tcenv; debug = uu___147_10856.debug; delta_level = uu___147_10856.delta_level; primitive_steps = equality_ops; strong = uu___147_10856.strong; memoize_lazy = uu___147_10856.memoize_lazy; normalize_pure_lets = uu___147_10856.normalize_pure_lets}) tm))


let is_norm_request : 'Auu____10866 . FStar_Syntax_Syntax.term  ->  'Auu____10866 Prims.list  ->  Prims.bool = (fun hd1 args -> (

let uu____10881 = (

let uu____10888 = (

let uu____10889 = (FStar_Syntax_Util.un_uinst hd1)
in uu____10889.FStar_Syntax_Syntax.n)
in ((uu____10888), (args)))
in (match (uu____10881) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____10895)::(uu____10896)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____10900)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (steps)::(uu____10905)::(uu____10906)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm)
end
| uu____10909 -> begin
false
end)))


let tr_norm_step : FStar_Syntax_Embeddings.norm_step  ->  step Prims.list = (fun uu___88_10922 -> (match (uu___88_10922) with
| FStar_Syntax_Embeddings.Zeta -> begin
(Zeta)::[]
end
| FStar_Syntax_Embeddings.Iota -> begin
(Iota)::[]
end
| FStar_Syntax_Embeddings.Delta -> begin
(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
end
| FStar_Syntax_Embeddings.Simpl -> begin
(Simplify)::[]
end
| FStar_Syntax_Embeddings.Weak -> begin
(Weak)::[]
end
| FStar_Syntax_Embeddings.HNF -> begin
(HNF)::[]
end
| FStar_Syntax_Embeddings.Primops -> begin
(Primops)::[]
end
| FStar_Syntax_Embeddings.UnfoldOnly (names1) -> begin
(

let uu____10928 = (

let uu____10931 = (

let uu____10932 = (FStar_List.map FStar_Ident.lid_of_str names1)
in UnfoldOnly (uu____10932))
in (uu____10931)::[])
in (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::uu____10928)
end
| FStar_Syntax_Embeddings.UnfoldFully (names1) -> begin
(

let uu____10938 = (

let uu____10941 = (

let uu____10942 = (FStar_List.map FStar_Ident.lid_of_str names1)
in UnfoldFully (uu____10942))
in (uu____10941)::[])
in (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::uu____10938)
end
| FStar_Syntax_Embeddings.UnfoldAttr (t) -> begin
(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(UnfoldAttr (t))::[]
end))


let tr_norm_steps : FStar_Syntax_Embeddings.norm_step Prims.list  ->  step Prims.list = (fun s -> (FStar_List.concatMap tr_norm_step s))


let get_norm_request : 'Auu____10963 . (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term * 'Auu____10963) Prims.list  ->  (step Prims.list * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun full_norm args -> (

let parse_steps = (fun s -> (

let uu____11009 = (

let uu____11014 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_norm_step)
in (FStar_Syntax_Embeddings.try_unembed uu____11014 s))
in (match (uu____11009) with
| FStar_Pervasives_Native.Some (steps) -> begin
(

let uu____11030 = (tr_norm_steps steps)
in FStar_Pervasives_Native.Some (uu____11030))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))
in (match (args) with
| (uu____11047)::((tm, uu____11049))::[] -> begin
(

let s = (Beta)::(Zeta)::(Iota)::(Primops)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Reify)::[]
in FStar_Pervasives_Native.Some (((s), (tm))))
end
| ((tm, uu____11078))::[] -> begin
(

let s = (Beta)::(Zeta)::(Iota)::(Primops)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Reify)::[]
in FStar_Pervasives_Native.Some (((s), (tm))))
end
| ((steps, uu____11099))::(uu____11100)::((tm, uu____11102))::[] -> begin
(

let add_exclude = (fun s z -> (match ((FStar_List.contains z s)) with
| true -> begin
s
end
| uu____11142 -> begin
(Exclude (z))::s
end))
in (

let uu____11143 = (

let uu____11148 = (full_norm steps)
in (parse_steps uu____11148))
in (match (uu____11143) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s) -> begin
(

let s1 = (Beta)::s
in (

let s2 = (add_exclude s1 Zeta)
in (

let s3 = (add_exclude s2 Iota)
in FStar_Pervasives_Native.Some (((s3), (tm))))))
end)))
end
| uu____11187 -> begin
FStar_Pervasives_Native.None
end)))


let is_reify_head : stack_elt Prims.list  ->  Prims.bool = (fun uu___89_11206 -> (match (uu___89_11206) with
| (App (uu____11209, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____11210; FStar_Syntax_Syntax.vars = uu____11211}, uu____11212, uu____11213))::uu____11214 -> begin
true
end
| uu____11219 -> begin
false
end))


let firstn : 'Auu____11228 . Prims.int  ->  'Auu____11228 Prims.list  ->  ('Auu____11228 Prims.list * 'Auu____11228 Prims.list) = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____11255 -> begin
(FStar_Util.first_N k l)
end))


let should_reify : cfg  ->  stack_elt Prims.list  ->  Prims.bool = (fun cfg stack -> (match (stack) with
| (App (uu____11270, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____11271; FStar_Syntax_Syntax.vars = uu____11272}, uu____11273, uu____11274))::uu____11275 -> begin
cfg.steps.reify_
end
| uu____11280 -> begin
false
end))


let rec maybe_weakly_reduced : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun tm -> (

let aux_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, uu____11303) -> begin
(maybe_weakly_reduced t)
end
| FStar_Syntax_Syntax.Total (t, uu____11313) -> begin
(maybe_weakly_reduced t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
((maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) || (FStar_Util.for_some (fun uu____11332 -> (match (uu____11332) with
| (a, uu____11340) -> begin
(maybe_weakly_reduced a)
end)) ct.FStar_Syntax_Syntax.effect_args))
end))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____11346) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (uu____11371) -> begin
false
end
| FStar_Syntax_Syntax.Tm_uvar (uu____11372) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____11373) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____11374) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (uu____11375) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____11376) -> begin
false
end
| FStar_Syntax_Syntax.Tm_lazy (uu____11377) -> begin
false
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| FStar_Syntax_Syntax.Tm_uinst (uu____11378) -> begin
false
end
| FStar_Syntax_Syntax.Tm_quoted (uu____11385) -> begin
false
end
| FStar_Syntax_Syntax.Tm_let (uu____11392) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____11405) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____11422) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____11435) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____11442) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
((maybe_weakly_reduced t1) || (FStar_All.pipe_right args (FStar_Util.for_some (fun uu____11504 -> (match (uu____11504) with
| (a, uu____11512) -> begin
(maybe_weakly_reduced a)
end)))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____11519) -> begin
(((maybe_weakly_reduced t1) || (match ((FStar_Pervasives_Native.fst asc)) with
| FStar_Util.Inl (t2) -> begin
(maybe_weakly_reduced t2)
end
| FStar_Util.Inr (c2) -> begin
(aux_comp c2)
end)) || (match ((FStar_Pervasives_Native.snd asc)) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (tac) -> begin
(maybe_weakly_reduced tac)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
((maybe_weakly_reduced t1) || (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(FStar_Util.for_some (FStar_Util.for_some (fun uu____11641 -> (match (uu____11641) with
| (a, uu____11649) -> begin
(maybe_weakly_reduced a)
end))) args)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____11654, uu____11655, t') -> begin
(maybe_weakly_reduced t')
end
| FStar_Syntax_Syntax.Meta_monadic (uu____11661, t') -> begin
(maybe_weakly_reduced t')
end
| FStar_Syntax_Syntax.Meta_labeled (uu____11667) -> begin
false
end
| FStar_Syntax_Syntax.Meta_desugared (uu____11674) -> begin
false
end
| FStar_Syntax_Syntax.Meta_named (uu____11675) -> begin
false
end))
end))))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t1 = ((match (cfg.debug.norm_delayed) with
| true -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____11965) -> begin
(

let uu____11990 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "NORM delayed: %s\n" uu____11990))
end
| uu____11991 -> begin
()
end)
end
| uu____11992 -> begin
()
end);
(FStar_Syntax_Subst.compress t);
)
in ((log cfg (fun uu____11999 -> (

let uu____12000 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____12001 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12002 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____12009 = (

let uu____12010 = (

let uu____12013 = (firstn (Prims.parse_int "4") stack)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12013))
in (stack_to_string uu____12010))
in (FStar_Util.print4 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n" uu____12000 uu____12001 uu____12002 uu____12009)))))));
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_constant (uu____12036) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____12037) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_lazy (uu____12038) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____12039; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = uu____12040}) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____12043; FStar_Syntax_Syntax.fv_delta = uu____12044; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____12045; FStar_Syntax_Syntax.fv_delta = uu____12046; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____12047))}) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____12054) -> begin
(

let uu____12061 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____12061))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when (((not (cfg.steps.no_full_norm)) && (is_norm_request hd1 args)) && (

let uu____12091 = (FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)
in (not (uu____12091)))) -> begin
(

let cfg' = (

let uu___149_12093 = cfg
in {steps = (

let uu___150_12096 = cfg.steps
in {beta = uu___150_12096.beta; iota = uu___150_12096.iota; zeta = uu___150_12096.zeta; weak = uu___150_12096.weak; hnf = uu___150_12096.hnf; primops = uu___150_12096.primops; do_not_unfold_pure_lets = false; unfold_until = uu___150_12096.unfold_until; unfold_only = FStar_Pervasives_Native.None; unfold_fully = FStar_Pervasives_Native.None; unfold_attr = uu___150_12096.unfold_attr; unfold_tac = uu___150_12096.unfold_tac; pure_subterms_within_computations = uu___150_12096.pure_subterms_within_computations; simplify = uu___150_12096.simplify; erase_universes = uu___150_12096.erase_universes; allow_unbound_universes = uu___150_12096.allow_unbound_universes; reify_ = uu___150_12096.reify_; compress_uvars = uu___150_12096.compress_uvars; no_full_norm = uu___150_12096.no_full_norm; check_no_uvars = uu___150_12096.check_no_uvars; unmeta = uu___150_12096.unmeta; unascribe = uu___150_12096.unascribe; in_full_norm_request = uu___150_12096.in_full_norm_request; weakly_reduce_scrutinee = uu___150_12096.weakly_reduce_scrutinee}); tcenv = uu___149_12093.tcenv; debug = uu___149_12093.debug; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]; primitive_steps = uu___149_12093.primitive_steps; strong = uu___149_12093.strong; memoize_lazy = uu___149_12093.memoize_lazy; normalize_pure_lets = true})
in (

let uu____12101 = (get_norm_request (norm cfg' env []) args)
in (match (uu____12101) with
| FStar_Pervasives_Native.None -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____12132 stack1 -> (match (uu____12132) with
| (a, aq) -> begin
(

let uu____12144 = (

let uu____12145 = (

let uu____12152 = (

let uu____12153 = (

let uu____12184 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____12184), (false)))
in Clos (uu____12153))
in ((uu____12152), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____12145))
in (uu____12144)::stack1)
end)) args))
in ((log cfg (fun uu____12272 -> (

let uu____12273 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____12273))));
(norm cfg env stack1 hd1);
))
end
| FStar_Pervasives_Native.Some (s, tm) -> begin
(

let delta_level = (

let uu____12295 = (FStar_All.pipe_right s (FStar_Util.for_some (fun uu___90_12300 -> (match (uu___90_12300) with
| UnfoldUntil (uu____12301) -> begin
true
end
| UnfoldOnly (uu____12302) -> begin
true
end
| UnfoldFully (uu____12305) -> begin
true
end
| uu____12308 -> begin
false
end))))
in (match (uu____12295) with
| true -> begin
(FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]
end
| uu____12311 -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end))
in (

let cfg'1 = (

let uu___151_12313 = cfg
in (

let uu____12314 = (

let uu___152_12315 = (to_fsteps s)
in {beta = uu___152_12315.beta; iota = uu___152_12315.iota; zeta = uu___152_12315.zeta; weak = uu___152_12315.weak; hnf = uu___152_12315.hnf; primops = uu___152_12315.primops; do_not_unfold_pure_lets = uu___152_12315.do_not_unfold_pure_lets; unfold_until = uu___152_12315.unfold_until; unfold_only = uu___152_12315.unfold_only; unfold_fully = uu___152_12315.unfold_fully; unfold_attr = uu___152_12315.unfold_attr; unfold_tac = uu___152_12315.unfold_tac; pure_subterms_within_computations = uu___152_12315.pure_subterms_within_computations; simplify = uu___152_12315.simplify; erase_universes = uu___152_12315.erase_universes; allow_unbound_universes = uu___152_12315.allow_unbound_universes; reify_ = uu___152_12315.reify_; compress_uvars = uu___152_12315.compress_uvars; no_full_norm = uu___152_12315.no_full_norm; check_no_uvars = uu___152_12315.check_no_uvars; unmeta = uu___152_12315.unmeta; unascribe = uu___152_12315.unascribe; in_full_norm_request = true; weakly_reduce_scrutinee = uu___152_12315.weakly_reduce_scrutinee})
in {steps = uu____12314; tcenv = uu___151_12313.tcenv; debug = uu___151_12313.debug; delta_level = delta_level; primitive_steps = uu___151_12313.primitive_steps; strong = uu___151_12313.strong; memoize_lazy = uu___151_12313.memoize_lazy; normalize_pure_lets = true}))
in (

let stack' = (

let tail1 = (Cfg (cfg))::stack
in (match (cfg.debug.print_normalized) with
| true -> begin
(

let uu____12324 = (

let uu____12325 = (

let uu____12330 = (FStar_Util.now ())
in ((t1), (uu____12330)))
in Debug (uu____12325))
in (uu____12324)::tail1)
end
| uu____12331 -> begin
tail1
end))
in (norm cfg'1 env stack' tm))))
end)))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u1 = (norm_universe cfg env u)
in (

let uu____12334 = (mk (FStar_Syntax_Syntax.Tm_type (u1)) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____12334)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(match (cfg.steps.erase_universes) with
| true -> begin
(norm cfg env stack t')
end
| uu____12341 -> begin
(

let us1 = (

let uu____12343 = (

let uu____12350 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____12350), (t1.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____12343))
in (

let stack1 = (us1)::stack
in (norm cfg env stack1 t')))
end)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let qninfo = (

let uu____12360 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12360))
in (

let uu____12361 = (FStar_TypeChecker_Env.qninfo_is_action qninfo)
in (match (uu____12361) with
| true -> begin
(

let b = (should_reify cfg stack)
in ((log cfg (fun uu____12367 -> (

let uu____12368 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12369 = (FStar_Util.string_of_bool b)
in (FStar_Util.print2 ">>> For DM4F action %s, should_reify = %s\n" uu____12368 uu____12369)))));
(match (b) with
| true -> begin
(

let uu____12370 = (FStar_List.tl stack)
in (do_unfold_fv cfg env uu____12370 t1 qninfo fv))
end
| uu____12371 -> begin
(rebuild cfg env stack t1)
end);
))
end
| uu____12372 -> begin
(

let should_delta = (((

let uu____12376 = (find_prim_step cfg fv)
in (FStar_Option.isNone uu____12376)) && (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, uu____12389), uu____12390); FStar_Syntax_Syntax.sigrng = uu____12391; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____12393; FStar_Syntax_Syntax.sigattrs = uu____12394}, uu____12395), uu____12396) -> begin
((not ((FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect qs))) && ((not (is_rec)) || cfg.steps.zeta))
end
| uu____12455 -> begin
true
end)) && (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun uu___91_12459 -> (match (uu___91_12459) with
| FStar_TypeChecker_Env.UnfoldTac -> begin
false
end
| FStar_TypeChecker_Env.NoDelta -> begin
false
end
| FStar_TypeChecker_Env.Inlining -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| FStar_TypeChecker_Env.Unfold (l) -> begin
(FStar_TypeChecker_Common.delta_depth_greater_than fv.FStar_Syntax_Syntax.fv_delta l)
end)))))
in (

let should_delta1 = (should_delta && (

let attrs = (FStar_TypeChecker_Env.attrs_of_qninfo qninfo)
in (((not (cfg.steps.unfold_tac)) || (

let uu____12469 = (cases (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.tac_opaque_attr)) false attrs)
in (not (uu____12469)))) && ((match (cfg.steps.unfold_only) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (lids) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
end) || (match (((attrs), (cfg.steps.unfold_attr))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____12488)) -> begin
false
end
| (FStar_Pervasives_Native.Some (ats), FStar_Pervasives_Native.Some (ats')) -> begin
(FStar_Util.for_some (fun at -> (FStar_Util.for_some (FStar_Syntax_Util.attr_eq at) ats')) ats)
end
| (uu____12523, uu____12524) -> begin
false
end)))))
in (

let uu____12541 = (match (cfg.steps.unfold_fully) with
| FStar_Pervasives_Native.None -> begin
((should_delta1), (false))
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____12557 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (match (uu____12557) with
| true -> begin
((true), (true))
end
| uu____12562 -> begin
((false), (false))
end))
end)
in (match (uu____12541) with
| (should_delta2, fully) -> begin
((log cfg (fun uu____12570 -> (

let uu____12571 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12572 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____12573 = (FStar_Util.string_of_bool should_delta2)
in (FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n" uu____12571 uu____12572 uu____12573))))));
(match (should_delta2) with
| true -> begin
(

let uu____12574 = (match (fully) with
| true -> begin
(((Cfg (cfg))::stack), ((

let uu___153_12584 = cfg
in {steps = (

let uu___154_12587 = cfg.steps
in {beta = uu___154_12587.beta; iota = false; zeta = false; weak = false; hnf = false; primops = false; do_not_unfold_pure_lets = uu___154_12587.do_not_unfold_pure_lets; unfold_until = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant); unfold_only = FStar_Pervasives_Native.None; unfold_fully = FStar_Pervasives_Native.None; unfold_attr = uu___154_12587.unfold_attr; unfold_tac = uu___154_12587.unfold_tac; pure_subterms_within_computations = uu___154_12587.pure_subterms_within_computations; simplify = false; erase_universes = uu___154_12587.erase_universes; allow_unbound_universes = uu___154_12587.allow_unbound_universes; reify_ = uu___154_12587.reify_; compress_uvars = uu___154_12587.compress_uvars; no_full_norm = uu___154_12587.no_full_norm; check_no_uvars = uu___154_12587.check_no_uvars; unmeta = uu___154_12587.unmeta; unascribe = uu___154_12587.unascribe; in_full_norm_request = uu___154_12587.in_full_norm_request; weakly_reduce_scrutinee = uu___154_12587.weakly_reduce_scrutinee}); tcenv = uu___153_12584.tcenv; debug = uu___153_12584.debug; delta_level = uu___153_12584.delta_level; primitive_steps = uu___153_12584.primitive_steps; strong = uu___153_12584.strong; memoize_lazy = uu___153_12584.memoize_lazy; normalize_pure_lets = uu___153_12584.normalize_pure_lets})))
end
| uu____12592 -> begin
((stack), (cfg))
end)
in (match (uu____12574) with
| (stack1, cfg1) -> begin
(do_unfold_fv cfg1 env stack1 t1 qninfo fv)
end))
end
| uu____12595 -> begin
(rebuild cfg env stack t1)
end);
)
end))))
end)))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____12597 = (lookup_bvar env x)
in (match (uu____12597) with
| Univ (uu____12598) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env1, t0, r, fix) -> begin
(match (((not (fix)) || cfg.steps.zeta)) with
| true -> begin
(

let uu____12647 = (FStar_ST.op_Bang r)
in (match (uu____12647) with
| FStar_Pervasives_Native.Some (env2, t') -> begin
((log cfg (fun uu____12769 -> (

let uu____12770 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12771 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____12770 uu____12771)))));
(

let uu____12772 = (maybe_weakly_reduced t')
in (match (uu____12772) with
| true -> begin
(match (stack) with
| [] when (cfg.steps.weak || cfg.steps.compress_uvars) -> begin
(rebuild cfg env2 stack t')
end
| uu____12773 -> begin
(norm cfg env2 stack t')
end)
end
| uu____12774 -> begin
(rebuild cfg env2 stack t')
end));
)
end
| FStar_Pervasives_Native.None -> begin
(norm cfg env1 ((MemoLazy (r))::stack) t0)
end))
end
| uu____12820 -> begin
(norm cfg env1 stack t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (UnivArgs (uu____12844))::uu____12845 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (uu____12854))::uu____12855 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, uu____12867, uu____12868))::stack_rest -> begin
(match (c) with
| Univ (uu____12872) -> begin
(norm cfg ((((FStar_Pervasives_Native.None), (c)))::env) stack_rest t1)
end
| uu____12881 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (b)::[] -> begin
((log cfg (fun uu____12902 -> (

let uu____12903 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____12903))));
(norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body);
)
end
| (b)::tl1 -> begin
((log cfg (fun uu____12939 -> (

let uu____12940 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____12940))));
(

let body1 = (mk (FStar_Syntax_Syntax.Tm_abs (((tl1), (body), (lopt)))) t1.FStar_Syntax_Syntax.pos)
in (norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body1));
)
end)
end)
end
| (Cfg (cfg1))::stack1 -> begin
(norm cfg1 env stack1 t1)
end
| (MemoLazy (r))::stack1 -> begin
((set_memo cfg r ((env), (t1)));
(log cfg (fun uu____13014 -> (

let uu____13015 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____13015))));
(norm cfg env stack1 t1);
)
end
| (Debug (uu____13016))::uu____13017 -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____13025 -> begin
(

let steps' = (

let uu___155_13027 = cfg.steps
in {beta = uu___155_13027.beta; iota = false; zeta = false; weak = false; hnf = uu___155_13027.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___155_13027.unfold_until; unfold_only = uu___155_13027.unfold_only; unfold_fully = uu___155_13027.unfold_fully; unfold_attr = uu___155_13027.unfold_attr; unfold_tac = uu___155_13027.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___155_13027.erase_universes; allow_unbound_universes = uu___155_13027.allow_unbound_universes; reify_ = false; compress_uvars = uu___155_13027.compress_uvars; no_full_norm = true; check_no_uvars = uu___155_13027.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___155_13027.in_full_norm_request; weakly_reduce_scrutinee = uu___155_13027.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___156_13029 = cfg
in {steps = steps'; tcenv = uu___156_13029.tcenv; debug = uu___156_13029.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___156_13029.primitive_steps; strong = uu___156_13029.strong; memoize_lazy = uu___156_13029.memoize_lazy; normalize_pure_lets = uu___156_13029.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____13030 -> begin
(

let uu____13031 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____13031) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____13057 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____13094 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____13094))))
end
| uu____13095 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___157_13099 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___157_13099.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___157_13099.FStar_Syntax_Syntax.residual_flags})))
end
| uu____13100 -> begin
lopt
end)
in ((log cfg (fun uu____13106 -> (

let uu____13107 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____13107))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___158_13116 = cfg
in {steps = uu___158_13116.steps; tcenv = uu___158_13116.tcenv; debug = uu___158_13116.debug; delta_level = uu___158_13116.delta_level; primitive_steps = uu___158_13116.primitive_steps; strong = true; memoize_lazy = uu___158_13116.memoize_lazy; normalize_pure_lets = uu___158_13116.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Meta (uu____13119))::uu____13120 -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____13130 -> begin
(

let steps' = (

let uu___155_13132 = cfg.steps
in {beta = uu___155_13132.beta; iota = false; zeta = false; weak = false; hnf = uu___155_13132.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___155_13132.unfold_until; unfold_only = uu___155_13132.unfold_only; unfold_fully = uu___155_13132.unfold_fully; unfold_attr = uu___155_13132.unfold_attr; unfold_tac = uu___155_13132.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___155_13132.erase_universes; allow_unbound_universes = uu___155_13132.allow_unbound_universes; reify_ = false; compress_uvars = uu___155_13132.compress_uvars; no_full_norm = true; check_no_uvars = uu___155_13132.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___155_13132.in_full_norm_request; weakly_reduce_scrutinee = uu___155_13132.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___156_13134 = cfg
in {steps = steps'; tcenv = uu___156_13134.tcenv; debug = uu___156_13134.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___156_13134.primitive_steps; strong = uu___156_13134.strong; memoize_lazy = uu___156_13134.memoize_lazy; normalize_pure_lets = uu___156_13134.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____13135 -> begin
(

let uu____13136 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____13136) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____13162 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____13199 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____13199))))
end
| uu____13200 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___157_13204 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___157_13204.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___157_13204.FStar_Syntax_Syntax.residual_flags})))
end
| uu____13205 -> begin
lopt
end)
in ((log cfg (fun uu____13211 -> (

let uu____13212 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____13212))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___158_13221 = cfg
in {steps = uu___158_13221.steps; tcenv = uu___158_13221.tcenv; debug = uu___158_13221.debug; delta_level = uu___158_13221.delta_level; primitive_steps = uu___158_13221.primitive_steps; strong = true; memoize_lazy = uu___158_13221.memoize_lazy; normalize_pure_lets = uu___158_13221.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Let (uu____13224))::uu____13225 -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____13237 -> begin
(

let steps' = (

let uu___155_13239 = cfg.steps
in {beta = uu___155_13239.beta; iota = false; zeta = false; weak = false; hnf = uu___155_13239.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___155_13239.unfold_until; unfold_only = uu___155_13239.unfold_only; unfold_fully = uu___155_13239.unfold_fully; unfold_attr = uu___155_13239.unfold_attr; unfold_tac = uu___155_13239.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___155_13239.erase_universes; allow_unbound_universes = uu___155_13239.allow_unbound_universes; reify_ = false; compress_uvars = uu___155_13239.compress_uvars; no_full_norm = true; check_no_uvars = uu___155_13239.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___155_13239.in_full_norm_request; weakly_reduce_scrutinee = uu___155_13239.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___156_13241 = cfg
in {steps = steps'; tcenv = uu___156_13241.tcenv; debug = uu___156_13241.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___156_13241.primitive_steps; strong = uu___156_13241.strong; memoize_lazy = uu___156_13241.memoize_lazy; normalize_pure_lets = uu___156_13241.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____13242 -> begin
(

let uu____13243 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____13243) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____13269 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____13306 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____13306))))
end
| uu____13307 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___157_13311 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___157_13311.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___157_13311.FStar_Syntax_Syntax.residual_flags})))
end
| uu____13312 -> begin
lopt
end)
in ((log cfg (fun uu____13318 -> (

let uu____13319 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____13319))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___158_13328 = cfg
in {steps = uu___158_13328.steps; tcenv = uu___158_13328.tcenv; debug = uu___158_13328.debug; delta_level = uu___158_13328.delta_level; primitive_steps = uu___158_13328.primitive_steps; strong = true; memoize_lazy = uu___158_13328.memoize_lazy; normalize_pure_lets = uu___158_13328.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (App (uu____13331))::uu____13332 -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____13344 -> begin
(

let steps' = (

let uu___155_13346 = cfg.steps
in {beta = uu___155_13346.beta; iota = false; zeta = false; weak = false; hnf = uu___155_13346.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___155_13346.unfold_until; unfold_only = uu___155_13346.unfold_only; unfold_fully = uu___155_13346.unfold_fully; unfold_attr = uu___155_13346.unfold_attr; unfold_tac = uu___155_13346.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___155_13346.erase_universes; allow_unbound_universes = uu___155_13346.allow_unbound_universes; reify_ = false; compress_uvars = uu___155_13346.compress_uvars; no_full_norm = true; check_no_uvars = uu___155_13346.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___155_13346.in_full_norm_request; weakly_reduce_scrutinee = uu___155_13346.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___156_13348 = cfg
in {steps = steps'; tcenv = uu___156_13348.tcenv; debug = uu___156_13348.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___156_13348.primitive_steps; strong = uu___156_13348.strong; memoize_lazy = uu___156_13348.memoize_lazy; normalize_pure_lets = uu___156_13348.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____13349 -> begin
(

let uu____13350 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____13350) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____13376 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____13413 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____13413))))
end
| uu____13414 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___157_13418 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___157_13418.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___157_13418.FStar_Syntax_Syntax.residual_flags})))
end
| uu____13419 -> begin
lopt
end)
in ((log cfg (fun uu____13425 -> (

let uu____13426 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____13426))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___158_13435 = cfg
in {steps = uu___158_13435.steps; tcenv = uu___158_13435.tcenv; debug = uu___158_13435.debug; delta_level = uu___158_13435.delta_level; primitive_steps = uu___158_13435.primitive_steps; strong = true; memoize_lazy = uu___158_13435.memoize_lazy; normalize_pure_lets = uu___158_13435.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Abs (uu____13438))::uu____13439 -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____13455 -> begin
(

let steps' = (

let uu___155_13457 = cfg.steps
in {beta = uu___155_13457.beta; iota = false; zeta = false; weak = false; hnf = uu___155_13457.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___155_13457.unfold_until; unfold_only = uu___155_13457.unfold_only; unfold_fully = uu___155_13457.unfold_fully; unfold_attr = uu___155_13457.unfold_attr; unfold_tac = uu___155_13457.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___155_13457.erase_universes; allow_unbound_universes = uu___155_13457.allow_unbound_universes; reify_ = false; compress_uvars = uu___155_13457.compress_uvars; no_full_norm = true; check_no_uvars = uu___155_13457.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___155_13457.in_full_norm_request; weakly_reduce_scrutinee = uu___155_13457.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___156_13459 = cfg
in {steps = steps'; tcenv = uu___156_13459.tcenv; debug = uu___156_13459.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___156_13459.primitive_steps; strong = uu___156_13459.strong; memoize_lazy = uu___156_13459.memoize_lazy; normalize_pure_lets = uu___156_13459.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____13460 -> begin
(

let uu____13461 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____13461) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____13487 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____13524 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____13524))))
end
| uu____13525 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___157_13529 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___157_13529.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___157_13529.FStar_Syntax_Syntax.residual_flags})))
end
| uu____13530 -> begin
lopt
end)
in ((log cfg (fun uu____13536 -> (

let uu____13537 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____13537))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___158_13546 = cfg
in {steps = uu___158_13546.steps; tcenv = uu___158_13546.tcenv; debug = uu___158_13546.debug; delta_level = uu___158_13546.delta_level; primitive_steps = uu___158_13546.primitive_steps; strong = true; memoize_lazy = uu___158_13546.memoize_lazy; normalize_pure_lets = uu___158_13546.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| [] -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____13550 -> begin
(

let steps' = (

let uu___155_13552 = cfg.steps
in {beta = uu___155_13552.beta; iota = false; zeta = false; weak = false; hnf = uu___155_13552.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___155_13552.unfold_until; unfold_only = uu___155_13552.unfold_only; unfold_fully = uu___155_13552.unfold_fully; unfold_attr = uu___155_13552.unfold_attr; unfold_tac = uu___155_13552.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___155_13552.erase_universes; allow_unbound_universes = uu___155_13552.allow_unbound_universes; reify_ = false; compress_uvars = uu___155_13552.compress_uvars; no_full_norm = true; check_no_uvars = uu___155_13552.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___155_13552.in_full_norm_request; weakly_reduce_scrutinee = uu___155_13552.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___156_13554 = cfg
in {steps = steps'; tcenv = uu___156_13554.tcenv; debug = uu___156_13554.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___156_13554.primitive_steps; strong = uu___156_13554.strong; memoize_lazy = uu___156_13554.memoize_lazy; normalize_pure_lets = uu___156_13554.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____13555 -> begin
(

let uu____13556 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____13556) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____13582 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____13619 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____13619))))
end
| uu____13620 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___157_13624 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___157_13624.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___157_13624.FStar_Syntax_Syntax.residual_flags})))
end
| uu____13625 -> begin
lopt
end)
in ((log cfg (fun uu____13631 -> (

let uu____13632 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____13632))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___158_13641 = cfg
in {steps = uu___158_13641.steps; tcenv = uu___158_13641.tcenv; debug = uu___158_13641.debug; delta_level = uu___158_13641.delta_level; primitive_steps = uu___158_13641.primitive_steps; strong = true; memoize_lazy = uu___158_13641.memoize_lazy; normalize_pure_lets = uu___158_13641.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____13682 stack1 -> (match (uu____13682) with
| (a, aq) -> begin
(

let uu____13694 = (

let uu____13695 = (

let uu____13702 = (

let uu____13703 = (

let uu____13734 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____13734), (false)))
in Clos (uu____13703))
in ((uu____13702), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____13695))
in (uu____13694)::stack1)
end)) args))
in ((log cfg (fun uu____13822 -> (

let uu____13823 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____13823))));
(norm cfg env stack1 head1);
))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
(match (cfg.steps.weak) with
| true -> begin
(match (((env), (stack))) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let uu___159_13869 = x
in {FStar_Syntax_Syntax.ppname = uu___159_13869.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___159_13869.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t2)))
end
| uu____13870 -> begin
(

let uu____13885 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____13885))
end)
end
| uu____13886 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____13888 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____13888) with
| (closing, f1) -> begin
(

let f2 = (norm cfg ((dummy)::env) [] f1)
in (

let t2 = (

let uu____13915 = (

let uu____13916 = (

let uu____13923 = (FStar_Syntax_Subst.close closing f2)
in (((

let uu___160_13929 = x
in {FStar_Syntax_Syntax.ppname = uu___160_13929.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_13929.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____13923)))
in FStar_Syntax_Syntax.Tm_refine (uu____13916))
in (mk uu____13915 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t2)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let uu____13948 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____13948))
end
| uu____13949 -> begin
(

let uu____13950 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____13950) with
| (bs1, c1) -> begin
(

let c2 = (

let uu____13958 = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____13982 -> (dummy)::env1) env))
in (norm_comp cfg uu____13958 c1))
in (

let t2 = (

let uu____14004 = (norm_binders cfg env bs1)
in (FStar_Syntax_Util.arrow uu____14004 c2))
in (rebuild cfg env stack t2)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when cfg.steps.unascribe -> begin
(norm cfg env stack t11)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) -> begin
(match (stack) with
| (Match (uu____14115))::uu____14116 -> begin
((log cfg (fun uu____14129 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (Arg (uu____14130))::uu____14131 -> begin
((log cfg (fun uu____14142 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (App (uu____14143, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____14144; FStar_Syntax_Syntax.vars = uu____14145}, uu____14146, uu____14147))::uu____14148 -> begin
((log cfg (fun uu____14155 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (MemoLazy (uu____14156))::uu____14157 -> begin
((log cfg (fun uu____14168 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| uu____14169 -> begin
((log cfg (fun uu____14172 -> (FStar_Util.print_string "+++ Keeping ascription \n")));
(

let t12 = (norm cfg env [] t11)
in ((log cfg (fun uu____14176 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc1 = (match (tc) with
| FStar_Util.Inl (t2) -> begin
(

let uu____14201 = (norm cfg env [] t2)
in FStar_Util.Inl (uu____14201))
end
| FStar_Util.Inr (c) -> begin
(

let uu____14211 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____14211))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (norm cfg env []))
in (match (stack) with
| (Cfg (cfg1))::stack1 -> begin
(

let t2 = (

let uu____14230 = (

let uu____14231 = (

let uu____14258 = (FStar_Syntax_Util.unascribe t12)
in ((uu____14258), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____14231))
in (mk uu____14230 t1.FStar_Syntax_Syntax.pos))
in (norm cfg1 env stack1 t2))
end
| uu____14293 -> begin
(

let uu____14294 = (

let uu____14295 = (

let uu____14296 = (

let uu____14323 = (FStar_Syntax_Util.unascribe t12)
in ((uu____14323), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____14296))
in (mk uu____14295 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack uu____14294))
end)));
));
)
end)
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack1 = (Match (((env), (branches), (cfg), (t1.FStar_Syntax_Syntax.pos))))::stack
in (

let cfg1 = (match (((cfg.steps.iota && cfg.steps.weakly_reduce_scrutinee) && (not (cfg.steps.weak)))) with
| true -> begin
(

let uu___161_14400 = cfg
in {steps = (

let uu___162_14403 = cfg.steps
in {beta = uu___162_14403.beta; iota = uu___162_14403.iota; zeta = uu___162_14403.zeta; weak = true; hnf = uu___162_14403.hnf; primops = uu___162_14403.primops; do_not_unfold_pure_lets = uu___162_14403.do_not_unfold_pure_lets; unfold_until = uu___162_14403.unfold_until; unfold_only = uu___162_14403.unfold_only; unfold_fully = uu___162_14403.unfold_fully; unfold_attr = uu___162_14403.unfold_attr; unfold_tac = uu___162_14403.unfold_tac; pure_subterms_within_computations = uu___162_14403.pure_subterms_within_computations; simplify = uu___162_14403.simplify; erase_universes = uu___162_14403.erase_universes; allow_unbound_universes = uu___162_14403.allow_unbound_universes; reify_ = uu___162_14403.reify_; compress_uvars = uu___162_14403.compress_uvars; no_full_norm = uu___162_14403.no_full_norm; check_no_uvars = uu___162_14403.check_no_uvars; unmeta = uu___162_14403.unmeta; unascribe = uu___162_14403.unascribe; in_full_norm_request = uu___162_14403.in_full_norm_request; weakly_reduce_scrutinee = uu___162_14403.weakly_reduce_scrutinee}); tcenv = uu___161_14400.tcenv; debug = uu___161_14400.debug; delta_level = uu___161_14400.delta_level; primitive_steps = uu___161_14400.primitive_steps; strong = uu___161_14400.strong; memoize_lazy = uu___161_14400.memoize_lazy; normalize_pure_lets = uu___161_14400.normalize_pure_lets})
end
| uu____14404 -> begin
cfg
end)
in (norm cfg1 env stack1 head1)))
end
| FStar_Syntax_Syntax.Tm_let ((b, lbs), lbody) when ((FStar_Syntax_Syntax.is_top_level lbs) && cfg.steps.compress_uvars) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____14439 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____14439) with
| (openings, lbunivs) -> begin
(

let cfg1 = (

let uu___163_14459 = cfg
in (

let uu____14460 = (FStar_TypeChecker_Env.push_univ_vars cfg.tcenv lbunivs)
in {steps = uu___163_14459.steps; tcenv = uu____14460; debug = uu___163_14459.debug; delta_level = uu___163_14459.delta_level; primitive_steps = uu___163_14459.primitive_steps; strong = uu___163_14459.strong; memoize_lazy = uu___163_14459.memoize_lazy; normalize_pure_lets = uu___163_14459.normalize_pure_lets}))
in (

let norm1 = (fun t2 -> (

let uu____14467 = (

let uu____14468 = (FStar_Syntax_Subst.subst openings t2)
in (norm cfg1 env [] uu____14468))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____14467)))
in (

let lbtyp = (norm1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (norm1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___164_14471 = lb
in {FStar_Syntax_Syntax.lbname = uu___164_14471.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___164_14471.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___164_14471.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___164_14471.FStar_Syntax_Syntax.lbpos})))))
end)))))
in (

let uu____14472 = (mk (FStar_Syntax_Syntax.Tm_let (((((b), (lbs1))), (lbody)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____14472)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____14483, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____14484); FStar_Syntax_Syntax.lbunivs = uu____14485; FStar_Syntax_Syntax.lbtyp = uu____14486; FStar_Syntax_Syntax.lbeff = uu____14487; FStar_Syntax_Syntax.lbdef = uu____14488; FStar_Syntax_Syntax.lbattrs = uu____14489; FStar_Syntax_Syntax.lbpos = uu____14490})::uu____14491), uu____14492) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n1 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____14532 = ((not (cfg.steps.do_not_unfold_pure_lets)) && (((cfg.steps.pure_subterms_within_computations && (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs FStar_Parser_Const.inline_let_attr)) || ((FStar_Syntax_Util.is_pure_effect n1) && (cfg.normalize_pure_lets || (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs FStar_Parser_Const.inline_let_attr)))) || ((FStar_Syntax_Util.is_ghost_effect n1) && (not (cfg.steps.pure_subterms_within_computations)))))
in (match (uu____14532) with
| true -> begin
(

let binder = (

let uu____14534 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____14534))
in (

let env1 = (

let uu____14544 = (

let uu____14551 = (

let uu____14552 = (

let uu____14583 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____14583), (false)))
in Clos (uu____14552))
in ((FStar_Pervasives_Native.Some (binder)), (uu____14551)))
in (uu____14544)::env)
in ((log cfg (fun uu____14678 -> (FStar_Util.print_string "+++ Reducing Tm_let\n")));
(norm cfg env1 stack body);
)))
end
| uu____14679 -> begin
(match (cfg.steps.weak) with
| true -> begin
((log cfg (fun uu____14682 -> (FStar_Util.print_string "+++ Not touching Tm_let\n")));
(

let uu____14683 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____14683));
)
end
| uu____14684 -> begin
(

let uu____14685 = (

let uu____14690 = (

let uu____14691 = (

let uu____14696 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____14696 FStar_Syntax_Syntax.mk_binder))
in (uu____14691)::[])
in (FStar_Syntax_Subst.open_term uu____14690 body))
in (match (uu____14685) with
| (bs, body1) -> begin
((log cfg (fun uu____14713 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- type")));
(

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let x = (

let uu____14721 = (FStar_List.hd bs)
in (FStar_Pervasives_Native.fst uu____14721))
in FStar_Util.Inl ((

let uu___165_14731 = x
in {FStar_Syntax_Syntax.ppname = uu___165_14731.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___165_14731.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
in ((log cfg (fun uu____14734 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- definiens\n")));
(

let lb1 = (

let uu___166_14736 = lb
in (

let uu____14737 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___166_14736.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___166_14736.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____14737; FStar_Syntax_Syntax.lbattrs = uu___166_14736.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___166_14736.FStar_Syntax_Syntax.lbpos}))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env1 uu____14772 -> (dummy)::env1) env))
in (

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___167_14795 = cfg
in {steps = uu___167_14795.steps; tcenv = uu___167_14795.tcenv; debug = uu___167_14795.debug; delta_level = uu___167_14795.delta_level; primitive_steps = uu___167_14795.primitive_steps; strong = true; memoize_lazy = uu___167_14795.memoize_lazy; normalize_pure_lets = uu___167_14795.normalize_pure_lets})
in ((log cfg1 (fun uu____14798 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- body\n")));
(norm cfg1 env' ((Let (((env), (bs), (lb1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1);
)))));
)));
)
end))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), body) when (cfg.steps.compress_uvars || ((not (cfg.steps.zeta)) && cfg.steps.pure_subterms_within_computations)) -> begin
(

let uu____14815 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____14815) with
| (lbs1, body1) -> begin
(

let lbs2 = (FStar_List.map (fun lb -> (

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let uu____14851 = (

let uu___168_14852 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___168_14852.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___168_14852.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})
in FStar_Util.Inl (uu____14851))
in (

let uu____14853 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____14853) with
| (xs, def_body, lopt) -> begin
(

let xs1 = (norm_binders cfg env xs)
in (

let env1 = (

let uu____14879 = (FStar_List.map (fun uu____14895 -> dummy) lbs1)
in (

let uu____14896 = (

let uu____14905 = (FStar_List.map (fun uu____14925 -> dummy) xs1)
in (FStar_List.append uu____14905 env))
in (FStar_List.append uu____14879 uu____14896)))
in (

let def_body1 = (norm cfg env1 [] def_body)
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____14949 = (

let uu___169_14950 = rc
in (

let uu____14951 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env1 []))
in {FStar_Syntax_Syntax.residual_effect = uu___169_14950.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____14951; FStar_Syntax_Syntax.residual_flags = uu___169_14950.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____14949))
end
| uu____14960 -> begin
lopt
end)
in (

let def = (FStar_Syntax_Util.abs xs1 def_body1 lopt1)
in (

let uu___170_14966 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___170_14966.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___170_14966.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___170_14966.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___170_14966.FStar_Syntax_Syntax.lbpos}))))))
end))))) lbs1)
in (

let env' = (

let uu____14976 = (FStar_List.map (fun uu____14992 -> dummy) lbs2)
in (FStar_List.append uu____14976 env))
in (

let body2 = (norm cfg env' [] body1)
in (

let uu____15000 = (FStar_Syntax_Subst.close_let_rec lbs2 body2)
in (match (uu____15000) with
| (lbs3, body3) -> begin
(

let t2 = (

let uu___171_15016 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (body3))); FStar_Syntax_Syntax.pos = uu___171_15016.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___171_15016.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack t2))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (not (cfg.steps.zeta)) -> begin
(

let uu____15045 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____15045))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____15064 = (FStar_List.fold_right (fun lb uu____15140 -> (match (uu____15140) with
| (rec_env, memos, i) -> begin
(

let bv = (

let uu___172_15261 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___172_15261.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___172_15261.FStar_Syntax_Syntax.sort})
in (

let f_i = (FStar_Syntax_Syntax.bv_to_tm bv)
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t1.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let rec_env1 = (((FStar_Pervasives_Native.None), (Clos (((env), (fix_f_i), (memo), (true))))))::rec_env
in ((rec_env1), ((memo)::memos), ((i + (Prims.parse_int "1")))))))))
end)) (FStar_Pervasives_Native.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (uu____15064) with
| (rec_env, memos, uu____15488) -> begin
(

let uu____15541 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (FStar_Pervasives_Native.Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (FStar_Pervasives_Native.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env1 -> (

let uu____15864 = (

let uu____15871 = (

let uu____15872 = (

let uu____15903 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____15903), (false)))
in Clos (uu____15872))
in ((FStar_Pervasives_Native.None), (uu____15871)))
in (uu____15864)::env1)) (FStar_Pervasives_Native.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head1, m) -> begin
((log cfg (fun uu____16007 -> (

let uu____16008 = (FStar_Syntax_Print.metadata_to_string m)
in (FStar_Util.print1 ">> metadata = %s\n" uu____16008))));
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m1, t2) -> begin
(reduce_impure_comp cfg env stack head1 (FStar_Util.Inl (m1)) t2)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) -> begin
(reduce_impure_comp cfg env stack head1 (FStar_Util.Inr (((m1), (m')))) t2)
end
| uu____16030 -> begin
(match (cfg.steps.unmeta) with
| true -> begin
(norm cfg env stack head1)
end
| uu____16031 -> begin
(match (stack) with
| (uu____16032)::uu____16033 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____16038) -> begin
(norm cfg env ((Meta (((env), (m), (r))))::stack) head1)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args1 = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((env), (FStar_Syntax_Syntax.Meta_pattern (args1)), (t1.FStar_Syntax_Syntax.pos))))::stack) head1))
end
| uu____16061 -> begin
(norm cfg env stack head1)
end)
end
| [] -> begin
(

let head2 = (norm cfg env [] head1)
in (

let m1 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let uu____16075 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (uu____16075))
end
| uu____16086 -> begin
m
end)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_meta (((head2), (m1)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t2))))
end)
end)
end);
)
end
| FStar_Syntax_Syntax.Tm_delayed (uu____16092) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (norm cfg env stack t2))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____16118) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____16120) -> begin
(match (cfg.steps.check_no_uvars) with
| true -> begin
(

let uu____16121 = (

let uu____16122 = (FStar_Range.string_of_range t2.FStar_Syntax_Syntax.pos)
in (

let uu____16123 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s) CheckNoUvars: Unexpected unification variable remains: %s" uu____16122 uu____16123)))
in (failwith uu____16121))
end
| uu____16124 -> begin
(rebuild cfg env stack t2)
end)
end
| uu____16125 -> begin
(norm cfg env stack t2)
end))
end);
)))
and do_unfold_fv : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.qninfo  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t0 qninfo f -> (

let r_env = (

let uu____16133 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv uu____16133))
in (

let uu____16134 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.delta_level f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (match (uu____16134) with
| FStar_Pervasives_Native.None -> begin
((log cfg (fun uu____16147 -> (FStar_Util.print "Tm_fvar case 2\n" [])));
(rebuild cfg env stack t0);
)
end
| FStar_Pervasives_Native.Some (us, t) -> begin
((log cfg (fun uu____16158 -> (

let uu____16159 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____16160 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16159 uu____16160)))));
(

let t1 = (match (((Prims.op_Equality cfg.steps.unfold_until (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant))) && (not (cfg.steps.unfold_tac)))) with
| true -> begin
t
end
| uu____16164 -> begin
(

let uu____16165 = (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Subst.set_use_range uu____16165 t))
end)
in (

let n1 = (FStar_List.length us)
in (match ((n1 > (Prims.parse_int "0"))) with
| true -> begin
(match (stack) with
| (UnivArgs (us', uu____16174))::stack1 -> begin
(

let env1 = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env1 u -> (((FStar_Pervasives_Native.None), (Univ (u))))::env1) env))
in (norm cfg env1 stack1 t1))
end
| uu____16229 when (cfg.steps.erase_universes || cfg.steps.allow_unbound_universes) -> begin
(norm cfg env stack t1)
end
| uu____16230 -> begin
(

let uu____16231 = (

let uu____16232 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____16232))
in (failwith uu____16231))
end)
end
| uu____16233 -> begin
(norm cfg env stack t1)
end)));
)
end))))
and reduce_impure_comp : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.monad_name, (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name)) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun cfg env stack head1 m t -> (

let t1 = (norm cfg env [] t)
in (

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (match (cfg.steps.pure_subterms_within_computations) with
| true -> begin
(

let new_steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::(Inlining)::[]
in (

let uu___173_16256 = cfg
in (

let uu____16257 = (FStar_List.fold_right fstep_add_one new_steps cfg.steps)
in {steps = uu____16257; tcenv = uu___173_16256.tcenv; debug = uu___173_16256.debug; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___173_16256.primitive_steps; strong = uu___173_16256.strong; memoize_lazy = uu___173_16256.memoize_lazy; normalize_pure_lets = uu___173_16256.normalize_pure_lets})))
end
| uu____16258 -> begin
(

let uu___174_16259 = cfg
in {steps = (

let uu___175_16262 = cfg.steps
in {beta = uu___175_16262.beta; iota = uu___175_16262.iota; zeta = false; weak = uu___175_16262.weak; hnf = uu___175_16262.hnf; primops = uu___175_16262.primops; do_not_unfold_pure_lets = uu___175_16262.do_not_unfold_pure_lets; unfold_until = uu___175_16262.unfold_until; unfold_only = uu___175_16262.unfold_only; unfold_fully = uu___175_16262.unfold_fully; unfold_attr = uu___175_16262.unfold_attr; unfold_tac = uu___175_16262.unfold_tac; pure_subterms_within_computations = uu___175_16262.pure_subterms_within_computations; simplify = uu___175_16262.simplify; erase_universes = uu___175_16262.erase_universes; allow_unbound_universes = uu___175_16262.allow_unbound_universes; reify_ = uu___175_16262.reify_; compress_uvars = uu___175_16262.compress_uvars; no_full_norm = uu___175_16262.no_full_norm; check_no_uvars = uu___175_16262.check_no_uvars; unmeta = uu___175_16262.unmeta; unascribe = uu___175_16262.unascribe; in_full_norm_request = uu___175_16262.in_full_norm_request; weakly_reduce_scrutinee = uu___175_16262.weakly_reduce_scrutinee}); tcenv = uu___174_16259.tcenv; debug = uu___174_16259.debug; delta_level = uu___174_16259.delta_level; primitive_steps = uu___174_16259.primitive_steps; strong = uu___174_16259.strong; memoize_lazy = uu___174_16259.memoize_lazy; normalize_pure_lets = uu___174_16259.normalize_pure_lets})
end)
in (

let metadata = (match (m) with
| FStar_Util.Inl (m1) -> begin
FStar_Syntax_Syntax.Meta_monadic (((m1), (t1)))
end
| FStar_Util.Inr (m1, m') -> begin
FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t1)))
end)
in (norm cfg1 env ((Meta (((env), (metadata), (head1.FStar_Syntax_Syntax.pos))))::stack1) head1))))))
and do_reify_monadic : (unit  ->  FStar_Syntax_Syntax.term)  ->  cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun fallback cfg env stack head1 m t -> (

let head0 = head1
in (

let head2 = (FStar_Syntax_Util.unascribe head1)
in ((log cfg (fun uu____16296 -> (

let uu____16297 = (FStar_Syntax_Print.tag_of_term head2)
in (

let uu____16298 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print2 "Reifying: (%s) %s\n" uu____16297 uu____16298)))));
(

let head3 = (FStar_Syntax_Util.unmeta_safe head2)
in (

let uu____16300 = (

let uu____16301 = (FStar_Syntax_Subst.compress head3)
in uu____16301.FStar_Syntax_Syntax.n)
in (match (uu____16300) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (

let uu____16319 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m)
in (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv uu____16319))
in (

let uu____16320 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____16320) with
| (uu____16321, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____16331) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____16341 = (

let uu____16342 = (FStar_Syntax_Subst.compress e)
in uu____16342.FStar_Syntax_Syntax.n)
in (match (uu____16341) with
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____16348, uu____16349)) -> begin
(

let uu____16358 = (

let uu____16359 = (FStar_Syntax_Subst.compress e1)
in uu____16359.FStar_Syntax_Syntax.n)
in (match (uu____16358) with
| FStar_Syntax_Syntax.Tm_meta (e2, FStar_Syntax_Syntax.Meta_monadic_lift (uu____16365, msrc, uu____16367)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____16376 = (FStar_Syntax_Subst.compress e2)
in FStar_Pervasives_Native.Some (uu____16376))
end
| uu____16377 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____16378 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____16379 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____16379) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let lb1 = (

let uu___176_16384 = lb
in {FStar_Syntax_Syntax.lbname = uu___176_16384.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___176_16384.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___176_16384.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu___176_16384.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___176_16384.FStar_Syntax_Syntax.lbpos})
in (

let uu____16385 = (FStar_List.tl stack)
in (

let uu____16386 = (

let uu____16387 = (

let uu____16394 = (

let uu____16395 = (

let uu____16408 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb1)::[]))), (uu____16408)))
in FStar_Syntax_Syntax.Tm_let (uu____16395))
in (FStar_Syntax_Syntax.mk uu____16394))
in (uu____16387 FStar_Pervasives_Native.None head3.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____16385 uu____16386))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____16424 = (

let uu____16425 = (is_return body)
in (match (uu____16425) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.pos = uu____16429; FStar_Syntax_Syntax.vars = uu____16430}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____16433 -> begin
false
end))
in (match (uu____16424) with
| true -> begin
(norm cfg env stack lb.FStar_Syntax_Syntax.lbdef)
end
| uu____16436 -> begin
(

let rng = head3.FStar_Syntax_Syntax.pos
in (

let head4 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body1 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body_rc = {FStar_Syntax_Syntax.residual_effect = m; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = []}
in (

let body2 = (

let uu____16458 = (

let uu____16465 = (

let uu____16466 = (

let uu____16483 = (

let uu____16490 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____16490)::[])
in ((uu____16483), (body1), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____16466))
in (FStar_Syntax_Syntax.mk uu____16465))
in (uu____16458 FStar_Pervasives_Native.None body1.FStar_Syntax_Syntax.pos))
in (

let close1 = (closure_as_term cfg env)
in (

let bind_inst = (

let uu____16512 = (

let uu____16513 = (FStar_Syntax_Subst.compress bind_repr)
in uu____16513.FStar_Syntax_Syntax.n)
in (match (uu____16512) with
| FStar_Syntax_Syntax.Tm_uinst (bind1, (uu____16519)::(uu____16520)::[]) -> begin
(

let uu____16525 = (

let uu____16532 = (

let uu____16533 = (

let uu____16540 = (

let uu____16541 = (

let uu____16542 = (close1 lb.FStar_Syntax_Syntax.lbtyp)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____16542))
in (

let uu____16543 = (

let uu____16546 = (

let uu____16547 = (close1 t)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____16547))
in (uu____16546)::[])
in (uu____16541)::uu____16543))
in ((bind1), (uu____16540)))
in FStar_Syntax_Syntax.Tm_uinst (uu____16533))
in (FStar_Syntax_Syntax.mk uu____16532))
in (uu____16525 FStar_Pervasives_Native.None rng))
end
| uu____16553 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let maybe_range_arg = (

let uu____16559 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____16559) with
| true -> begin
(

let uu____16562 = (

let uu____16563 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range lb.FStar_Syntax_Syntax.lbpos lb.FStar_Syntax_Syntax.lbpos)
in (FStar_Syntax_Syntax.as_arg uu____16563))
in (

let uu____16564 = (

let uu____16567 = (

let uu____16568 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range body2.FStar_Syntax_Syntax.pos body2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.as_arg uu____16568))
in (uu____16567)::[])
in (uu____16562)::uu____16564))
end
| uu____16569 -> begin
[]
end))
in (

let reified = (

let uu____16573 = (

let uu____16580 = (

let uu____16581 = (

let uu____16596 = (

let uu____16605 = (

let uu____16608 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____16609 = (

let uu____16612 = (FStar_Syntax_Syntax.as_arg t)
in (uu____16612)::[])
in (uu____16608)::uu____16609))
in (

let uu____16613 = (

let uu____16616 = (

let uu____16619 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____16620 = (

let uu____16623 = (FStar_Syntax_Syntax.as_arg head4)
in (

let uu____16624 = (

let uu____16627 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____16628 = (

let uu____16631 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____16631)::[])
in (uu____16627)::uu____16628))
in (uu____16623)::uu____16624))
in (uu____16619)::uu____16620))
in (FStar_List.append maybe_range_arg uu____16616))
in (FStar_List.append uu____16605 uu____16613)))
in ((bind_inst), (uu____16596)))
in FStar_Syntax_Syntax.Tm_app (uu____16581))
in (FStar_Syntax_Syntax.mk uu____16580))
in (uu____16573 FStar_Pervasives_Native.None rng))
in ((log cfg (fun uu____16649 -> (

let uu____16650 = (FStar_Syntax_Print.term_to_string head0)
in (

let uu____16651 = (FStar_Syntax_Print.term_to_string reified)
in (FStar_Util.print2 "Reified (1) <%s> to %s\n" uu____16650 uu____16651)))));
(

let uu____16652 = (FStar_List.tl stack)
in (norm cfg env uu____16652 reified));
))))))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head_app, args) -> begin
(

let ed = (

let uu____16676 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m)
in (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv uu____16676))
in (

let uu____16677 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____16677) with
| (uu____16678, bind_repr) -> begin
(

let maybe_unfold_action = (fun head4 -> (

let maybe_extract_fv = (fun t1 -> (

let t2 = (

let uu____16715 = (

let uu____16716 = (FStar_Syntax_Subst.compress t1)
in uu____16716.FStar_Syntax_Syntax.n)
in (match (uu____16715) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____16720) -> begin
t2
end
| uu____16725 -> begin
head4
end))
in (

let uu____16726 = (

let uu____16727 = (FStar_Syntax_Subst.compress t2)
in uu____16727.FStar_Syntax_Syntax.n)
in (match (uu____16726) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____16733 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____16734 = (maybe_extract_fv head4)
in (match (uu____16734) with
| FStar_Pervasives_Native.Some (x) when (

let uu____16744 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv uu____16744)) -> begin
(

let head5 = (norm cfg env [] head4)
in (

let action_unfolded = (

let uu____16749 = (maybe_extract_fv head5)
in (match (uu____16749) with
| FStar_Pervasives_Native.Some (uu____16754) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____16755 -> begin
FStar_Pervasives_Native.Some (false)
end))
in ((head5), (action_unfolded))))
end
| uu____16760 -> begin
((head4), (FStar_Pervasives_Native.None))
end))))
in ((

let is_arg_impure = (fun uu____16775 -> (match (uu____16775) with
| (e, q) -> begin
(

let uu____16782 = (

let uu____16783 = (FStar_Syntax_Subst.compress e)
in uu____16783.FStar_Syntax_Syntax.n)
in (match (uu____16782) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t')) -> begin
(

let uu____16798 = (FStar_Syntax_Util.is_pure_effect m1)
in (not (uu____16798)))
end
| uu____16799 -> begin
false
end))
end))
in (

let uu____16800 = (

let uu____16801 = (

let uu____16810 = (FStar_Syntax_Syntax.as_arg head_app)
in (uu____16810)::args)
in (FStar_Util.for_some is_arg_impure uu____16801))
in (match (uu____16800) with
| true -> begin
(

let uu____16829 = (

let uu____16830 = (FStar_Syntax_Print.term_to_string head3)
in (FStar_Util.format1 "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n" uu____16830))
in (failwith uu____16829))
end
| uu____16831 -> begin
()
end)));
(

let uu____16832 = (maybe_unfold_action head_app)
in (match (uu____16832) with
| (head_app1, found_action) -> begin
(

let mk1 = (fun tm -> (FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None head3.FStar_Syntax_Syntax.pos))
in (

let body = (mk1 (FStar_Syntax_Syntax.Tm_app (((head_app1), (args)))))
in (

let body1 = (match (found_action) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Util.mk_reify body)
end
| FStar_Pervasives_Native.Some (false) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))))
end
| FStar_Pervasives_Native.Some (true) -> begin
body
end)
in ((log cfg (fun uu____16875 -> (

let uu____16876 = (FStar_Syntax_Print.term_to_string head0)
in (

let uu____16877 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print2 "Reified (2) <%s> to %s\n" uu____16876 uu____16877)))));
(

let uu____16878 = (FStar_List.tl stack)
in (norm cfg env uu____16878 body1));
))))
end));
))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (uu____16880)) -> begin
(do_reify_monadic fallback cfg env stack e m t)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (

let uu____16904 = (closure_as_term cfg env t')
in (reify_lift cfg e msrc mtgt uu____16904))
in ((log cfg (fun uu____16908 -> (

let uu____16909 = (FStar_Syntax_Print.term_to_string lifted)
in (FStar_Util.print1 "Reified lift to (2): %s\n" uu____16909))));
(

let uu____16910 = (FStar_List.tl stack)
in (norm cfg env uu____16910 lifted));
))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____17031 -> (match (uu____17031) with
| (pat, wopt, tm) -> begin
(

let uu____17079 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____17079)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches1)))) head3.FStar_Syntax_Syntax.pos)
in (

let uu____17111 = (FStar_List.tl stack)
in (norm cfg env uu____17111 tm))))
end
| uu____17112 -> begin
(fallback ())
end)));
))))
and reify_lift : cfg  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg e msrc mtgt t -> (

let env = cfg.tcenv
in ((log cfg (fun uu____17126 -> (

let uu____17127 = (FStar_Ident.string_of_lid msrc)
in (

let uu____17128 = (FStar_Ident.string_of_lid mtgt)
in (

let uu____17129 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17127 uu____17128 uu____17129))))));
(

let uu____17130 = ((FStar_Syntax_Util.is_pure_effect msrc) || (FStar_Syntax_Util.is_div_effect msrc))
in (match (uu____17130) with
| true -> begin
(

let ed = (

let uu____17132 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt)
in (FStar_TypeChecker_Env.get_effect_decl env uu____17132))
in (

let uu____17133 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____17133) with
| (uu____17134, return_repr) -> begin
(

let return_inst = (

let uu____17147 = (

let uu____17148 = (FStar_Syntax_Subst.compress return_repr)
in uu____17148.FStar_Syntax_Syntax.n)
in (match (uu____17147) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____17154)::[]) -> begin
(

let uu____17159 = (

let uu____17166 = (

let uu____17167 = (

let uu____17174 = (

let uu____17175 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____17175)::[])
in ((return_tm), (uu____17174)))
in FStar_Syntax_Syntax.Tm_uinst (uu____17167))
in (FStar_Syntax_Syntax.mk uu____17166))
in (uu____17159 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end
| uu____17181 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____17184 = (

let uu____17191 = (

let uu____17192 = (

let uu____17207 = (

let uu____17216 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____17217 = (

let uu____17220 = (FStar_Syntax_Syntax.as_arg e)
in (uu____17220)::[])
in (uu____17216)::uu____17217))
in ((return_inst), (uu____17207)))
in FStar_Syntax_Syntax.Tm_app (uu____17192))
in (FStar_Syntax_Syntax.mk uu____17191))
in (uu____17184 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____17234 -> begin
(

let uu____17235 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____17235) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17238 = (

let uu____17239 = (FStar_Ident.text_of_lid msrc)
in (

let uu____17240 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" uu____17239 uu____17240)))
in (failwith uu____17238))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____17241; FStar_TypeChecker_Env.mtarget = uu____17242; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____17243; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(

let uu____17265 = (

let uu____17266 = (FStar_Ident.text_of_lid msrc)
in (

let uu____17267 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)" uu____17266 uu____17267)))
in (failwith uu____17265))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____17268; FStar_TypeChecker_Env.mtarget = uu____17269; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____17270; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let uu____17305 = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let uu____17306 = (FStar_Syntax_Util.mk_reify e)
in (lift uu____17305 t FStar_Syntax_Syntax.tun uu____17306)))
end))
end));
)))
and norm_pattern_args : cfg  ->  env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____17362 -> (match (uu____17362) with
| (a, imp) -> begin
(

let uu____17373 = (norm cfg env [] a)
in ((uu____17373), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> ((log cfg (fun uu____17381 -> (

let uu____17382 = (FStar_Syntax_Print.comp_to_string comp)
in (

let uu____17383 = (FStar_Util.string_of_int (FStar_List.length env))
in (FStar_Util.print2 ">>> %s\nNormComp with with %s env elements" uu____17382 uu____17383)))));
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let t1 = (norm cfg env [] t)
in (

let uopt1 = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
(

let uu____17407 = (norm_universe cfg env u)
in (FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some (_0_18)) uu____17407))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let uu___177_17410 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t1), (uopt1))); FStar_Syntax_Syntax.pos = uu___177_17410.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___177_17410.FStar_Syntax_Syntax.vars})))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let t1 = (norm cfg env [] t)
in (

let uopt1 = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
(

let uu____17432 = (norm_universe cfg env u)
in (FStar_All.pipe_left (fun _0_19 -> FStar_Pervasives_Native.Some (_0_19)) uu____17432))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let uu___178_17435 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (((t1), (uopt1))); FStar_Syntax_Syntax.pos = uu___178_17435.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___178_17435.FStar_Syntax_Syntax.vars})))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (FStar_List.mapi (fun idx uu____17472 -> (match (uu____17472) with
| (a, i) -> begin
(

let uu____17483 = (norm cfg env [] a)
in ((uu____17483), (i)))
end)))
in (

let effect_args = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in (

let flags1 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___92_17501 -> (match (uu___92_17501) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____17505 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____17505))
end
| f -> begin
f
end))))
in (

let comp_univs = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let result_typ = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu___179_17513 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((

let uu___180_17516 = ct
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___180_17516.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = flags1})); FStar_Syntax_Syntax.pos = uu___179_17513.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___179_17513.FStar_Syntax_Syntax.vars}))))))
end);
))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env uu____17519 -> (match (uu____17519) with
| (x, imp) -> begin
(

let uu____17522 = (

let uu___181_17523 = x
in (

let uu____17524 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___181_17523.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___181_17523.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____17524}))
in ((uu____17522), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____17530 = (FStar_List.fold_left (fun uu____17564 b -> (match (uu____17564) with
| (nbs', env1) -> begin
(

let b1 = (norm_binder cfg env1 b)
in (((b1)::nbs'), ((dummy)::env1)))
end)) (([]), (env)) bs)
in (match (uu____17530) with
| (nbs, uu____17644) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags1 = (filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____17676 = (

let uu___182_17677 = rc
in (

let uu____17678 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___182_17677.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____17678; FStar_Syntax_Syntax.residual_flags = uu___182_17677.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____17676)))
end
| uu____17687 -> begin
lopt
end))
and maybe_simplify : cfg  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.option * closure) Prims.list  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (

let tm' = (maybe_simplify_aux cfg env stack tm)
in ((match (cfg.debug.b380) with
| true -> begin
(

let uu____17708 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____17709 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n" (match (cfg.steps.simplify) with
| true -> begin
""
end
| uu____17710 -> begin
"NOT "
end) uu____17708 uu____17709)))
end
| uu____17711 -> begin
()
end);
tm';
)))
and maybe_simplify_aux : cfg  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.option * closure) Prims.list  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (

let tm1 = (reduce_primops cfg env stack tm)
in (

let uu____17729 = (FStar_All.pipe_left Prims.op_Negation cfg.steps.simplify)
in (match (uu____17729) with
| true -> begin
tm1
end
| uu____17730 -> begin
(

let w = (fun t -> (

let uu___183_17743 = t
in {FStar_Syntax_Syntax.n = uu___183_17743.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = tm1.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___183_17743.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (

let uu____17754 = (

let uu____17755 = (FStar_Syntax_Util.unmeta t)
in uu____17755.FStar_Syntax_Syntax.n)
in (match (uu____17754) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_Pervasives_Native.Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid) -> begin
FStar_Pervasives_Native.Some (false)
end
| uu____17762 -> begin
FStar_Pervasives_Native.None
end)))
in (

let rec args_are_binders = (fun args bs -> (match (((args), (bs))) with
| (((t, uu____17811))::args1, ((bv, uu____17814))::bs1) -> begin
(

let uu____17848 = (

let uu____17849 = (FStar_Syntax_Subst.compress t)
in uu____17849.FStar_Syntax_Syntax.n)
in (match (uu____17848) with
| FStar_Syntax_Syntax.Tm_name (bv') -> begin
((FStar_Syntax_Syntax.bv_eq bv bv') && (args_are_binders args1 bs1))
end
| uu____17853 -> begin
false
end))
end
| ([], []) -> begin
true
end
| (uu____17874, uu____17875) -> begin
false
end))
in (

let is_applied = (fun bs t -> (

let uu____17915 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____17915) with
| (hd1, args) -> begin
(

let uu____17948 = (

let uu____17949 = (FStar_Syntax_Subst.compress hd1)
in uu____17949.FStar_Syntax_Syntax.n)
in (match (uu____17948) with
| FStar_Syntax_Syntax.Tm_name (bv) when (args_are_binders args bs) -> begin
FStar_Pervasives_Native.Some (bv)
end
| uu____17955 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (

let is_applied_maybe_squashed = (fun bs t -> (

let uu____17971 = (FStar_Syntax_Util.is_squash t)
in (match (uu____17971) with
| FStar_Pervasives_Native.Some (uu____17982, t') -> begin
(is_applied bs t')
end
| uu____17994 -> begin
(

let uu____18003 = (FStar_Syntax_Util.is_auto_squash t)
in (match (uu____18003) with
| FStar_Pervasives_Native.Some (uu____18014, t') -> begin
(is_applied bs t')
end
| uu____18026 -> begin
(is_applied bs t)
end))
end)))
in (

let is_quantified_const = (fun phi -> (

let uu____18045 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____18045) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid, ((p, uu____18052))::((q, uu____18054))::[])) when (FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid) -> begin
(

let uu____18081 = (FStar_Syntax_Util.destruct_typ_as_formula p)
in (match (uu____18081) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18086 = (

let uu____18087 = (FStar_Syntax_Subst.compress p)
in uu____18087.FStar_Syntax_Syntax.n)
in (match (uu____18086) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____18093 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (FStar_Syntax_Util.t_true))))::[]) q)
in FStar_Pervasives_Native.Some (uu____18093))
end
| uu____18096 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid1, ((p1, uu____18099))::[])) when (FStar_Ident.lid_equals lid1 FStar_Parser_Const.not_lid) -> begin
(

let uu____18116 = (

let uu____18117 = (FStar_Syntax_Subst.compress p1)
in uu____18117.FStar_Syntax_Syntax.n)
in (match (uu____18116) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____18123 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (FStar_Syntax_Util.t_false))))::[]) q)
in FStar_Pervasives_Native.Some (uu____18123))
end
| uu____18126 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (bs, pats, phi1)) -> begin
(

let uu____18130 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____18130) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18135 = (is_applied_maybe_squashed bs phi1)
in (match (uu____18135) with
| FStar_Pervasives_Native.Some (bv) -> begin
(

let ftrue = (FStar_Syntax_Util.abs bs FStar_Syntax_Util.t_true (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let uu____18144 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (ftrue))))::[]) q)
in FStar_Pervasives_Native.Some (uu____18144)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid1, ((p1, uu____18149))::[])) when (FStar_Ident.lid_equals lid1 FStar_Parser_Const.not_lid) -> begin
(

let uu____18166 = (is_applied_maybe_squashed bs p1)
in (match (uu____18166) with
| FStar_Pervasives_Native.Some (bv) -> begin
(

let ffalse = (FStar_Syntax_Util.abs bs FStar_Syntax_Util.t_false (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let uu____18175 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (ffalse))))::[]) q)
in FStar_Pervasives_Native.Some (uu____18175)))
end
| uu____18178 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____18181 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____18184 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____18187 -> begin
FStar_Pervasives_Native.None
end)))
in (

let is_const_match = (fun phi -> (

let uu____18200 = (

let uu____18201 = (FStar_Syntax_Subst.compress phi)
in uu____18201.FStar_Syntax_Syntax.n)
in (match (uu____18200) with
| FStar_Syntax_Syntax.Tm_match (uu____18206, (br)::brs) -> begin
(

let uu____18273 = br
in (match (uu____18273) with
| (uu____18290, uu____18291, e) -> begin
(

let r = (

let uu____18312 = (simp_t e)
in (match (uu____18312) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let uu____18318 = (FStar_List.for_all (fun uu____18336 -> (match (uu____18336) with
| (uu____18349, uu____18350, e') -> begin
(

let uu____18364 = (simp_t e')
in (Prims.op_Equality uu____18364 (FStar_Pervasives_Native.Some (b))))
end)) brs)
in (match (uu____18318) with
| true -> begin
FStar_Pervasives_Native.Some (b)
end
| uu____18371 -> begin
FStar_Pervasives_Native.None
end))
end))
in r)
end))
end
| uu____18372 -> begin
FStar_Pervasives_Native.None
end)))
in (

let maybe_auto_squash = (fun t -> (

let uu____18381 = (FStar_Syntax_Util.is_sub_singleton t)
in (match (uu____18381) with
| true -> begin
t
end
| uu____18384 -> begin
(FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t)
end)))
in (

let squashed_head_un_auto_squash_args = (fun t -> (

let maybe_un_auto_squash_arg = (fun uu____18412 -> (match (uu____18412) with
| (t1, q) -> begin
(

let uu____18425 = (FStar_Syntax_Util.is_auto_squash t1)
in (match (uu____18425) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t2) -> begin
((t2), (q))
end
| uu____18453 -> begin
((t1), (q))
end))
end))
in (

let uu____18464 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____18464) with
| (head1, args) -> begin
(

let args1 = (FStar_List.map maybe_un_auto_squash_arg args)
in (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))))
in (

let rec clearly_inhabited = (fun ty -> (

let uu____18530 = (

let uu____18531 = (FStar_Syntax_Util.unmeta ty)
in uu____18531.FStar_Syntax_Syntax.n)
in (match (uu____18530) with
| FStar_Syntax_Syntax.Tm_uinst (t, uu____18535) -> begin
(clearly_inhabited t)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____18540, c) -> begin
(clearly_inhabited (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in ((((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)))
end
| uu____18560 -> begin
false
end)))
in (

let simplify1 = (fun arg -> (

let uu____18585 = (simp_t (FStar_Pervasives_Native.fst arg))
in ((uu____18585), (arg))))
in (

let uu____18594 = (is_quantified_const tm1)
in (match (uu____18594) with
| FStar_Pervasives_Native.Some (tm2) -> begin
(

let uu____18598 = (norm cfg env [] tm2)
in (maybe_simplify_aux cfg env stack uu____18598))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____18599 = (

let uu____18600 = (FStar_Syntax_Subst.compress tm1)
in uu____18600.FStar_Syntax_Syntax.n)
in (match (uu____18599) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____18604; FStar_Syntax_Syntax.vars = uu____18605}, uu____18606); FStar_Syntax_Syntax.pos = uu____18607; FStar_Syntax_Syntax.vars = uu____18608}, args) -> begin
(

let uu____18634 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____18634) with
| true -> begin
(

let uu____18635 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____18635) with
| ((FStar_Pervasives_Native.Some (true), uu____18682))::((uu____18683, (arg, uu____18685)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____18734, (arg, uu____18736)))::((FStar_Pervasives_Native.Some (true), uu____18737))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (false), uu____18786))::(uu____18787)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____18838)::((FStar_Pervasives_Native.Some (false), uu____18839))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____18890 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____18903 -> begin
(

let uu____18904 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____18904) with
| true -> begin
(

let uu____18905 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____18905) with
| ((FStar_Pervasives_Native.Some (true), uu____18952))::(uu____18953)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____19004)::((FStar_Pervasives_Native.Some (true), uu____19005))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____19056))::((uu____19057, (arg, uu____19059)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____19108, (arg, uu____19110)))::((FStar_Pervasives_Native.Some (false), uu____19111))::[] -> begin
(maybe_auto_squash arg)
end
| uu____19160 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19173 -> begin
(

let uu____19174 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____19174) with
| true -> begin
(

let uu____19175 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19175) with
| (uu____19222)::((FStar_Pervasives_Native.Some (true), uu____19223))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____19274))::(uu____19275)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____19326))::((uu____19327, (arg, uu____19329)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____19378, (p, uu____19380)))::((uu____19381, (q, uu____19383)))::[] -> begin
(

let uu____19430 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____19430) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____19431 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19432 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19445 -> begin
(

let uu____19446 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)
in (match (uu____19446) with
| true -> begin
(

let uu____19447 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19447) with
| ((FStar_Pervasives_Native.Some (true), uu____19494))::((FStar_Pervasives_Native.Some (true), uu____19495))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____19546))::((FStar_Pervasives_Native.Some (false), uu____19547))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____19598))::((FStar_Pervasives_Native.Some (false), uu____19599))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____19650))::((FStar_Pervasives_Native.Some (true), uu____19651))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((uu____19702, (arg, uu____19704)))::((FStar_Pervasives_Native.Some (true), uu____19705))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (true), uu____19754))::((uu____19755, (arg, uu____19757)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____19806, (arg, uu____19808)))::((FStar_Pervasives_Native.Some (false), uu____19809))::[] -> begin
(

let uu____19858 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____19858))
end
| ((FStar_Pervasives_Native.Some (false), uu____19859))::((uu____19860, (arg, uu____19862)))::[] -> begin
(

let uu____19911 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____19911))
end
| ((uu____19912, (p, uu____19914)))::((uu____19915, (q, uu____19917)))::[] -> begin
(

let uu____19964 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____19964) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____19965 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19966 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19979 -> begin
(

let uu____19980 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____19980) with
| true -> begin
(

let uu____19981 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19981) with
| ((FStar_Pervasives_Native.Some (true), uu____20028))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____20059))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20090 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20103 -> begin
(

let uu____20104 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____20104) with
| true -> begin
(match (args) with
| ((t, uu____20106))::[] -> begin
(

let uu____20123 = (

let uu____20124 = (FStar_Syntax_Subst.compress t)
in uu____20124.FStar_Syntax_Syntax.n)
in (match (uu____20123) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20127)::[], body, uu____20129) -> begin
(

let uu____20156 = (simp_t body)
in (match (uu____20156) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20159 -> begin
tm1
end))
end
| uu____20162 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____20164))))::((t, uu____20166))::[] -> begin
(

let uu____20193 = (

let uu____20194 = (FStar_Syntax_Subst.compress t)
in uu____20194.FStar_Syntax_Syntax.n)
in (match (uu____20193) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20197)::[], body, uu____20199) -> begin
(

let uu____20226 = (simp_t body)
in (match (uu____20226) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____20229 -> begin
tm1
end))
end
| uu____20232 -> begin
tm1
end))
end
| uu____20233 -> begin
tm1
end)
end
| uu____20242 -> begin
(

let uu____20243 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____20243) with
| true -> begin
(match (args) with
| ((t, uu____20245))::[] -> begin
(

let uu____20262 = (

let uu____20263 = (FStar_Syntax_Subst.compress t)
in uu____20263.FStar_Syntax_Syntax.n)
in (match (uu____20262) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20266)::[], body, uu____20268) -> begin
(

let uu____20295 = (simp_t body)
in (match (uu____20295) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____20298 -> begin
tm1
end))
end
| uu____20301 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____20303))))::((t, uu____20305))::[] -> begin
(

let uu____20332 = (

let uu____20333 = (FStar_Syntax_Subst.compress t)
in uu____20333.FStar_Syntax_Syntax.n)
in (match (uu____20332) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20336)::[], body, uu____20338) -> begin
(

let uu____20365 = (simp_t body)
in (match (uu____20365) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.Some (true) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20368 -> begin
tm1
end))
end
| uu____20371 -> begin
tm1
end))
end
| uu____20372 -> begin
tm1
end)
end
| uu____20381 -> begin
(

let uu____20382 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____20382) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____20383; FStar_Syntax_Syntax.vars = uu____20384}, uu____20385))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____20402; FStar_Syntax_Syntax.vars = uu____20403}, uu____20404))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____20421 -> begin
tm1
end)
end
| uu____20430 -> begin
(

let uu____20431 = (FStar_Syntax_Util.is_auto_squash tm1)
in (match (uu____20431) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t) when (FStar_Syntax_Util.is_sub_singleton t) -> begin
t
end
| uu____20451 -> begin
(reduce_equality cfg env stack tm1)
end))
end))
end))
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____20461; FStar_Syntax_Syntax.vars = uu____20462}, args) -> begin
(

let uu____20484 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____20484) with
| true -> begin
(

let uu____20485 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____20485) with
| ((FStar_Pervasives_Native.Some (true), uu____20532))::((uu____20533, (arg, uu____20535)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____20584, (arg, uu____20586)))::((FStar_Pervasives_Native.Some (true), uu____20587))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (false), uu____20636))::(uu____20637)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____20688)::((FStar_Pervasives_Native.Some (false), uu____20689))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____20740 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20753 -> begin
(

let uu____20754 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____20754) with
| true -> begin
(

let uu____20755 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____20755) with
| ((FStar_Pervasives_Native.Some (true), uu____20802))::(uu____20803)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____20854)::((FStar_Pervasives_Native.Some (true), uu____20855))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____20906))::((uu____20907, (arg, uu____20909)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____20958, (arg, uu____20960)))::((FStar_Pervasives_Native.Some (false), uu____20961))::[] -> begin
(maybe_auto_squash arg)
end
| uu____21010 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21023 -> begin
(

let uu____21024 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____21024) with
| true -> begin
(

let uu____21025 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____21025) with
| (uu____21072)::((FStar_Pervasives_Native.Some (true), uu____21073))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____21124))::(uu____21125)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____21176))::((uu____21177, (arg, uu____21179)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____21228, (p, uu____21230)))::((uu____21231, (q, uu____21233)))::[] -> begin
(

let uu____21280 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____21280) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____21281 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21282 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21295 -> begin
(

let uu____21296 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)
in (match (uu____21296) with
| true -> begin
(

let uu____21297 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____21297) with
| ((FStar_Pervasives_Native.Some (true), uu____21344))::((FStar_Pervasives_Native.Some (true), uu____21345))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____21396))::((FStar_Pervasives_Native.Some (false), uu____21397))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____21448))::((FStar_Pervasives_Native.Some (false), uu____21449))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____21500))::((FStar_Pervasives_Native.Some (true), uu____21501))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((uu____21552, (arg, uu____21554)))::((FStar_Pervasives_Native.Some (true), uu____21555))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (true), uu____21604))::((uu____21605, (arg, uu____21607)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____21656, (arg, uu____21658)))::((FStar_Pervasives_Native.Some (false), uu____21659))::[] -> begin
(

let uu____21708 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____21708))
end
| ((FStar_Pervasives_Native.Some (false), uu____21709))::((uu____21710, (arg, uu____21712)))::[] -> begin
(

let uu____21761 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____21761))
end
| ((uu____21762, (p, uu____21764)))::((uu____21765, (q, uu____21767)))::[] -> begin
(

let uu____21814 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____21814) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____21815 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21816 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21829 -> begin
(

let uu____21830 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____21830) with
| true -> begin
(

let uu____21831 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____21831) with
| ((FStar_Pervasives_Native.Some (true), uu____21878))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____21909))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____21940 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21953 -> begin
(

let uu____21954 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____21954) with
| true -> begin
(match (args) with
| ((t, uu____21956))::[] -> begin
(

let uu____21973 = (

let uu____21974 = (FStar_Syntax_Subst.compress t)
in uu____21974.FStar_Syntax_Syntax.n)
in (match (uu____21973) with
| FStar_Syntax_Syntax.Tm_abs ((uu____21977)::[], body, uu____21979) -> begin
(

let uu____22006 = (simp_t body)
in (match (uu____22006) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22009 -> begin
tm1
end))
end
| uu____22012 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____22014))))::((t, uu____22016))::[] -> begin
(

let uu____22043 = (

let uu____22044 = (FStar_Syntax_Subst.compress t)
in uu____22044.FStar_Syntax_Syntax.n)
in (match (uu____22043) with
| FStar_Syntax_Syntax.Tm_abs ((uu____22047)::[], body, uu____22049) -> begin
(

let uu____22076 = (simp_t body)
in (match (uu____22076) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____22079 -> begin
tm1
end))
end
| uu____22082 -> begin
tm1
end))
end
| uu____22083 -> begin
tm1
end)
end
| uu____22092 -> begin
(

let uu____22093 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____22093) with
| true -> begin
(match (args) with
| ((t, uu____22095))::[] -> begin
(

let uu____22112 = (

let uu____22113 = (FStar_Syntax_Subst.compress t)
in uu____22113.FStar_Syntax_Syntax.n)
in (match (uu____22112) with
| FStar_Syntax_Syntax.Tm_abs ((uu____22116)::[], body, uu____22118) -> begin
(

let uu____22145 = (simp_t body)
in (match (uu____22145) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____22148 -> begin
tm1
end))
end
| uu____22151 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____22153))))::((t, uu____22155))::[] -> begin
(

let uu____22182 = (

let uu____22183 = (FStar_Syntax_Subst.compress t)
in uu____22183.FStar_Syntax_Syntax.n)
in (match (uu____22182) with
| FStar_Syntax_Syntax.Tm_abs ((uu____22186)::[], body, uu____22188) -> begin
(

let uu____22215 = (simp_t body)
in (match (uu____22215) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.Some (true) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22218 -> begin
tm1
end))
end
| uu____22221 -> begin
tm1
end))
end
| uu____22222 -> begin
tm1
end)
end
| uu____22231 -> begin
(

let uu____22232 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____22232) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____22233; FStar_Syntax_Syntax.vars = uu____22234}, uu____22235))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____22252; FStar_Syntax_Syntax.vars = uu____22253}, uu____22254))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____22271 -> begin
tm1
end)
end
| uu____22280 -> begin
(

let uu____22281 = (FStar_Syntax_Util.is_auto_squash tm1)
in (match (uu____22281) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t) when (FStar_Syntax_Util.is_sub_singleton t) -> begin
t
end
| uu____22301 -> begin
(reduce_equality cfg env stack tm1)
end))
end))
end))
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let uu____22316 = (simp_t t)
in (match (uu____22316) with
| FStar_Pervasives_Native.Some (true) -> begin
bv.FStar_Syntax_Syntax.sort
end
| FStar_Pervasives_Native.Some (false) -> begin
tm1
end
| FStar_Pervasives_Native.None -> begin
tm1
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____22319) -> begin
(

let uu____22342 = (is_const_match tm1)
in (match (uu____22342) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.None -> begin
tm1
end))
end
| uu____22345 -> begin
tm1
end))
end)))))))))))))
end))))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> ((log cfg (fun uu____22355 -> ((

let uu____22357 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____22358 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____22359 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____22366 = (

let uu____22367 = (

let uu____22370 = (firstn (Prims.parse_int "4") stack)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____22370))
in (stack_to_string uu____22367))
in (FStar_Util.print4 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n" uu____22357 uu____22358 uu____22359 uu____22366)))));
(

let uu____22393 = (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("NormRebuild")))
in (match (uu____22393) with
| true -> begin
(

let uu____22394 = (FStar_Syntax_Util.unbound_variables t)
in (match (uu____22394) with
| [] -> begin
()
end
| bvs -> begin
((

let uu____22401 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____22402 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____22403 = (

let uu____22404 = (FStar_All.pipe_right bvs (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____22404 (FStar_String.concat ", ")))
in (FStar_Util.print3 "!!! Rebuild (%s) %s, free vars=%s\n" uu____22401 uu____22402 uu____22403))));
(failwith "DIE!");
)
end))
end
| uu____22413 -> begin
()
end));
)));
(

let t1 = (maybe_simplify cfg env stack t)
in (match (stack) with
| [] -> begin
t1
end
| (Debug (tm, time_then))::stack1 -> begin
((match (cfg.debug.print_normalized) with
| true -> begin
(

let time_now = (FStar_Util.now ())
in (

let uu____22422 = (

let uu____22423 = (

let uu____22424 = (FStar_Util.time_diff time_then time_now)
in (FStar_Pervasives_Native.snd uu____22424))
in (FStar_Util.string_of_int uu____22423))
in (

let uu____22429 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____22430 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n" uu____22422 uu____22429 uu____22430)))))
end
| uu____22431 -> begin
()
end);
(rebuild cfg env stack1 t1);
)
end
| (Cfg (cfg1))::stack1 -> begin
(rebuild cfg1 env stack1 t1)
end
| (Meta (uu____22436, m, r))::stack1 -> begin
(

let t2 = (mk (FStar_Syntax_Syntax.Tm_meta (((t1), (m)))) r)
in (rebuild cfg env stack1 t2))
end
| (MemoLazy (r))::stack1 -> begin
((set_memo cfg r ((env), (t1)));
(log cfg (fun uu____22487 -> (

let uu____22488 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____22488))));
(rebuild cfg env stack1 t1);
)
end
| (Let (env', bs, lb, r))::stack1 -> begin
(

let body = (FStar_Syntax_Subst.close bs t1)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) FStar_Pervasives_Native.None r)
in (rebuild cfg env' stack1 t2)))
end
| (Abs (env', bs, env'', lopt, r))::stack1 -> begin
(

let bs1 = (norm_binders cfg env' bs)
in (

let lopt1 = (norm_lcomp_opt cfg env'' lopt)
in (

let uu____22526 = (

let uu___184_22527 = (FStar_Syntax_Util.abs bs1 t1 lopt1)
in {FStar_Syntax_Syntax.n = uu___184_22527.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___184_22527.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 uu____22526))))
end
| (Arg (Univ (uu____22530), uu____22531, uu____22532))::uu____22533 -> begin
(failwith "Impossible")
end
| (Arg (Dummy, uu____22536, uu____22537))::uu____22538 -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack1 -> begin
(

let t2 = (FStar_Syntax_Syntax.mk_Tm_uinst t1 us)
in (rebuild cfg env stack1 t2))
end
| (Arg (Clos (env_arg, tm, uu____22553, uu____22554), aq, r))::stack1 when (

let uu____22604 = (head_of t1)
in (FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22604)) -> begin
(

let t2 = (

let uu____22608 = (

let uu____22613 = (

let uu____22614 = (closure_as_term cfg env_arg tm)
in ((uu____22614), (aq)))
in (FStar_Syntax_Syntax.extend_app t1 uu____22613))
in (uu____22608 FStar_Pervasives_Native.None r))
in (rebuild cfg env stack1 t2))
end
| (Arg (Clos (env_arg, tm, m, uu____22624), aq, r))::stack1 -> begin
((log cfg (fun uu____22677 -> (

let uu____22678 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____22678))));
(match ((not (cfg.steps.iota))) with
| true -> begin
(match (cfg.steps.hnf) with
| true -> begin
(

let arg = (closure_as_term cfg env_arg tm)
in (

let t2 = (FStar_Syntax_Syntax.extend_app t1 ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack1 t2)))
end
| uu____22685 -> begin
(

let stack2 = (App (((env), (t1), (aq), (r))))::stack1
in (norm cfg env_arg stack2 tm))
end)
end
| uu____22689 -> begin
(

let uu____22690 = (FStar_ST.op_Bang m)
in (match (uu____22690) with
| FStar_Pervasives_Native.None -> begin
(match (cfg.steps.hnf) with
| true -> begin
(

let arg = (closure_as_term cfg env_arg tm)
in (

let t2 = (FStar_Syntax_Syntax.extend_app t1 ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack1 t2)))
end
| uu____22796 -> begin
(

let stack2 = (MemoLazy (m))::(App (((env), (t1), (aq), (r))))::stack1
in (norm cfg env_arg stack2 tm))
end)
end
| FStar_Pervasives_Native.Some (uu____22833, a) -> begin
(

let t2 = (FStar_Syntax_Syntax.extend_app t1 ((a), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack1 t2))
end))
end);
)
end
| (App (env1, head1, aq, r))::stack' when (should_reify cfg stack) -> begin
(

let t0 = t1
in (

let fallback = (fun msg uu____22886 -> ((log cfg (fun uu____22890 -> (

let uu____22891 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not reifying%s: %s\n" msg uu____22891))));
(

let t2 = (FStar_Syntax_Syntax.extend_app head1 ((t1), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack' t2));
))
in (

let uu____22897 = (

let uu____22898 = (FStar_Syntax_Subst.compress t1)
in uu____22898.FStar_Syntax_Syntax.n)
in (match (uu____22897) with
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) -> begin
(do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty)
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, ty)) -> begin
(

let lifted = (

let uu____22925 = (closure_as_term cfg env1 ty)
in (reify_lift cfg t2 msrc mtgt uu____22925))
in ((log cfg (fun uu____22929 -> (

let uu____22930 = (FStar_Syntax_Print.term_to_string lifted)
in (FStar_Util.print1 "Reified lift to (1): %s\n" uu____22930))));
(

let uu____22931 = (FStar_List.tl stack)
in (norm cfg env1 uu____22931 lifted));
))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____22932)); FStar_Syntax_Syntax.pos = uu____22933; FStar_Syntax_Syntax.vars = uu____22934}, ((e, uu____22936))::[]) -> begin
(norm cfg env1 stack' e)
end
| FStar_Syntax_Syntax.Tm_app (uu____22965) when cfg.steps.primops -> begin
(

let uu____22980 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____22980) with
| (hd1, args) -> begin
(

let uu____23017 = (

let uu____23018 = (FStar_Syntax_Util.un_uinst hd1)
in uu____23018.FStar_Syntax_Syntax.n)
in (match (uu____23017) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____23022 = (find_prim_step cfg fv)
in (match (uu____23022) with
| FStar_Pervasives_Native.Some ({name = uu____23025; arity = uu____23026; auto_reflect = FStar_Pervasives_Native.Some (n1); strong_reduction_ok = uu____23028; requires_binder_substitution = uu____23029; interpretation = uu____23030}) when (Prims.op_Equality (FStar_List.length args) n1) -> begin
(norm cfg env1 stack' t1)
end
| uu____23045 -> begin
(fallback " (3)" ())
end))
end
| uu____23048 -> begin
(fallback " (4)" ())
end))
end))
end
| uu____23049 -> begin
(fallback " (2)" ())
end))))
end
| (App (env1, head1, aq, r))::stack1 -> begin
(

let t2 = (FStar_Syntax_Syntax.extend_app head1 ((t1), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack1 t2))
end
| (Match (env', branches, cfg1, r))::stack1 -> begin
((log cfg1 (fun uu____23072 -> (

let uu____23073 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____23073))));
(

let scrutinee_env = env
in (

let env1 = env'
in (

let scrutinee = t1
in (

let norm_and_rebuild_match = (fun uu____23082 -> ((log cfg1 (fun uu____23087 -> (

let uu____23088 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____23089 = (

let uu____23090 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____23117 -> (match (uu____23117) with
| (p, uu____23127, uu____23128) -> begin
(FStar_Syntax_Print.pat_to_string p)
end))))
in (FStar_All.pipe_right uu____23090 (FStar_String.concat "\n\t")))
in (FStar_Util.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu____23088 uu____23089)))));
(

let whnf = (cfg1.steps.weak || cfg1.steps.hnf)
in (

let cfg_exclude_zeta = (

let new_delta = (FStar_All.pipe_right cfg1.delta_level (FStar_List.filter (fun uu___93_23145 -> (match (uu___93_23145) with
| FStar_TypeChecker_Env.Inlining -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| uu____23146 -> begin
false
end))))
in (

let steps = (

let uu___185_23148 = cfg1.steps
in {beta = uu___185_23148.beta; iota = uu___185_23148.iota; zeta = false; weak = uu___185_23148.weak; hnf = uu___185_23148.hnf; primops = uu___185_23148.primops; do_not_unfold_pure_lets = uu___185_23148.do_not_unfold_pure_lets; unfold_until = FStar_Pervasives_Native.None; unfold_only = FStar_Pervasives_Native.None; unfold_fully = uu___185_23148.unfold_fully; unfold_attr = FStar_Pervasives_Native.None; unfold_tac = false; pure_subterms_within_computations = uu___185_23148.pure_subterms_within_computations; simplify = uu___185_23148.simplify; erase_universes = uu___185_23148.erase_universes; allow_unbound_universes = uu___185_23148.allow_unbound_universes; reify_ = uu___185_23148.reify_; compress_uvars = uu___185_23148.compress_uvars; no_full_norm = uu___185_23148.no_full_norm; check_no_uvars = uu___185_23148.check_no_uvars; unmeta = uu___185_23148.unmeta; unascribe = uu___185_23148.unascribe; in_full_norm_request = uu___185_23148.in_full_norm_request; weakly_reduce_scrutinee = uu___185_23148.weakly_reduce_scrutinee})
in (

let uu___186_23153 = cfg1
in {steps = steps; tcenv = uu___186_23153.tcenv; debug = uu___186_23153.debug; delta_level = new_delta; primitive_steps = uu___186_23153.primitive_steps; strong = true; memoize_lazy = uu___186_23153.memoize_lazy; normalize_pure_lets = uu___186_23153.normalize_pure_lets})))
in (

let norm_or_whnf = (fun env2 t2 -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_zeta env2 t2)
end
| uu____23165 -> begin
(norm cfg_exclude_zeta env2 [] t2)
end))
in (

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____23225) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____23254 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____23338 uu____23339 -> (match (((uu____23338), (uu____23339))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____23478 = (norm_pat env3 p1)
in (match (uu____23478) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____23254) with
| (pats1, env3) -> begin
(((

let uu___187_23640 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___187_23640.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___188_23659 = x
in (

let uu____23660 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___188_23659.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___188_23659.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____23660}))
in (((

let uu___189_23674 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___189_23674.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___190_23685 = x
in (

let uu____23686 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___190_23685.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___190_23685.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____23686}))
in (((

let uu___191_23700 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___191_23700.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t2) -> begin
(

let x1 = (

let uu___192_23716 = x
in (

let uu____23717 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___192_23716.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___192_23716.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____23717}))
in (

let t3 = (norm_or_whnf env2 t2)
in (((

let uu___193_23732 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t3))); FStar_Syntax_Syntax.p = uu___193_23732.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let branches1 = (match (env1) with
| [] when whnf -> begin
branches
end
| uu____23744 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch1 -> (

let uu____23758 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____23758) with
| (p, wopt, e) -> begin
(

let uu____23778 = (norm_pat env1 p)
in (match (uu____23778) with
| (p1, env2) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____23827 = (norm_or_whnf env2 w)
in FStar_Pervasives_Native.Some (uu____23827))
end)
in (

let e1 = (norm_or_whnf env2 e)
in (FStar_Syntax_Util.branch ((p1), (wopt1), (e1)))))
end))
end)))))
end)
in (

let scrutinee1 = (

let uu____23838 = ((((cfg1.steps.iota && (not (cfg1.steps.weak))) && (not (cfg1.steps.compress_uvars))) && cfg1.steps.weakly_reduce_scrutinee) && (maybe_weakly_reduced scrutinee))
in (match (uu____23838) with
| true -> begin
(norm (

let uu___194_23841 = cfg1
in {steps = (

let uu___195_23844 = cfg1.steps
in {beta = uu___195_23844.beta; iota = uu___195_23844.iota; zeta = uu___195_23844.zeta; weak = uu___195_23844.weak; hnf = uu___195_23844.hnf; primops = uu___195_23844.primops; do_not_unfold_pure_lets = uu___195_23844.do_not_unfold_pure_lets; unfold_until = uu___195_23844.unfold_until; unfold_only = uu___195_23844.unfold_only; unfold_fully = uu___195_23844.unfold_fully; unfold_attr = uu___195_23844.unfold_attr; unfold_tac = uu___195_23844.unfold_tac; pure_subterms_within_computations = uu___195_23844.pure_subterms_within_computations; simplify = uu___195_23844.simplify; erase_universes = uu___195_23844.erase_universes; allow_unbound_universes = uu___195_23844.allow_unbound_universes; reify_ = uu___195_23844.reify_; compress_uvars = uu___195_23844.compress_uvars; no_full_norm = uu___195_23844.no_full_norm; check_no_uvars = uu___195_23844.check_no_uvars; unmeta = uu___195_23844.unmeta; unascribe = uu___195_23844.unascribe; in_full_norm_request = uu___195_23844.in_full_norm_request; weakly_reduce_scrutinee = false}); tcenv = uu___194_23841.tcenv; debug = uu___194_23841.debug; delta_level = uu___194_23841.delta_level; primitive_steps = uu___194_23841.primitive_steps; strong = uu___194_23841.strong; memoize_lazy = uu___194_23841.memoize_lazy; normalize_pure_lets = uu___194_23841.normalize_pure_lets}) scrutinee_env [] scrutinee)
end
| uu____23845 -> begin
scrutinee
end))
in (

let uu____23846 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee1), (branches1)))) r)
in (rebuild cfg1 env1 stack1 uu____23846))))))));
))
in (

let rec is_cons = (fun head1 -> (

let uu____23871 = (

let uu____23872 = (FStar_Syntax_Subst.compress head1)
in uu____23872.FStar_Syntax_Syntax.n)
in (match (uu____23871) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____23876) -> begin
(is_cons h)
end
| FStar_Syntax_Syntax.Tm_constant (uu____23881) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____23882; FStar_Syntax_Syntax.fv_delta = uu____23883; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____23884; FStar_Syntax_Syntax.fv_delta = uu____23885; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____23886))}) -> begin
true
end
| uu____23893 -> begin
false
end)))
in (

let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| FStar_Pervasives_Native.None -> begin
b
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let then_branch = b
in (

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (rest)))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (

let rec matches_pat = (fun scrutinee_orig p -> (

let scrutinee1 = (FStar_Syntax_Util.unmeta scrutinee_orig)
in (

let uu____24056 = (FStar_Syntax_Util.head_and_args scrutinee1)
in (match (uu____24056) with
| (head1, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____24143) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (FStar_Const.eq_const s s') -> begin
FStar_Util.Inl ([])
end
| uu____24182 -> begin
(

let uu____24183 = (

let uu____24184 = (is_cons head1)
in (not (uu____24184)))
in FStar_Util.Inr (uu____24183))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____24209 = (

let uu____24210 = (FStar_Syntax_Util.un_uinst head1)
in uu____24210.FStar_Syntax_Syntax.n)
in (match (uu____24209) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____24228 -> begin
(

let uu____24229 = (

let uu____24230 = (is_cons head1)
in (not (uu____24230)))
in FStar_Util.Inr (uu____24229))
end))
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t2, uu____24307))::rest_a, ((p1, uu____24310))::rest_p) -> begin
(

let uu____24354 = (matches_pat t2 p1)
in (match (uu____24354) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____24403 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee1 p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p1, wopt, b))::rest -> begin
(

let uu____24521 = (matches_pat scrutinee1 p1)
in (match (uu____24521) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee1 rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((log cfg1 (fun uu____24561 -> (

let uu____24562 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____24563 = (

let uu____24564 = (FStar_List.map (fun uu____24574 -> (match (uu____24574) with
| (uu____24579, t2) -> begin
(FStar_Syntax_Print.term_to_string t2)
end)) s)
in (FStar_All.pipe_right uu____24564 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____24562 uu____24563)))));
(

let env0 = env1
in (

let env2 = (FStar_List.fold_left (fun env2 uu____24611 -> (match (uu____24611) with
| (bv, t2) -> begin
(

let uu____24634 = (

let uu____24641 = (

let uu____24644 = (FStar_Syntax_Syntax.mk_binder bv)
in FStar_Pervasives_Native.Some (uu____24644))
in (

let uu____24645 = (

let uu____24646 = (

let uu____24677 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (t2)))))
in (([]), (t2), (uu____24677), (false)))
in Clos (uu____24646))
in ((uu____24641), (uu____24645))))
in (uu____24634)::env2)
end)) env1 s)
in (

let uu____24790 = (guard_when_clause wopt b rest)
in (norm cfg1 env2 stack1 uu____24790))));
)
end))
end))
in (match (cfg1.steps.iota) with
| true -> begin
(matches scrutinee branches)
end
| uu____24791 -> begin
(norm_and_rebuild_match ())
end)))))))));
)
end));
))


let plugins : ((primitive_step  ->  unit) * (unit  ->  primitive_step Prims.list)) = (

let plugins = (FStar_Util.mk_ref [])
in (

let register = (fun p -> (

let uu____24817 = (

let uu____24820 = (FStar_ST.op_Bang plugins)
in (p)::uu____24820)
in (FStar_ST.op_Colon_Equals plugins uu____24817)))
in (

let retrieve = (fun uu____24928 -> (FStar_ST.op_Bang plugins))
in ((register), (retrieve)))))


let register_plugin : primitive_step  ->  unit = (fun p -> (FStar_Pervasives_Native.fst plugins p))


let retrieve_plugins : unit  ->  primitive_step Prims.list = (fun uu____25005 -> (FStar_Pervasives_Native.snd plugins ()))


let config' : primitive_step Prims.list  ->  step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun psteps s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___94_25046 -> (match (uu___94_25046) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| UnfoldTac -> begin
(FStar_TypeChecker_Env.UnfoldTac)::[]
end
| uu____25050 -> begin
[]
end))))
in (

let d1 = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| uu____25056 -> begin
d
end)
in (

let uu____25059 = (to_fsteps s)
in (

let uu____25060 = (

let uu____25061 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("Norm")))
in (

let uu____25062 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("Primops")))
in (

let uu____25063 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("380")))
in (

let uu____25064 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("NormDelayed")))
in (

let uu____25065 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("print_normalized_terms")))
in {gen = uu____25061; primop = uu____25062; b380 = uu____25063; norm_delayed = uu____25064; print_normalized = uu____25065})))))
in (

let uu____25066 = (

let uu____25069 = (

let uu____25072 = (retrieve_plugins ())
in (FStar_List.append uu____25072 psteps))
in (add_steps built_in_primitive_steps uu____25069))
in (

let uu____25075 = ((FStar_Options.normalize_pure_terms_for_extraction ()) || (

let uu____25077 = (FStar_All.pipe_right s (FStar_List.contains PureSubtermsWithinComputations))
in (not (uu____25077))))
in {steps = uu____25059; tcenv = e; debug = uu____25060; delta_level = d1; primitive_steps = uu____25066; strong = false; memoize_lazy = true; normalize_pure_lets = uu____25075})))))))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (config' [] s e))


let normalize_with_primitive_steps : primitive_step Prims.list  ->  step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun ps s e t -> (

let c = (config' ps s e)
in (norm c [] [] t)))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (normalize_with_primitive_steps [] s e t))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (

let uu____25159 = (config s e)
in (norm_comp uu____25159 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____25176 = (config [] env)
in (norm_universe uu____25176 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (

let cfg = (config ((UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::(EraseUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____25200 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____25200)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____25207) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___196_25226 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.pos = uu___196_25226.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___196_25226.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____25233 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____25233) with
| true -> begin
(

let ct1 = (

let uu____25235 = (downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)
in (match (uu____25235) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let flags1 = (

let uu____25242 = (FStar_Ident.lid_equals pure_eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____25242) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::ct.FStar_Syntax_Syntax.flags
end
| uu____25245 -> begin
ct.FStar_Syntax_Syntax.flags
end))
in (

let uu___197_25246 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___197_25246.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___197_25246.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___197_25246.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags1}))
end
| FStar_Pervasives_Native.None -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c)
in (

let uu___198_25248 = ct1
in {FStar_Syntax_Syntax.comp_univs = uu___198_25248.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___198_25248.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___198_25248.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___198_25248.FStar_Syntax_Syntax.flags}))
end))
in (

let uu___199_25249 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___199_25249.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___199_25249.FStar_Syntax_Syntax.vars}))
end
| uu____25250 -> begin
c
end)))
end
| uu____25251 -> begin
c
end))))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____25269 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____25269)))
in (

let uu____25276 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____25276) with
| true -> begin
(

let uu____25277 = (downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____25277) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(FStar_Syntax_Syntax.mk_lcomp pure_eff lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____25283 -> (

let uu____25284 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (ghost_to_pure env uu____25284))))
end
| FStar_Pervasives_Native.None -> begin
lc
end))
end
| uu____25285 -> begin
lc
end)))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let t1 = (FStar_All.try_with (fun uu___201_25298 -> (match (()) with
| () -> begin
(normalize ((AllowUnboundUniverses)::[]) env t)
end)) (fun uu___200_25302 -> (match (uu___200_25302) with
| e -> begin
((

let uu____25305 = (

let uu____25310 = (

let uu____25311 = (FStar_Util.message_of_exn e)
in (FStar_Util.format1 "Normalization failed with error %s\n" uu____25311))
in ((FStar_Errors.Warning_NormalizationFailure), (uu____25310)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25305));
t;
)
end)))
in (FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let c1 = (FStar_All.try_with (fun uu___203_25325 -> (match (()) with
| () -> begin
(

let uu____25326 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp uu____25326 [] c))
end)) (fun uu___202_25336 -> (match (uu___202_25336) with
| e -> begin
((

let uu____25339 = (

let uu____25344 = (

let uu____25345 = (FStar_Util.message_of_exn e)
in (FStar_Util.format1 "Normalization failed with error %s\n" uu____25345))
in ((FStar_Errors.Warning_NormalizationFailure), (uu____25344)))
in (FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____25339));
c;
)
end)))
in (FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1)))


let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (

let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (

let rec aux = (fun t1 -> (

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let t01 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t01.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(

let uu____25390 = (

let uu____25391 = (

let uu____25398 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (uu____25398)))
in FStar_Syntax_Syntax.Tm_refine (uu____25391))
in (mk uu____25390 t01.FStar_Syntax_Syntax.pos))
end
| uu____25403 -> begin
t2
end))
end
| uu____25404 -> begin
t2
end)))
in (aux t))))


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((Primops)::(Weak)::(HNF)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Beta)::[]) env t))


let reduce_or_remove_uvar_solutions : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun remove env t -> (normalize (FStar_List.append (match (remove) with
| true -> begin
(CheckNoUvars)::[]
end
| uu____25432 -> begin
[]
end) ((Beta)::(DoNotUnfoldPureLets)::(CompressUvars)::(Exclude (Zeta))::(Exclude (Iota))::(NoFullNorm)::[])) env t))


let reduce_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions false env t))


let remove_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions true env t))


let eta_expand_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e t_e -> (

let uu____25468 = (FStar_Syntax_Util.arrow_formals_comp t_e)
in (match (uu____25468) with
| (formals, c) -> begin
(match (formals) with
| [] -> begin
e
end
| uu____25497 -> begin
(

let uu____25504 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____25504) with
| (actuals, uu____25514, uu____25515) -> begin
(match ((Prims.op_Equality (FStar_List.length actuals) (FStar_List.length formals))) with
| true -> begin
e
end
| uu____25528 -> begin
(

let uu____25529 = (FStar_All.pipe_right formals FStar_Syntax_Util.args_of_binders)
in (match (uu____25529) with
| (binders, args) -> begin
(

let uu____25546 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Util.abs binders uu____25546 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c)))))
end))
end)
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(eta_expand_with_type env t x.FStar_Syntax_Syntax.sort)
end
| uu____25560 -> begin
(

let uu____25561 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____25561) with
| (head1, args) -> begin
(

let uu____25598 = (

let uu____25599 = (FStar_Syntax_Subst.compress head1)
in uu____25599.FStar_Syntax_Syntax.n)
in (match (uu____25598) with
| FStar_Syntax_Syntax.Tm_uvar (u) -> begin
(

let uu____25603 = (FStar_Syntax_Util.arrow_formals u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (match (uu____25603) with
| (formals, tres) -> begin
(match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
t
end
| uu____25644 -> begin
(

let uu____25645 = (env.FStar_TypeChecker_Env.type_of (

let uu___204_25653 = env
in {FStar_TypeChecker_Env.solver = uu___204_25653.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___204_25653.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___204_25653.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___204_25653.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___204_25653.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___204_25653.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___204_25653.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___204_25653.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___204_25653.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___204_25653.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___204_25653.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___204_25653.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___204_25653.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___204_25653.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___204_25653.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___204_25653.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___204_25653.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___204_25653.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___204_25653.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___204_25653.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___204_25653.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___204_25653.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___204_25653.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___204_25653.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___204_25653.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___204_25653.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___204_25653.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___204_25653.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___204_25653.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___204_25653.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___204_25653.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___204_25653.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___204_25653.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___204_25653.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___204_25653.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____25645) with
| (uu____25654, ty, uu____25656) -> begin
(eta_expand_with_type env t ty)
end))
end)
end))
end
| uu____25657 -> begin
(

let uu____25658 = (env.FStar_TypeChecker_Env.type_of (

let uu___205_25666 = env
in {FStar_TypeChecker_Env.solver = uu___205_25666.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___205_25666.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___205_25666.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___205_25666.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___205_25666.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___205_25666.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___205_25666.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___205_25666.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___205_25666.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___205_25666.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___205_25666.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___205_25666.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___205_25666.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___205_25666.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___205_25666.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___205_25666.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___205_25666.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___205_25666.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___205_25666.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___205_25666.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___205_25666.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___205_25666.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___205_25666.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___205_25666.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___205_25666.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___205_25666.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___205_25666.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___205_25666.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___205_25666.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___205_25666.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___205_25666.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___205_25666.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___205_25666.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___205_25666.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___205_25666.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____25658) with
| (uu____25667, ty, uu____25669) -> begin
(eta_expand_with_type env t ty)
end))
end))
end))
end))


let rec elim_delayed_subst_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let elim_bv = (fun x -> (

let uu___206_25742 = x
in (

let uu____25743 = (elim_delayed_subst_term x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___206_25742.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___206_25742.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____25743})))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____25746) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____25771) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_name (uu____25772) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (uu____25773) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uinst (uu____25774) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____25781) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____25782) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_lazy (uu____25783) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) -> begin
(

let elim_rc = (fun rc -> (

let uu___207_25813 = rc
in (

let uu____25814 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ elim_delayed_subst_term)
in (

let uu____25823 = (elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags)
in {FStar_Syntax_Syntax.residual_effect = uu___207_25813.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____25814; FStar_Syntax_Syntax.residual_flags = uu____25823}))))
in (

let uu____25826 = (

let uu____25827 = (

let uu____25844 = (elim_delayed_subst_binders bs)
in (

let uu____25851 = (elim_delayed_subst_term t2)
in (

let uu____25854 = (FStar_Util.map_opt rc_opt elim_rc)
in ((uu____25844), (uu____25851), (uu____25854)))))
in FStar_Syntax_Syntax.Tm_abs (uu____25827))
in (mk1 uu____25826)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____25885 = (

let uu____25886 = (

let uu____25899 = (elim_delayed_subst_binders bs)
in (

let uu____25906 = (elim_delayed_subst_comp c)
in ((uu____25899), (uu____25906))))
in FStar_Syntax_Syntax.Tm_arrow (uu____25886))
in (mk1 uu____25885))
end
| FStar_Syntax_Syntax.Tm_refine (bv, phi) -> begin
(

let uu____25923 = (

let uu____25924 = (

let uu____25931 = (elim_bv bv)
in (

let uu____25932 = (elim_delayed_subst_term phi)
in ((uu____25931), (uu____25932))))
in FStar_Syntax_Syntax.Tm_refine (uu____25924))
in (mk1 uu____25923))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____25959 = (

let uu____25960 = (

let uu____25975 = (elim_delayed_subst_term t2)
in (

let uu____25978 = (elim_delayed_subst_args args)
in ((uu____25975), (uu____25978))))
in FStar_Syntax_Syntax.Tm_app (uu____25960))
in (mk1 uu____25959))
end
| FStar_Syntax_Syntax.Tm_match (t2, branches) -> begin
(

let rec elim_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___208_26046 = p
in (

let uu____26047 = (

let uu____26048 = (elim_bv x)
in FStar_Syntax_Syntax.Pat_var (uu____26048))
in {FStar_Syntax_Syntax.v = uu____26047; FStar_Syntax_Syntax.p = uu___208_26046.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___209_26050 = p
in (

let uu____26051 = (

let uu____26052 = (elim_bv x)
in FStar_Syntax_Syntax.Pat_wild (uu____26052))
in {FStar_Syntax_Syntax.v = uu____26051; FStar_Syntax_Syntax.p = uu___209_26050.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let uu___210_26059 = p
in (

let uu____26060 = (

let uu____26061 = (

let uu____26068 = (elim_bv x)
in (

let uu____26069 = (elim_delayed_subst_term t0)
in ((uu____26068), (uu____26069))))
in FStar_Syntax_Syntax.Pat_dot_term (uu____26061))
in {FStar_Syntax_Syntax.v = uu____26060; FStar_Syntax_Syntax.p = uu___210_26059.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu___211_26092 = p
in (

let uu____26093 = (

let uu____26094 = (

let uu____26107 = (FStar_List.map (fun uu____26130 -> (match (uu____26130) with
| (x, b) -> begin
(

let uu____26143 = (elim_pat x)
in ((uu____26143), (b)))
end)) pats)
in ((fv), (uu____26107)))
in FStar_Syntax_Syntax.Pat_cons (uu____26094))
in {FStar_Syntax_Syntax.v = uu____26093; FStar_Syntax_Syntax.p = uu___211_26092.FStar_Syntax_Syntax.p}))
end
| uu____26156 -> begin
p
end))
in (

let elim_branch = (fun uu____26180 -> (match (uu____26180) with
| (pat, wopt, t3) -> begin
(

let uu____26206 = (elim_pat pat)
in (

let uu____26209 = (FStar_Util.map_opt wopt elim_delayed_subst_term)
in (

let uu____26212 = (elim_delayed_subst_term t3)
in ((uu____26206), (uu____26209), (uu____26212)))))
end))
in (

let uu____26217 = (

let uu____26218 = (

let uu____26241 = (elim_delayed_subst_term t2)
in (

let uu____26244 = (FStar_List.map elim_branch branches)
in ((uu____26241), (uu____26244))))
in FStar_Syntax_Syntax.Tm_match (uu____26218))
in (mk1 uu____26217))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) -> begin
(

let elim_ascription = (fun uu____26371 -> (match (uu____26371) with
| (tc, topt) -> begin
(

let uu____26406 = (match (tc) with
| FStar_Util.Inl (t3) -> begin
(

let uu____26416 = (elim_delayed_subst_term t3)
in FStar_Util.Inl (uu____26416))
end
| FStar_Util.Inr (c) -> begin
(

let uu____26418 = (elim_delayed_subst_comp c)
in FStar_Util.Inr (uu____26418))
end)
in (

let uu____26419 = (FStar_Util.map_opt topt elim_delayed_subst_term)
in ((uu____26406), (uu____26419))))
end))
in (

let uu____26428 = (

let uu____26429 = (

let uu____26456 = (elim_delayed_subst_term t2)
in (

let uu____26459 = (elim_ascription a)
in ((uu____26456), (uu____26459), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____26429))
in (mk1 uu____26428)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t2) -> begin
(

let elim_lb = (fun lb -> (

let uu___212_26520 = lb
in (

let uu____26521 = (elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____26524 = (elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___212_26520.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___212_26520.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____26521; FStar_Syntax_Syntax.lbeff = uu___212_26520.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____26524; FStar_Syntax_Syntax.lbattrs = uu___212_26520.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___212_26520.FStar_Syntax_Syntax.lbpos}))))
in (

let uu____26527 = (

let uu____26528 = (

let uu____26541 = (

let uu____26548 = (FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs))
in (((FStar_Pervasives_Native.fst lbs)), (uu____26548)))
in (

let uu____26557 = (elim_delayed_subst_term t2)
in ((uu____26541), (uu____26557))))
in FStar_Syntax_Syntax.Tm_let (uu____26528))
in (mk1 uu____26527)))
end
| FStar_Syntax_Syntax.Tm_uvar (u) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uvar (u)))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi)
in (

let uu____26576 = (

let uu____26577 = (

let uu____26584 = (elim_delayed_subst_term tm)
in ((uu____26584), (qi1)))
in FStar_Syntax_Syntax.Tm_quoted (uu____26577))
in (mk1 uu____26576)))
end
| FStar_Syntax_Syntax.Tm_meta (t2, md) -> begin
(

let uu____26595 = (

let uu____26596 = (

let uu____26603 = (elim_delayed_subst_term t2)
in (

let uu____26606 = (elim_delayed_subst_meta md)
in ((uu____26603), (uu____26606))))
in FStar_Syntax_Syntax.Tm_meta (uu____26596))
in (mk1 uu____26595))
end)))))
and elim_delayed_subst_cflags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun flags1 -> (FStar_List.map (fun uu___95_26615 -> (match (uu___95_26615) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____26619 = (elim_delayed_subst_term t)
in FStar_Syntax_Syntax.DECREASES (uu____26619))
end
| f -> begin
f
end)) flags1))
and elim_delayed_subst_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun c -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____26642 = (

let uu____26643 = (

let uu____26652 = (elim_delayed_subst_term t)
in ((uu____26652), (uopt)))
in FStar_Syntax_Syntax.Total (uu____26643))
in (mk1 uu____26642))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____26669 = (

let uu____26670 = (

let uu____26679 = (elim_delayed_subst_term t)
in ((uu____26679), (uopt)))
in FStar_Syntax_Syntax.GTotal (uu____26670))
in (mk1 uu____26669))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___213_26688 = ct
in (

let uu____26689 = (elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____26692 = (elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____26701 = (elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu___213_26688.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___213_26688.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____26689; FStar_Syntax_Syntax.effect_args = uu____26692; FStar_Syntax_Syntax.flags = uu____26701}))))
in (mk1 (FStar_Syntax_Syntax.Comp (ct1))))
end)))
and elim_delayed_subst_meta : FStar_Syntax_Syntax.metadata  ->  FStar_Syntax_Syntax.metadata = (fun uu___96_26704 -> (match (uu___96_26704) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let uu____26716 = (FStar_List.map elim_delayed_subst_args args)
in FStar_Syntax_Syntax.Meta_pattern (uu____26716))
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____26749 = (

let uu____26756 = (elim_delayed_subst_term t)
in ((m), (uu____26756)))
in FStar_Syntax_Syntax.Meta_monadic (uu____26749))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) -> begin
(

let uu____26768 = (

let uu____26777 = (elim_delayed_subst_term t)
in ((m1), (m2), (uu____26777)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____26768))
end
| m -> begin
m
end))
and elim_delayed_subst_args : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun args -> (FStar_List.map (fun uu____26804 -> (match (uu____26804) with
| (t, q) -> begin
(

let uu____26815 = (elim_delayed_subst_term t)
in ((uu____26815), (q)))
end)) args))
and elim_delayed_subst_binders : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun bs -> (FStar_List.map (fun uu____26835 -> (match (uu____26835) with
| (x, q) -> begin
(

let uu____26846 = (

let uu___214_26847 = x
in (

let uu____26848 = (elim_delayed_subst_term x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___214_26847.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___214_26847.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____26848}))
in ((uu____26846), (q)))
end)) bs))


let elim_uvars_aux_tc : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.comp) FStar_Util.either  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either) = (fun env univ_names binders tc -> (

let t = (match (((binders), (tc))) with
| ([], FStar_Util.Inl (t)) -> begin
t
end
| ([], FStar_Util.Inr (c)) -> begin
(failwith "Impossible: empty bindes with a comp")
end
| (uu____26938, FStar_Util.Inr (c)) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
end
| (uu____26964, FStar_Util.Inl (t)) -> begin
(

let uu____26982 = (

let uu____26989 = (

let uu____26990 = (

let uu____27003 = (FStar_Syntax_Syntax.mk_Total t)
in ((binders), (uu____27003)))
in FStar_Syntax_Syntax.Tm_arrow (uu____26990))
in (FStar_Syntax_Syntax.mk uu____26989))
in (uu____26982 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end)
in (

let uu____27017 = (FStar_Syntax_Subst.open_univ_vars univ_names t)
in (match (uu____27017) with
| (univ_names1, t1) -> begin
(

let t2 = (remove_uvar_solutions env t1)
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars univ_names1 t2)
in (

let t4 = (elim_delayed_subst_term t3)
in (

let uu____27045 = (match (binders) with
| [] -> begin
(([]), (FStar_Util.Inl (t4)))
end
| uu____27100 -> begin
(

let uu____27101 = (

let uu____27110 = (

let uu____27111 = (FStar_Syntax_Subst.compress t4)
in uu____27111.FStar_Syntax_Syntax.n)
in ((uu____27110), (tc)))
in (match (uu____27101) with
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inr (uu____27136)) -> begin
((binders1), (FStar_Util.Inr (c)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inl (uu____27173)) -> begin
((binders1), (FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))))
end
| (uu____27212, FStar_Util.Inl (uu____27213)) -> begin
(([]), (FStar_Util.Inl (t4)))
end
| uu____27236 -> begin
(failwith "Impossible")
end))
end)
in (match (uu____27045) with
| (binders1, tc1) -> begin
((univ_names1), (binders1), (tc1))
end)))))
end))))


let elim_uvars_aux_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term) = (fun env univ_names binders t -> (

let uu____27349 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl (t)))
in (match (uu____27349) with
| (univ_names1, binders1, tc) -> begin
(

let uu____27407 = (FStar_Util.left tc)
in ((univ_names1), (binders1), (uu____27407)))
end)))


let elim_uvars_aux_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) = (fun env univ_names binders c -> (

let uu____27450 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr (c)))
in (match (uu____27450) with
| (univ_names1, binders1, tc) -> begin
(

let uu____27510 = (FStar_Util.right tc)
in ((univ_names1), (binders1), (uu____27510)))
end)))


let rec elim_uvars : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, lids, lids') -> begin
(

let uu____27547 = (elim_uvars_aux_t env univ_names binders typ)
in (match (uu____27547) with
| (univ_names1, binders1, typ1) -> begin
(

let uu___215_27575 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univ_names1), (binders1), (typ1), (lids), (lids'))); FStar_Syntax_Syntax.sigrng = uu___215_27575.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___215_27575.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___215_27575.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___215_27575.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uu___216_27590 = s
in (

let uu____27591 = (

let uu____27592 = (

let uu____27601 = (FStar_List.map (elim_uvars env) sigs)
in ((uu____27601), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____27592))
in {FStar_Syntax_Syntax.sigel = uu____27591; FStar_Syntax_Syntax.sigrng = uu___216_27590.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___216_27590.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___216_27590.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___216_27590.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univ_names, typ, lident, i, lids) -> begin
(

let uu____27618 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____27618) with
| (univ_names1, uu____27636, typ1) -> begin
(

let uu___217_27650 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univ_names1), (typ1), (lident), (i), (lids))); FStar_Syntax_Syntax.sigrng = uu___217_27650.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___217_27650.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___217_27650.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___217_27650.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) -> begin
(

let uu____27656 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____27656) with
| (univ_names1, uu____27674, typ1) -> begin
(

let uu___218_27688 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (univ_names1), (typ1))); FStar_Syntax_Syntax.sigrng = uu___218_27688.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___218_27688.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___218_27688.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___218_27688.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____27716 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____27716) with
| (opening, lbunivs) -> begin
(

let elim = (fun t -> (

let uu____27741 = (

let uu____27742 = (

let uu____27743 = (FStar_Syntax_Subst.subst opening t)
in (remove_uvar_solutions env uu____27743))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____27742))
in (elim_delayed_subst_term uu____27741)))
in (

let lbtyp = (elim lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (elim lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___219_27746 = lb
in {FStar_Syntax_Syntax.lbname = uu___219_27746.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___219_27746.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___219_27746.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___219_27746.FStar_Syntax_Syntax.lbpos}))))
end)))))
in (

let uu___220_27747 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((b), (lbs1))), (lids))); FStar_Syntax_Syntax.sigrng = uu___220_27747.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___220_27747.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___220_27747.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___220_27747.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(

let uu___221_27753 = s
in (

let uu____27754 = (

let uu____27755 = (remove_uvar_solutions env t)
in FStar_Syntax_Syntax.Sig_main (uu____27755))
in {FStar_Syntax_Syntax.sigel = uu____27754; FStar_Syntax_Syntax.sigrng = uu___221_27753.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___221_27753.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___221_27753.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___221_27753.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, t) -> begin
(

let uu____27759 = (elim_uvars_aux_t env us [] t)
in (match (uu____27759) with
| (us1, uu____27777, t1) -> begin
(

let uu___222_27791 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((l), (us1), (t1))); FStar_Syntax_Syntax.sigrng = uu___222_27791.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___222_27791.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___222_27791.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___222_27791.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____27792) -> begin
(failwith "Impossible: should have been desugared already")
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____27794 = (elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____27794) with
| (univs1, binders, signature) -> begin
(

let uu____27822 = (

let uu____27831 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____27831) with
| (univs_opening, univs2) -> begin
(

let uu____27858 = (FStar_Syntax_Subst.univ_var_closing univs2)
in ((univs_opening), (uu____27858)))
end))
in (match (uu____27822) with
| (univs_opening, univs_closing) -> begin
(

let uu____27875 = (

let binders1 = (FStar_Syntax_Subst.open_binders binders)
in (

let uu____27881 = (FStar_Syntax_Subst.opening_of_binders binders1)
in (

let uu____27882 = (FStar_Syntax_Subst.closing_of_binders binders1)
in ((uu____27881), (uu____27882)))))
in (match (uu____27875) with
| (b_opening, b_closing) -> begin
(

let n1 = (FStar_List.length univs1)
in (

let n_binders = (FStar_List.length binders)
in (

let elim_tscheme = (fun uu____27906 -> (match (uu____27906) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____27924 = (FStar_Syntax_Subst.open_univ_vars us t)
in (match (uu____27924) with
| (us1, t1) -> begin
(

let uu____27935 = (

let uu____27944 = (FStar_All.pipe_right b_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____27953 = (FStar_All.pipe_right b_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____27944), (uu____27953))))
in (match (uu____27935) with
| (b_opening1, b_closing1) -> begin
(

let uu____27980 = (

let uu____27989 = (FStar_All.pipe_right univs_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____28000 = (FStar_All.pipe_right univs_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____27989), (uu____28000))))
in (match (uu____27980) with
| (univs_opening1, univs_closing1) -> begin
(

let t2 = (

let uu____28030 = (FStar_Syntax_Subst.subst b_opening1 t1)
in (FStar_Syntax_Subst.subst univs_opening1 uu____28030))
in (

let uu____28031 = (elim_uvars_aux_t env [] [] t2)
in (match (uu____28031) with
| (uu____28052, uu____28053, t3) -> begin
(

let t4 = (

let uu____28068 = (

let uu____28069 = (FStar_Syntax_Subst.close_univ_vars us1 t3)
in (FStar_Syntax_Subst.subst b_closing1 uu____28069))
in (FStar_Syntax_Subst.subst univs_closing1 uu____28068))
in ((us1), (t4)))
end)))
end))
end))
end)))
end))
in (

let elim_term = (fun t -> (

let uu____28076 = (elim_uvars_aux_t env univs1 binders t)
in (match (uu____28076) with
| (uu____28089, uu____28090, t1) -> begin
t1
end)))
in (

let elim_action = (fun a -> (

let action_typ_templ = (

let body = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((a.FStar_Syntax_Syntax.action_defn), (((FStar_Util.Inl (a.FStar_Syntax_Syntax.action_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (match (a.FStar_Syntax_Syntax.action_params) with
| [] -> begin
body
end
| uu____28160 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((a.FStar_Syntax_Syntax.action_params), (body), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
end))
in (

let destruct_action_body = (fun body -> (

let uu____28185 = (

let uu____28186 = (FStar_Syntax_Subst.compress body)
in uu____28186.FStar_Syntax_Syntax.n)
in (match (uu____28185) with
| FStar_Syntax_Syntax.Tm_ascribed (defn, (FStar_Util.Inl (typ), FStar_Pervasives_Native.None), FStar_Pervasives_Native.None) -> begin
((defn), (typ))
end
| uu____28245 -> begin
(failwith "Impossible")
end)))
in (

let destruct_action_typ_templ = (fun t -> (

let uu____28276 = (

let uu____28277 = (FStar_Syntax_Subst.compress t)
in uu____28277.FStar_Syntax_Syntax.n)
in (match (uu____28276) with
| FStar_Syntax_Syntax.Tm_abs (pars, body, uu____28298) -> begin
(

let uu____28319 = (destruct_action_body body)
in (match (uu____28319) with
| (defn, typ) -> begin
((pars), (defn), (typ))
end))
end
| uu____28364 -> begin
(

let uu____28365 = (destruct_action_body t)
in (match (uu____28365) with
| (defn, typ) -> begin
(([]), (defn), (typ))
end))
end)))
in (

let uu____28414 = (elim_tscheme ((a.FStar_Syntax_Syntax.action_univs), (action_typ_templ)))
in (match (uu____28414) with
| (action_univs, t) -> begin
(

let uu____28423 = (destruct_action_typ_templ t)
in (match (uu____28423) with
| (action_params, action_defn, action_typ) -> begin
(

let a' = (

let uu___223_28464 = a
in {FStar_Syntax_Syntax.action_name = uu___223_28464.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___223_28464.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action_univs; FStar_Syntax_Syntax.action_params = action_params; FStar_Syntax_Syntax.action_defn = action_defn; FStar_Syntax_Syntax.action_typ = action_typ})
in a')
end))
end))))))
in (

let ed1 = (

let uu___224_28466 = ed
in (

let uu____28467 = (elim_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____28468 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____28469 = (elim_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____28470 = (elim_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____28471 = (elim_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____28472 = (elim_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____28473 = (elim_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____28474 = (elim_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____28475 = (elim_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____28476 = (elim_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____28477 = (elim_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____28478 = (elim_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____28479 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____28480 = (FStar_List.map elim_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___224_28466.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___224_28466.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu____28467; FStar_Syntax_Syntax.bind_wp = uu____28468; FStar_Syntax_Syntax.if_then_else = uu____28469; FStar_Syntax_Syntax.ite_wp = uu____28470; FStar_Syntax_Syntax.stronger = uu____28471; FStar_Syntax_Syntax.close_wp = uu____28472; FStar_Syntax_Syntax.assert_p = uu____28473; FStar_Syntax_Syntax.assume_p = uu____28474; FStar_Syntax_Syntax.null_wp = uu____28475; FStar_Syntax_Syntax.trivial = uu____28476; FStar_Syntax_Syntax.repr = uu____28477; FStar_Syntax_Syntax.return_repr = uu____28478; FStar_Syntax_Syntax.bind_repr = uu____28479; FStar_Syntax_Syntax.actions = uu____28480; FStar_Syntax_Syntax.eff_attrs = uu___224_28466.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in (

let uu___225_28483 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ed1); FStar_Syntax_Syntax.sigrng = uu___225_28483.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___225_28483.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___225_28483.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___225_28483.FStar_Syntax_Syntax.sigattrs})))))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub_eff) -> begin
(

let elim_tscheme_opt = (fun uu___97_28502 -> (match (uu___97_28502) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (us, t) -> begin
(

let uu____28529 = (elim_uvars_aux_t env us [] t)
in (match (uu____28529) with
| (us1, uu____28553, t1) -> begin
FStar_Pervasives_Native.Some (((us1), (t1)))
end))
end))
in (

let sub_eff1 = (

let uu___226_28572 = sub_eff
in (

let uu____28573 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp)
in (

let uu____28576 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift)
in {FStar_Syntax_Syntax.source = uu___226_28572.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___226_28572.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = uu____28573; FStar_Syntax_Syntax.lift = uu____28576})))
in (

let uu___227_28579 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub_eff1); FStar_Syntax_Syntax.sigrng = uu___227_28579.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___227_28579.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___227_28579.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___227_28579.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univ_names, binders, comp, flags1) -> begin
(

let uu____28589 = (elim_uvars_aux_c env univ_names binders comp)
in (match (uu____28589) with
| (univ_names1, binders1, comp1) -> begin
(

let uu___228_28623 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (univ_names1), (binders1), (comp1), (flags1))); FStar_Syntax_Syntax.sigrng = uu___228_28623.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___228_28623.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___228_28623.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___228_28623.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_pragma (uu____28626) -> begin
s
end
| FStar_Syntax_Syntax.Sig_splice (uu____28627) -> begin
s
end))


let erase_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((EraseUniverses)::(AllowUnboundUniverses)::[]) env t))




