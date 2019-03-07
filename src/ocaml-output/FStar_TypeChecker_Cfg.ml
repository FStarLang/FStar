open Prims
type fsteps =
  {
  beta: Prims.bool ;
  iota: Prims.bool ;
  zeta: Prims.bool ;
  weak: Prims.bool ;
  hnf: Prims.bool ;
  primops: Prims.bool ;
  do_not_unfold_pure_lets: Prims.bool ;
  unfold_until:
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option ;
  unfold_only: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_fully: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_attr: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
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
  unascribe: Prims.bool ;
  in_full_norm_request: Prims.bool ;
  weakly_reduce_scrutinee: Prims.bool ;
  nbe_step: Prims.bool ;
  for_extraction: Prims.bool }
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> beta
  
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> iota1
  
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> zeta1
  
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> weak1
  
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> hnf1
  
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> primops1
  
let (__proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        do_not_unfold_pure_lets
  
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_until
  
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_only
  
let (__proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_fully
  
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_attr
  
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_tac
  
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        pure_subterms_within_computations
  
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> simplify1
  
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        erase_universes
  
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        allow_unbound_universes
  
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> reify_1
  
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        compress_uvars
  
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> no_full_norm
  
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        check_no_uvars
  
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unmeta1
  
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unascribe1
  
let (__proj__Mkfsteps__item__in_full_norm_request : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        in_full_norm_request
  
let (__proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        weakly_reduce_scrutinee
  
let (__proj__Mkfsteps__item__nbe_step : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> nbe_step
  
let (__proj__Mkfsteps__item__for_extraction : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        for_extraction
  
let (steps_to_string : fsteps -> Prims.string) =
  fun f  ->
    let format_opt f1 o =
      match o with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____60238 =
            let uu____60240 = f1 x  in FStar_String.op_Hat uu____60240 ")"
             in
          FStar_String.op_Hat "Some (" uu____60238
       in
    let b = FStar_Util.string_of_bool  in
    let uu____60251 =
      let uu____60255 = FStar_All.pipe_right f.beta b  in
      let uu____60259 =
        let uu____60263 = FStar_All.pipe_right f.iota b  in
        let uu____60267 =
          let uu____60271 = FStar_All.pipe_right f.zeta b  in
          let uu____60275 =
            let uu____60279 = FStar_All.pipe_right f.weak b  in
            let uu____60283 =
              let uu____60287 = FStar_All.pipe_right f.hnf b  in
              let uu____60291 =
                let uu____60295 = FStar_All.pipe_right f.primops b  in
                let uu____60299 =
                  let uu____60303 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____60307 =
                    let uu____60311 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____60316 =
                      let uu____60320 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____60334 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____60334
                                  (FStar_String.concat ", ")))
                         in
                      let uu____60344 =
                        let uu____60348 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____60362 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____60362
                                    (FStar_String.concat ", ")))
                           in
                        let uu____60372 =
                          let uu____60376 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____60390 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____60390
                                      (FStar_String.concat ", ")))
                             in
                          let uu____60400 =
                            let uu____60404 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____60408 =
                              let uu____60412 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____60416 =
                                let uu____60420 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____60424 =
                                  let uu____60428 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____60432 =
                                    let uu____60436 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____60440 =
                                      let uu____60444 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____60448 =
                                        let uu____60452 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____60456 =
                                          let uu____60460 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____60464 =
                                            let uu____60468 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____60472 =
                                              let uu____60476 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____60480 =
                                                let uu____60484 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____60488 =
                                                  let uu____60492 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____60496 =
                                                    let uu____60500 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____60500]  in
                                                  uu____60492 :: uu____60496
                                                   in
                                                uu____60484 :: uu____60488
                                                 in
                                              uu____60476 :: uu____60480  in
                                            uu____60468 :: uu____60472  in
                                          uu____60460 :: uu____60464  in
                                        uu____60452 :: uu____60456  in
                                      uu____60444 :: uu____60448  in
                                    uu____60436 :: uu____60440  in
                                  uu____60428 :: uu____60432  in
                                uu____60420 :: uu____60424  in
                              uu____60412 :: uu____60416  in
                            uu____60404 :: uu____60408  in
                          uu____60376 :: uu____60400  in
                        uu____60348 :: uu____60372  in
                      uu____60320 :: uu____60344  in
                    uu____60311 :: uu____60316  in
                  uu____60303 :: uu____60307  in
                uu____60295 :: uu____60299  in
              uu____60287 :: uu____60291  in
            uu____60279 :: uu____60283  in
          uu____60271 :: uu____60275  in
        uu____60263 :: uu____60267  in
      uu____60255 :: uu____60259  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____60251
  
let (default_steps : fsteps) =
  {
    beta = true;
    iota = true;
    zeta = true;
    weak = false;
    hnf = false;
    primops = false;
    do_not_unfold_pure_lets = false;
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
    unascribe = false;
    in_full_norm_request = false;
    weakly_reduce_scrutinee = true;
    nbe_step = false;
    for_extraction = false
  } 
let (fstep_add_one : FStar_TypeChecker_Env.step -> fsteps -> fsteps) =
  fun s  ->
    fun fs  ->
      match s with
      | FStar_TypeChecker_Env.Beta  ->
          let uu___625_60570 = fs  in
          {
            beta = true;
            iota = (uu___625_60570.iota);
            zeta = (uu___625_60570.zeta);
            weak = (uu___625_60570.weak);
            hnf = (uu___625_60570.hnf);
            primops = (uu___625_60570.primops);
            do_not_unfold_pure_lets =
              (uu___625_60570.do_not_unfold_pure_lets);
            unfold_until = (uu___625_60570.unfold_until);
            unfold_only = (uu___625_60570.unfold_only);
            unfold_fully = (uu___625_60570.unfold_fully);
            unfold_attr = (uu___625_60570.unfold_attr);
            unfold_tac = (uu___625_60570.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_60570.pure_subterms_within_computations);
            simplify = (uu___625_60570.simplify);
            erase_universes = (uu___625_60570.erase_universes);
            allow_unbound_universes =
              (uu___625_60570.allow_unbound_universes);
            reify_ = (uu___625_60570.reify_);
            compress_uvars = (uu___625_60570.compress_uvars);
            no_full_norm = (uu___625_60570.no_full_norm);
            check_no_uvars = (uu___625_60570.check_no_uvars);
            unmeta = (uu___625_60570.unmeta);
            unascribe = (uu___625_60570.unascribe);
            in_full_norm_request = (uu___625_60570.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_60570.weakly_reduce_scrutinee);
            nbe_step = (uu___625_60570.nbe_step);
            for_extraction = (uu___625_60570.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_60572 = fs  in
          {
            beta = (uu___628_60572.beta);
            iota = true;
            zeta = (uu___628_60572.zeta);
            weak = (uu___628_60572.weak);
            hnf = (uu___628_60572.hnf);
            primops = (uu___628_60572.primops);
            do_not_unfold_pure_lets =
              (uu___628_60572.do_not_unfold_pure_lets);
            unfold_until = (uu___628_60572.unfold_until);
            unfold_only = (uu___628_60572.unfold_only);
            unfold_fully = (uu___628_60572.unfold_fully);
            unfold_attr = (uu___628_60572.unfold_attr);
            unfold_tac = (uu___628_60572.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_60572.pure_subterms_within_computations);
            simplify = (uu___628_60572.simplify);
            erase_universes = (uu___628_60572.erase_universes);
            allow_unbound_universes =
              (uu___628_60572.allow_unbound_universes);
            reify_ = (uu___628_60572.reify_);
            compress_uvars = (uu___628_60572.compress_uvars);
            no_full_norm = (uu___628_60572.no_full_norm);
            check_no_uvars = (uu___628_60572.check_no_uvars);
            unmeta = (uu___628_60572.unmeta);
            unascribe = (uu___628_60572.unascribe);
            in_full_norm_request = (uu___628_60572.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_60572.weakly_reduce_scrutinee);
            nbe_step = (uu___628_60572.nbe_step);
            for_extraction = (uu___628_60572.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_60574 = fs  in
          {
            beta = (uu___631_60574.beta);
            iota = (uu___631_60574.iota);
            zeta = true;
            weak = (uu___631_60574.weak);
            hnf = (uu___631_60574.hnf);
            primops = (uu___631_60574.primops);
            do_not_unfold_pure_lets =
              (uu___631_60574.do_not_unfold_pure_lets);
            unfold_until = (uu___631_60574.unfold_until);
            unfold_only = (uu___631_60574.unfold_only);
            unfold_fully = (uu___631_60574.unfold_fully);
            unfold_attr = (uu___631_60574.unfold_attr);
            unfold_tac = (uu___631_60574.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_60574.pure_subterms_within_computations);
            simplify = (uu___631_60574.simplify);
            erase_universes = (uu___631_60574.erase_universes);
            allow_unbound_universes =
              (uu___631_60574.allow_unbound_universes);
            reify_ = (uu___631_60574.reify_);
            compress_uvars = (uu___631_60574.compress_uvars);
            no_full_norm = (uu___631_60574.no_full_norm);
            check_no_uvars = (uu___631_60574.check_no_uvars);
            unmeta = (uu___631_60574.unmeta);
            unascribe = (uu___631_60574.unascribe);
            in_full_norm_request = (uu___631_60574.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_60574.weakly_reduce_scrutinee);
            nbe_step = (uu___631_60574.nbe_step);
            for_extraction = (uu___631_60574.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_60576 = fs  in
          {
            beta = false;
            iota = (uu___635_60576.iota);
            zeta = (uu___635_60576.zeta);
            weak = (uu___635_60576.weak);
            hnf = (uu___635_60576.hnf);
            primops = (uu___635_60576.primops);
            do_not_unfold_pure_lets =
              (uu___635_60576.do_not_unfold_pure_lets);
            unfold_until = (uu___635_60576.unfold_until);
            unfold_only = (uu___635_60576.unfold_only);
            unfold_fully = (uu___635_60576.unfold_fully);
            unfold_attr = (uu___635_60576.unfold_attr);
            unfold_tac = (uu___635_60576.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_60576.pure_subterms_within_computations);
            simplify = (uu___635_60576.simplify);
            erase_universes = (uu___635_60576.erase_universes);
            allow_unbound_universes =
              (uu___635_60576.allow_unbound_universes);
            reify_ = (uu___635_60576.reify_);
            compress_uvars = (uu___635_60576.compress_uvars);
            no_full_norm = (uu___635_60576.no_full_norm);
            check_no_uvars = (uu___635_60576.check_no_uvars);
            unmeta = (uu___635_60576.unmeta);
            unascribe = (uu___635_60576.unascribe);
            in_full_norm_request = (uu___635_60576.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_60576.weakly_reduce_scrutinee);
            nbe_step = (uu___635_60576.nbe_step);
            for_extraction = (uu___635_60576.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_60578 = fs  in
          {
            beta = (uu___639_60578.beta);
            iota = false;
            zeta = (uu___639_60578.zeta);
            weak = (uu___639_60578.weak);
            hnf = (uu___639_60578.hnf);
            primops = (uu___639_60578.primops);
            do_not_unfold_pure_lets =
              (uu___639_60578.do_not_unfold_pure_lets);
            unfold_until = (uu___639_60578.unfold_until);
            unfold_only = (uu___639_60578.unfold_only);
            unfold_fully = (uu___639_60578.unfold_fully);
            unfold_attr = (uu___639_60578.unfold_attr);
            unfold_tac = (uu___639_60578.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_60578.pure_subterms_within_computations);
            simplify = (uu___639_60578.simplify);
            erase_universes = (uu___639_60578.erase_universes);
            allow_unbound_universes =
              (uu___639_60578.allow_unbound_universes);
            reify_ = (uu___639_60578.reify_);
            compress_uvars = (uu___639_60578.compress_uvars);
            no_full_norm = (uu___639_60578.no_full_norm);
            check_no_uvars = (uu___639_60578.check_no_uvars);
            unmeta = (uu___639_60578.unmeta);
            unascribe = (uu___639_60578.unascribe);
            in_full_norm_request = (uu___639_60578.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_60578.weakly_reduce_scrutinee);
            nbe_step = (uu___639_60578.nbe_step);
            for_extraction = (uu___639_60578.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_60580 = fs  in
          {
            beta = (uu___643_60580.beta);
            iota = (uu___643_60580.iota);
            zeta = false;
            weak = (uu___643_60580.weak);
            hnf = (uu___643_60580.hnf);
            primops = (uu___643_60580.primops);
            do_not_unfold_pure_lets =
              (uu___643_60580.do_not_unfold_pure_lets);
            unfold_until = (uu___643_60580.unfold_until);
            unfold_only = (uu___643_60580.unfold_only);
            unfold_fully = (uu___643_60580.unfold_fully);
            unfold_attr = (uu___643_60580.unfold_attr);
            unfold_tac = (uu___643_60580.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_60580.pure_subterms_within_computations);
            simplify = (uu___643_60580.simplify);
            erase_universes = (uu___643_60580.erase_universes);
            allow_unbound_universes =
              (uu___643_60580.allow_unbound_universes);
            reify_ = (uu___643_60580.reify_);
            compress_uvars = (uu___643_60580.compress_uvars);
            no_full_norm = (uu___643_60580.no_full_norm);
            check_no_uvars = (uu___643_60580.check_no_uvars);
            unmeta = (uu___643_60580.unmeta);
            unascribe = (uu___643_60580.unascribe);
            in_full_norm_request = (uu___643_60580.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_60580.weakly_reduce_scrutinee);
            nbe_step = (uu___643_60580.nbe_step);
            for_extraction = (uu___643_60580.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____60582 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_60584 = fs  in
          {
            beta = (uu___648_60584.beta);
            iota = (uu___648_60584.iota);
            zeta = (uu___648_60584.zeta);
            weak = true;
            hnf = (uu___648_60584.hnf);
            primops = (uu___648_60584.primops);
            do_not_unfold_pure_lets =
              (uu___648_60584.do_not_unfold_pure_lets);
            unfold_until = (uu___648_60584.unfold_until);
            unfold_only = (uu___648_60584.unfold_only);
            unfold_fully = (uu___648_60584.unfold_fully);
            unfold_attr = (uu___648_60584.unfold_attr);
            unfold_tac = (uu___648_60584.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_60584.pure_subterms_within_computations);
            simplify = (uu___648_60584.simplify);
            erase_universes = (uu___648_60584.erase_universes);
            allow_unbound_universes =
              (uu___648_60584.allow_unbound_universes);
            reify_ = (uu___648_60584.reify_);
            compress_uvars = (uu___648_60584.compress_uvars);
            no_full_norm = (uu___648_60584.no_full_norm);
            check_no_uvars = (uu___648_60584.check_no_uvars);
            unmeta = (uu___648_60584.unmeta);
            unascribe = (uu___648_60584.unascribe);
            in_full_norm_request = (uu___648_60584.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_60584.weakly_reduce_scrutinee);
            nbe_step = (uu___648_60584.nbe_step);
            for_extraction = (uu___648_60584.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_60586 = fs  in
          {
            beta = (uu___651_60586.beta);
            iota = (uu___651_60586.iota);
            zeta = (uu___651_60586.zeta);
            weak = (uu___651_60586.weak);
            hnf = true;
            primops = (uu___651_60586.primops);
            do_not_unfold_pure_lets =
              (uu___651_60586.do_not_unfold_pure_lets);
            unfold_until = (uu___651_60586.unfold_until);
            unfold_only = (uu___651_60586.unfold_only);
            unfold_fully = (uu___651_60586.unfold_fully);
            unfold_attr = (uu___651_60586.unfold_attr);
            unfold_tac = (uu___651_60586.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_60586.pure_subterms_within_computations);
            simplify = (uu___651_60586.simplify);
            erase_universes = (uu___651_60586.erase_universes);
            allow_unbound_universes =
              (uu___651_60586.allow_unbound_universes);
            reify_ = (uu___651_60586.reify_);
            compress_uvars = (uu___651_60586.compress_uvars);
            no_full_norm = (uu___651_60586.no_full_norm);
            check_no_uvars = (uu___651_60586.check_no_uvars);
            unmeta = (uu___651_60586.unmeta);
            unascribe = (uu___651_60586.unascribe);
            in_full_norm_request = (uu___651_60586.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_60586.weakly_reduce_scrutinee);
            nbe_step = (uu___651_60586.nbe_step);
            for_extraction = (uu___651_60586.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_60588 = fs  in
          {
            beta = (uu___654_60588.beta);
            iota = (uu___654_60588.iota);
            zeta = (uu___654_60588.zeta);
            weak = (uu___654_60588.weak);
            hnf = (uu___654_60588.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_60588.do_not_unfold_pure_lets);
            unfold_until = (uu___654_60588.unfold_until);
            unfold_only = (uu___654_60588.unfold_only);
            unfold_fully = (uu___654_60588.unfold_fully);
            unfold_attr = (uu___654_60588.unfold_attr);
            unfold_tac = (uu___654_60588.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_60588.pure_subterms_within_computations);
            simplify = (uu___654_60588.simplify);
            erase_universes = (uu___654_60588.erase_universes);
            allow_unbound_universes =
              (uu___654_60588.allow_unbound_universes);
            reify_ = (uu___654_60588.reify_);
            compress_uvars = (uu___654_60588.compress_uvars);
            no_full_norm = (uu___654_60588.no_full_norm);
            check_no_uvars = (uu___654_60588.check_no_uvars);
            unmeta = (uu___654_60588.unmeta);
            unascribe = (uu___654_60588.unascribe);
            in_full_norm_request = (uu___654_60588.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_60588.weakly_reduce_scrutinee);
            nbe_step = (uu___654_60588.nbe_step);
            for_extraction = (uu___654_60588.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_60590 = fs  in
          {
            beta = (uu___659_60590.beta);
            iota = (uu___659_60590.iota);
            zeta = (uu___659_60590.zeta);
            weak = (uu___659_60590.weak);
            hnf = (uu___659_60590.hnf);
            primops = (uu___659_60590.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_60590.unfold_until);
            unfold_only = (uu___659_60590.unfold_only);
            unfold_fully = (uu___659_60590.unfold_fully);
            unfold_attr = (uu___659_60590.unfold_attr);
            unfold_tac = (uu___659_60590.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_60590.pure_subterms_within_computations);
            simplify = (uu___659_60590.simplify);
            erase_universes = (uu___659_60590.erase_universes);
            allow_unbound_universes =
              (uu___659_60590.allow_unbound_universes);
            reify_ = (uu___659_60590.reify_);
            compress_uvars = (uu___659_60590.compress_uvars);
            no_full_norm = (uu___659_60590.no_full_norm);
            check_no_uvars = (uu___659_60590.check_no_uvars);
            unmeta = (uu___659_60590.unmeta);
            unascribe = (uu___659_60590.unascribe);
            in_full_norm_request = (uu___659_60590.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_60590.weakly_reduce_scrutinee);
            nbe_step = (uu___659_60590.nbe_step);
            for_extraction = (uu___659_60590.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_60593 = fs  in
          {
            beta = (uu___663_60593.beta);
            iota = (uu___663_60593.iota);
            zeta = (uu___663_60593.zeta);
            weak = (uu___663_60593.weak);
            hnf = (uu___663_60593.hnf);
            primops = (uu___663_60593.primops);
            do_not_unfold_pure_lets =
              (uu___663_60593.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_60593.unfold_only);
            unfold_fully = (uu___663_60593.unfold_fully);
            unfold_attr = (uu___663_60593.unfold_attr);
            unfold_tac = (uu___663_60593.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_60593.pure_subterms_within_computations);
            simplify = (uu___663_60593.simplify);
            erase_universes = (uu___663_60593.erase_universes);
            allow_unbound_universes =
              (uu___663_60593.allow_unbound_universes);
            reify_ = (uu___663_60593.reify_);
            compress_uvars = (uu___663_60593.compress_uvars);
            no_full_norm = (uu___663_60593.no_full_norm);
            check_no_uvars = (uu___663_60593.check_no_uvars);
            unmeta = (uu___663_60593.unmeta);
            unascribe = (uu___663_60593.unascribe);
            in_full_norm_request = (uu___663_60593.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_60593.weakly_reduce_scrutinee);
            nbe_step = (uu___663_60593.nbe_step);
            for_extraction = (uu___663_60593.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_60597 = fs  in
          {
            beta = (uu___667_60597.beta);
            iota = (uu___667_60597.iota);
            zeta = (uu___667_60597.zeta);
            weak = (uu___667_60597.weak);
            hnf = (uu___667_60597.hnf);
            primops = (uu___667_60597.primops);
            do_not_unfold_pure_lets =
              (uu___667_60597.do_not_unfold_pure_lets);
            unfold_until = (uu___667_60597.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_60597.unfold_fully);
            unfold_attr = (uu___667_60597.unfold_attr);
            unfold_tac = (uu___667_60597.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_60597.pure_subterms_within_computations);
            simplify = (uu___667_60597.simplify);
            erase_universes = (uu___667_60597.erase_universes);
            allow_unbound_universes =
              (uu___667_60597.allow_unbound_universes);
            reify_ = (uu___667_60597.reify_);
            compress_uvars = (uu___667_60597.compress_uvars);
            no_full_norm = (uu___667_60597.no_full_norm);
            check_no_uvars = (uu___667_60597.check_no_uvars);
            unmeta = (uu___667_60597.unmeta);
            unascribe = (uu___667_60597.unascribe);
            in_full_norm_request = (uu___667_60597.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_60597.weakly_reduce_scrutinee);
            nbe_step = (uu___667_60597.nbe_step);
            for_extraction = (uu___667_60597.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_60603 = fs  in
          {
            beta = (uu___671_60603.beta);
            iota = (uu___671_60603.iota);
            zeta = (uu___671_60603.zeta);
            weak = (uu___671_60603.weak);
            hnf = (uu___671_60603.hnf);
            primops = (uu___671_60603.primops);
            do_not_unfold_pure_lets =
              (uu___671_60603.do_not_unfold_pure_lets);
            unfold_until = (uu___671_60603.unfold_until);
            unfold_only = (uu___671_60603.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_60603.unfold_attr);
            unfold_tac = (uu___671_60603.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_60603.pure_subterms_within_computations);
            simplify = (uu___671_60603.simplify);
            erase_universes = (uu___671_60603.erase_universes);
            allow_unbound_universes =
              (uu___671_60603.allow_unbound_universes);
            reify_ = (uu___671_60603.reify_);
            compress_uvars = (uu___671_60603.compress_uvars);
            no_full_norm = (uu___671_60603.no_full_norm);
            check_no_uvars = (uu___671_60603.check_no_uvars);
            unmeta = (uu___671_60603.unmeta);
            unascribe = (uu___671_60603.unascribe);
            in_full_norm_request = (uu___671_60603.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_60603.weakly_reduce_scrutinee);
            nbe_step = (uu___671_60603.nbe_step);
            for_extraction = (uu___671_60603.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_60609 = fs  in
          {
            beta = (uu___675_60609.beta);
            iota = (uu___675_60609.iota);
            zeta = (uu___675_60609.zeta);
            weak = (uu___675_60609.weak);
            hnf = (uu___675_60609.hnf);
            primops = (uu___675_60609.primops);
            do_not_unfold_pure_lets =
              (uu___675_60609.do_not_unfold_pure_lets);
            unfold_until = (uu___675_60609.unfold_until);
            unfold_only = (uu___675_60609.unfold_only);
            unfold_fully = (uu___675_60609.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_60609.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_60609.pure_subterms_within_computations);
            simplify = (uu___675_60609.simplify);
            erase_universes = (uu___675_60609.erase_universes);
            allow_unbound_universes =
              (uu___675_60609.allow_unbound_universes);
            reify_ = (uu___675_60609.reify_);
            compress_uvars = (uu___675_60609.compress_uvars);
            no_full_norm = (uu___675_60609.no_full_norm);
            check_no_uvars = (uu___675_60609.check_no_uvars);
            unmeta = (uu___675_60609.unmeta);
            unascribe = (uu___675_60609.unascribe);
            in_full_norm_request = (uu___675_60609.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_60609.weakly_reduce_scrutinee);
            nbe_step = (uu___675_60609.nbe_step);
            for_extraction = (uu___675_60609.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_60612 = fs  in
          {
            beta = (uu___678_60612.beta);
            iota = (uu___678_60612.iota);
            zeta = (uu___678_60612.zeta);
            weak = (uu___678_60612.weak);
            hnf = (uu___678_60612.hnf);
            primops = (uu___678_60612.primops);
            do_not_unfold_pure_lets =
              (uu___678_60612.do_not_unfold_pure_lets);
            unfold_until = (uu___678_60612.unfold_until);
            unfold_only = (uu___678_60612.unfold_only);
            unfold_fully = (uu___678_60612.unfold_fully);
            unfold_attr = (uu___678_60612.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_60612.pure_subterms_within_computations);
            simplify = (uu___678_60612.simplify);
            erase_universes = (uu___678_60612.erase_universes);
            allow_unbound_universes =
              (uu___678_60612.allow_unbound_universes);
            reify_ = (uu___678_60612.reify_);
            compress_uvars = (uu___678_60612.compress_uvars);
            no_full_norm = (uu___678_60612.no_full_norm);
            check_no_uvars = (uu___678_60612.check_no_uvars);
            unmeta = (uu___678_60612.unmeta);
            unascribe = (uu___678_60612.unascribe);
            in_full_norm_request = (uu___678_60612.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_60612.weakly_reduce_scrutinee);
            nbe_step = (uu___678_60612.nbe_step);
            for_extraction = (uu___678_60612.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_60614 = fs  in
          {
            beta = (uu___681_60614.beta);
            iota = (uu___681_60614.iota);
            zeta = (uu___681_60614.zeta);
            weak = (uu___681_60614.weak);
            hnf = (uu___681_60614.hnf);
            primops = (uu___681_60614.primops);
            do_not_unfold_pure_lets =
              (uu___681_60614.do_not_unfold_pure_lets);
            unfold_until = (uu___681_60614.unfold_until);
            unfold_only = (uu___681_60614.unfold_only);
            unfold_fully = (uu___681_60614.unfold_fully);
            unfold_attr = (uu___681_60614.unfold_attr);
            unfold_tac = (uu___681_60614.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_60614.simplify);
            erase_universes = (uu___681_60614.erase_universes);
            allow_unbound_universes =
              (uu___681_60614.allow_unbound_universes);
            reify_ = (uu___681_60614.reify_);
            compress_uvars = (uu___681_60614.compress_uvars);
            no_full_norm = (uu___681_60614.no_full_norm);
            check_no_uvars = (uu___681_60614.check_no_uvars);
            unmeta = (uu___681_60614.unmeta);
            unascribe = (uu___681_60614.unascribe);
            in_full_norm_request = (uu___681_60614.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_60614.weakly_reduce_scrutinee);
            nbe_step = (uu___681_60614.nbe_step);
            for_extraction = (uu___681_60614.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_60616 = fs  in
          {
            beta = (uu___684_60616.beta);
            iota = (uu___684_60616.iota);
            zeta = (uu___684_60616.zeta);
            weak = (uu___684_60616.weak);
            hnf = (uu___684_60616.hnf);
            primops = (uu___684_60616.primops);
            do_not_unfold_pure_lets =
              (uu___684_60616.do_not_unfold_pure_lets);
            unfold_until = (uu___684_60616.unfold_until);
            unfold_only = (uu___684_60616.unfold_only);
            unfold_fully = (uu___684_60616.unfold_fully);
            unfold_attr = (uu___684_60616.unfold_attr);
            unfold_tac = (uu___684_60616.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_60616.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_60616.erase_universes);
            allow_unbound_universes =
              (uu___684_60616.allow_unbound_universes);
            reify_ = (uu___684_60616.reify_);
            compress_uvars = (uu___684_60616.compress_uvars);
            no_full_norm = (uu___684_60616.no_full_norm);
            check_no_uvars = (uu___684_60616.check_no_uvars);
            unmeta = (uu___684_60616.unmeta);
            unascribe = (uu___684_60616.unascribe);
            in_full_norm_request = (uu___684_60616.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_60616.weakly_reduce_scrutinee);
            nbe_step = (uu___684_60616.nbe_step);
            for_extraction = (uu___684_60616.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_60618 = fs  in
          {
            beta = (uu___687_60618.beta);
            iota = (uu___687_60618.iota);
            zeta = (uu___687_60618.zeta);
            weak = (uu___687_60618.weak);
            hnf = (uu___687_60618.hnf);
            primops = (uu___687_60618.primops);
            do_not_unfold_pure_lets =
              (uu___687_60618.do_not_unfold_pure_lets);
            unfold_until = (uu___687_60618.unfold_until);
            unfold_only = (uu___687_60618.unfold_only);
            unfold_fully = (uu___687_60618.unfold_fully);
            unfold_attr = (uu___687_60618.unfold_attr);
            unfold_tac = (uu___687_60618.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_60618.pure_subterms_within_computations);
            simplify = (uu___687_60618.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_60618.allow_unbound_universes);
            reify_ = (uu___687_60618.reify_);
            compress_uvars = (uu___687_60618.compress_uvars);
            no_full_norm = (uu___687_60618.no_full_norm);
            check_no_uvars = (uu___687_60618.check_no_uvars);
            unmeta = (uu___687_60618.unmeta);
            unascribe = (uu___687_60618.unascribe);
            in_full_norm_request = (uu___687_60618.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_60618.weakly_reduce_scrutinee);
            nbe_step = (uu___687_60618.nbe_step);
            for_extraction = (uu___687_60618.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_60620 = fs  in
          {
            beta = (uu___690_60620.beta);
            iota = (uu___690_60620.iota);
            zeta = (uu___690_60620.zeta);
            weak = (uu___690_60620.weak);
            hnf = (uu___690_60620.hnf);
            primops = (uu___690_60620.primops);
            do_not_unfold_pure_lets =
              (uu___690_60620.do_not_unfold_pure_lets);
            unfold_until = (uu___690_60620.unfold_until);
            unfold_only = (uu___690_60620.unfold_only);
            unfold_fully = (uu___690_60620.unfold_fully);
            unfold_attr = (uu___690_60620.unfold_attr);
            unfold_tac = (uu___690_60620.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_60620.pure_subterms_within_computations);
            simplify = (uu___690_60620.simplify);
            erase_universes = (uu___690_60620.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_60620.reify_);
            compress_uvars = (uu___690_60620.compress_uvars);
            no_full_norm = (uu___690_60620.no_full_norm);
            check_no_uvars = (uu___690_60620.check_no_uvars);
            unmeta = (uu___690_60620.unmeta);
            unascribe = (uu___690_60620.unascribe);
            in_full_norm_request = (uu___690_60620.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_60620.weakly_reduce_scrutinee);
            nbe_step = (uu___690_60620.nbe_step);
            for_extraction = (uu___690_60620.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_60622 = fs  in
          {
            beta = (uu___693_60622.beta);
            iota = (uu___693_60622.iota);
            zeta = (uu___693_60622.zeta);
            weak = (uu___693_60622.weak);
            hnf = (uu___693_60622.hnf);
            primops = (uu___693_60622.primops);
            do_not_unfold_pure_lets =
              (uu___693_60622.do_not_unfold_pure_lets);
            unfold_until = (uu___693_60622.unfold_until);
            unfold_only = (uu___693_60622.unfold_only);
            unfold_fully = (uu___693_60622.unfold_fully);
            unfold_attr = (uu___693_60622.unfold_attr);
            unfold_tac = (uu___693_60622.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_60622.pure_subterms_within_computations);
            simplify = (uu___693_60622.simplify);
            erase_universes = (uu___693_60622.erase_universes);
            allow_unbound_universes =
              (uu___693_60622.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_60622.compress_uvars);
            no_full_norm = (uu___693_60622.no_full_norm);
            check_no_uvars = (uu___693_60622.check_no_uvars);
            unmeta = (uu___693_60622.unmeta);
            unascribe = (uu___693_60622.unascribe);
            in_full_norm_request = (uu___693_60622.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_60622.weakly_reduce_scrutinee);
            nbe_step = (uu___693_60622.nbe_step);
            for_extraction = (uu___693_60622.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_60624 = fs  in
          {
            beta = (uu___696_60624.beta);
            iota = (uu___696_60624.iota);
            zeta = (uu___696_60624.zeta);
            weak = (uu___696_60624.weak);
            hnf = (uu___696_60624.hnf);
            primops = (uu___696_60624.primops);
            do_not_unfold_pure_lets =
              (uu___696_60624.do_not_unfold_pure_lets);
            unfold_until = (uu___696_60624.unfold_until);
            unfold_only = (uu___696_60624.unfold_only);
            unfold_fully = (uu___696_60624.unfold_fully);
            unfold_attr = (uu___696_60624.unfold_attr);
            unfold_tac = (uu___696_60624.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_60624.pure_subterms_within_computations);
            simplify = (uu___696_60624.simplify);
            erase_universes = (uu___696_60624.erase_universes);
            allow_unbound_universes =
              (uu___696_60624.allow_unbound_universes);
            reify_ = (uu___696_60624.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_60624.no_full_norm);
            check_no_uvars = (uu___696_60624.check_no_uvars);
            unmeta = (uu___696_60624.unmeta);
            unascribe = (uu___696_60624.unascribe);
            in_full_norm_request = (uu___696_60624.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_60624.weakly_reduce_scrutinee);
            nbe_step = (uu___696_60624.nbe_step);
            for_extraction = (uu___696_60624.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_60626 = fs  in
          {
            beta = (uu___699_60626.beta);
            iota = (uu___699_60626.iota);
            zeta = (uu___699_60626.zeta);
            weak = (uu___699_60626.weak);
            hnf = (uu___699_60626.hnf);
            primops = (uu___699_60626.primops);
            do_not_unfold_pure_lets =
              (uu___699_60626.do_not_unfold_pure_lets);
            unfold_until = (uu___699_60626.unfold_until);
            unfold_only = (uu___699_60626.unfold_only);
            unfold_fully = (uu___699_60626.unfold_fully);
            unfold_attr = (uu___699_60626.unfold_attr);
            unfold_tac = (uu___699_60626.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_60626.pure_subterms_within_computations);
            simplify = (uu___699_60626.simplify);
            erase_universes = (uu___699_60626.erase_universes);
            allow_unbound_universes =
              (uu___699_60626.allow_unbound_universes);
            reify_ = (uu___699_60626.reify_);
            compress_uvars = (uu___699_60626.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_60626.check_no_uvars);
            unmeta = (uu___699_60626.unmeta);
            unascribe = (uu___699_60626.unascribe);
            in_full_norm_request = (uu___699_60626.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_60626.weakly_reduce_scrutinee);
            nbe_step = (uu___699_60626.nbe_step);
            for_extraction = (uu___699_60626.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_60628 = fs  in
          {
            beta = (uu___702_60628.beta);
            iota = (uu___702_60628.iota);
            zeta = (uu___702_60628.zeta);
            weak = (uu___702_60628.weak);
            hnf = (uu___702_60628.hnf);
            primops = (uu___702_60628.primops);
            do_not_unfold_pure_lets =
              (uu___702_60628.do_not_unfold_pure_lets);
            unfold_until = (uu___702_60628.unfold_until);
            unfold_only = (uu___702_60628.unfold_only);
            unfold_fully = (uu___702_60628.unfold_fully);
            unfold_attr = (uu___702_60628.unfold_attr);
            unfold_tac = (uu___702_60628.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_60628.pure_subterms_within_computations);
            simplify = (uu___702_60628.simplify);
            erase_universes = (uu___702_60628.erase_universes);
            allow_unbound_universes =
              (uu___702_60628.allow_unbound_universes);
            reify_ = (uu___702_60628.reify_);
            compress_uvars = (uu___702_60628.compress_uvars);
            no_full_norm = (uu___702_60628.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_60628.unmeta);
            unascribe = (uu___702_60628.unascribe);
            in_full_norm_request = (uu___702_60628.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_60628.weakly_reduce_scrutinee);
            nbe_step = (uu___702_60628.nbe_step);
            for_extraction = (uu___702_60628.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_60630 = fs  in
          {
            beta = (uu___705_60630.beta);
            iota = (uu___705_60630.iota);
            zeta = (uu___705_60630.zeta);
            weak = (uu___705_60630.weak);
            hnf = (uu___705_60630.hnf);
            primops = (uu___705_60630.primops);
            do_not_unfold_pure_lets =
              (uu___705_60630.do_not_unfold_pure_lets);
            unfold_until = (uu___705_60630.unfold_until);
            unfold_only = (uu___705_60630.unfold_only);
            unfold_fully = (uu___705_60630.unfold_fully);
            unfold_attr = (uu___705_60630.unfold_attr);
            unfold_tac = (uu___705_60630.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_60630.pure_subterms_within_computations);
            simplify = (uu___705_60630.simplify);
            erase_universes = (uu___705_60630.erase_universes);
            allow_unbound_universes =
              (uu___705_60630.allow_unbound_universes);
            reify_ = (uu___705_60630.reify_);
            compress_uvars = (uu___705_60630.compress_uvars);
            no_full_norm = (uu___705_60630.no_full_norm);
            check_no_uvars = (uu___705_60630.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_60630.unascribe);
            in_full_norm_request = (uu___705_60630.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_60630.weakly_reduce_scrutinee);
            nbe_step = (uu___705_60630.nbe_step);
            for_extraction = (uu___705_60630.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_60632 = fs  in
          {
            beta = (uu___708_60632.beta);
            iota = (uu___708_60632.iota);
            zeta = (uu___708_60632.zeta);
            weak = (uu___708_60632.weak);
            hnf = (uu___708_60632.hnf);
            primops = (uu___708_60632.primops);
            do_not_unfold_pure_lets =
              (uu___708_60632.do_not_unfold_pure_lets);
            unfold_until = (uu___708_60632.unfold_until);
            unfold_only = (uu___708_60632.unfold_only);
            unfold_fully = (uu___708_60632.unfold_fully);
            unfold_attr = (uu___708_60632.unfold_attr);
            unfold_tac = (uu___708_60632.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_60632.pure_subterms_within_computations);
            simplify = (uu___708_60632.simplify);
            erase_universes = (uu___708_60632.erase_universes);
            allow_unbound_universes =
              (uu___708_60632.allow_unbound_universes);
            reify_ = (uu___708_60632.reify_);
            compress_uvars = (uu___708_60632.compress_uvars);
            no_full_norm = (uu___708_60632.no_full_norm);
            check_no_uvars = (uu___708_60632.check_no_uvars);
            unmeta = (uu___708_60632.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_60632.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_60632.weakly_reduce_scrutinee);
            nbe_step = (uu___708_60632.nbe_step);
            for_extraction = (uu___708_60632.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_60634 = fs  in
          {
            beta = (uu___711_60634.beta);
            iota = (uu___711_60634.iota);
            zeta = (uu___711_60634.zeta);
            weak = (uu___711_60634.weak);
            hnf = (uu___711_60634.hnf);
            primops = (uu___711_60634.primops);
            do_not_unfold_pure_lets =
              (uu___711_60634.do_not_unfold_pure_lets);
            unfold_until = (uu___711_60634.unfold_until);
            unfold_only = (uu___711_60634.unfold_only);
            unfold_fully = (uu___711_60634.unfold_fully);
            unfold_attr = (uu___711_60634.unfold_attr);
            unfold_tac = (uu___711_60634.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_60634.pure_subterms_within_computations);
            simplify = (uu___711_60634.simplify);
            erase_universes = (uu___711_60634.erase_universes);
            allow_unbound_universes =
              (uu___711_60634.allow_unbound_universes);
            reify_ = (uu___711_60634.reify_);
            compress_uvars = (uu___711_60634.compress_uvars);
            no_full_norm = (uu___711_60634.no_full_norm);
            check_no_uvars = (uu___711_60634.check_no_uvars);
            unmeta = (uu___711_60634.unmeta);
            unascribe = (uu___711_60634.unascribe);
            in_full_norm_request = (uu___711_60634.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_60634.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_60634.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_60636 = fs  in
          {
            beta = (uu___714_60636.beta);
            iota = (uu___714_60636.iota);
            zeta = (uu___714_60636.zeta);
            weak = (uu___714_60636.weak);
            hnf = (uu___714_60636.hnf);
            primops = (uu___714_60636.primops);
            do_not_unfold_pure_lets =
              (uu___714_60636.do_not_unfold_pure_lets);
            unfold_until = (uu___714_60636.unfold_until);
            unfold_only = (uu___714_60636.unfold_only);
            unfold_fully = (uu___714_60636.unfold_fully);
            unfold_attr = (uu___714_60636.unfold_attr);
            unfold_tac = (uu___714_60636.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_60636.pure_subterms_within_computations);
            simplify = (uu___714_60636.simplify);
            erase_universes = (uu___714_60636.erase_universes);
            allow_unbound_universes =
              (uu___714_60636.allow_unbound_universes);
            reify_ = (uu___714_60636.reify_);
            compress_uvars = (uu___714_60636.compress_uvars);
            no_full_norm = (uu___714_60636.no_full_norm);
            check_no_uvars = (uu___714_60636.check_no_uvars);
            unmeta = (uu___714_60636.unmeta);
            unascribe = (uu___714_60636.unascribe);
            in_full_norm_request = (uu___714_60636.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_60636.weakly_reduce_scrutinee);
            nbe_step = (uu___714_60636.nbe_step);
            for_extraction = true
          }
  
let (to_fsteps : FStar_TypeChecker_Env.step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: unit -> FStar_Syntax_Syntax.subst_t }
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee  ->
    match projectee with | { psc_range; psc_subst;_} -> psc_range
  
let (__proj__Mkpsc__item__psc_subst :
  psc -> unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee  ->
    match projectee with | { psc_range; psc_subst;_} -> psc_subst
  
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____60694  -> [])
  } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
type debug_switches =
  {
  gen: Prims.bool ;
  top: Prims.bool ;
  cfg: Prims.bool ;
  primop: Prims.bool ;
  unfolding: Prims.bool ;
  b380: Prims.bool ;
  wpe: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> gen1
  
let (__proj__Mkdebug_switches__item__top : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> top
  
let (__proj__Mkdebug_switches__item__cfg : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> cfg
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> primop
  
let (__proj__Mkdebug_switches__item__unfolding :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> unfolding
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> b380
  
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> wpe
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> print_normalized
  
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  univ_arity: Prims.int ;
  auto_reflect: Prims.int FStar_Pervasives_Native.option ;
  strong_reduction_ok: Prims.bool ;
  requires_binder_substitution: Prims.bool ;
  interpretation:
    psc ->
      FStar_Syntax_Embeddings.norm_cb ->
        FStar_Syntax_Syntax.args ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    ;
  interpretation_nbe:
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      FStar_TypeChecker_NBETerm.args ->
        FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
    }
let (__proj__Mkprimitive_step__item__name :
  primitive_step -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> name
  
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> arity
  
let (__proj__Mkprimitive_step__item__univ_arity :
  primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> univ_arity
  
let (__proj__Mkprimitive_step__item__auto_reflect :
  primitive_step -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> auto_reflect
  
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> strong_reduction_ok
  
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> requires_binder_substitution
  
let (__proj__Mkprimitive_step__item__interpretation :
  primitive_step ->
    psc ->
      FStar_Syntax_Embeddings.norm_cb ->
        FStar_Syntax_Syntax.args ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> interpretation
  
let (__proj__Mkprimitive_step__item__interpretation_nbe :
  primitive_step ->
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      FStar_TypeChecker_NBETerm.args ->
        FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> interpretation_nbe
  
type cfg =
  {
  steps: fsteps ;
  tcenv: FStar_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step FStar_Util.psmap ;
  strong: Prims.bool ;
  memoize_lazy: Prims.bool ;
  normalize_pure_lets: Prims.bool ;
  reifying: Prims.bool }
let (__proj__Mkcfg__item__steps : cfg -> fsteps) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> steps
  
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> tcenv
  
let (__proj__Mkcfg__item__debug : cfg -> debug_switches) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> debug1
  
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> delta_level
  
let (__proj__Mkcfg__item__primitive_steps :
  cfg -> primitive_step FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> primitive_steps
  
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> strong
  
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> memoize_lazy
  
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> normalize_pure_lets
  
let (__proj__Mkcfg__item__reifying : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> reifying
  
let (cfg_to_string : cfg -> Prims.string) =
  fun cfg  ->
    let uu____61743 =
      let uu____61747 =
        let uu____61751 =
          let uu____61753 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____61753  in
        [uu____61751; "}"]  in
      "{" :: uu____61747  in
    FStar_String.concat "\n" uu____61743
  
let (cfg_env : cfg -> FStar_TypeChecker_Env.env) = fun cfg  -> cfg.tcenv 
let (add_steps :
  primitive_step FStar_Util.psmap ->
    primitive_step Prims.list -> primitive_step FStar_Util.psmap)
  =
  fun m  ->
    fun l  ->
      FStar_List.fold_right
        (fun p  ->
           fun m1  ->
             let uu____61801 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____61801 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____61817 = FStar_Util.psmap_empty ()  in add_steps uu____61817 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____61833 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____61833
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____61847 =
        let uu____61850 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____61850  in
      FStar_Util.is_some uu____61847
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_top : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).top then f () else () 
let (log_cfg : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).cfg then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let (log_unfolding : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).unfolding then f () else () 
let (log_nbe : cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____61963 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____61963 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____61999 = FStar_Syntax_Embeddings.embed emb x  in
        uu____61999 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____62032 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____62032 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____62047 .
    'Auu____62047 ->
      FStar_Range.range -> 'Auu____62047 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_int)
     in
  let arg_as_bool1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_bool)
     in
  let arg_as_char1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_char)
     in
  let arg_as_string1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_string)
     in
  let arg_as_list1 e a =
    let uu____62168 =
      let uu____62177 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____62177  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62168  in
  let arg_as_bounded_int1 uu____62207 =
    match uu____62207 with
    | (a,uu____62221) ->
        let uu____62232 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____62232 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____62276 =
               let uu____62291 =
                 let uu____62292 = FStar_Syntax_Subst.compress hd1  in
                 uu____62292.FStar_Syntax_Syntax.n  in
               (uu____62291, args)  in
             (match uu____62276 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____62313)::[]) when
                  let uu____62348 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____62348 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____62352 =
                    let uu____62353 = FStar_Syntax_Subst.compress arg1  in
                    uu____62353.FStar_Syntax_Syntax.n  in
                  (match uu____62352 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____62375 =
                         let uu____62380 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____62380)  in
                       FStar_Pervasives_Native.Some uu____62375
                   | uu____62385 -> FStar_Pervasives_Native.None)
              | uu____62390 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____62452 = f a  in FStar_Pervasives_Native.Some uu____62452
    | uu____62453 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____62509 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____62509
    | uu____62510 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____62577 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____62577  in
  let binary_op1 as_a f res n1 args =
    let uu____62659 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____62659  in
  let as_primitive_step is_strong uu____62714 =
    match uu____62714 with
    | (l,arity,u_arity,f,f_nbe) ->
        {
          name = l;
          arity;
          univ_arity = u_arity;
          auto_reflect = FStar_Pervasives_Native.None;
          strong_reduction_ok = is_strong;
          requires_binder_substitution = false;
          interpretation = f;
          interpretation_nbe = ((fun _cb  -> f_nbe))
        }
     in
  let unary_int_op1 f =
    unary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           let uu____62822 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____62822)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____62864 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____62864)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____62905 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____62905)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____62958 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____62958)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____63011 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____63011)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____63164 =
          let uu____63173 = as_a a  in
          let uu____63176 = as_b b  in (uu____63173, uu____63176)  in
        (match uu____63164 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____63191 =
               let uu____63192 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____63192  in
             FStar_Pervasives_Native.Some uu____63191
         | uu____63193 -> FStar_Pervasives_Native.None)
    | uu____63202 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____63224 =
        let uu____63225 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____63225  in
      mk uu____63224 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____63239 =
      let uu____63242 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____63242  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____63239
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____63290 =
      let uu____63291 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____63291  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____63290  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____63377 = arg_as_string1 a1  in
        (match uu____63377 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63386 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____63386 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____63404 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____63404
              | uu____63406 -> FStar_Pervasives_Native.None)
         | uu____63412 -> FStar_Pervasives_Native.None)
    | uu____63416 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63497 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____63497 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63513 = arg_as_string1 a2  in
             (match uu____63513 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____63526 =
                    let uu____63527 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____63527 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____63526
              | uu____63537 -> FStar_Pervasives_Native.None)
         | uu____63541 -> FStar_Pervasives_Native.None)
    | uu____63547 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____63585 =
          let uu____63599 = arg_as_string1 a1  in
          let uu____63603 = arg_as_int1 a2  in
          let uu____63606 = arg_as_int1 a3  in
          (uu____63599, uu____63603, uu____63606)  in
        (match uu____63585 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_63639  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____63644 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63644) ()
              with | uu___1030_63647 -> FStar_Pervasives_Native.None)
         | uu____63650 -> FStar_Pervasives_Native.None)
    | uu____63664 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____63678 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____63678  in
  let string_of_bool1 rng b =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let lowercase1 rng s =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (FStar_String.lowercase s)
     in
  let uppercase1 rng s =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (FStar_String.uppercase s)
     in
  let string_index1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63757 =
          let uu____63767 = arg_as_string1 a1  in
          let uu____63771 = arg_as_int1 a2  in (uu____63767, uu____63771)  in
        (match uu____63757 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_63795  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____63800 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63800) ()
              with | uu___1064_63803 -> FStar_Pervasives_Native.None)
         | uu____63806 -> FStar_Pervasives_Native.None)
    | uu____63816 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63847 =
          let uu____63858 = arg_as_string1 a1  in
          let uu____63862 = arg_as_char1 a2  in (uu____63858, uu____63862)
           in
        (match uu____63847 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_63891  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____63895 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63895) ()
              with | uu___1085_63897 -> FStar_Pervasives_Native.None)
         | uu____63900 -> FStar_Pervasives_Native.None)
    | uu____63911 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____63945 =
          let uu____63967 = arg_as_string1 fn  in
          let uu____63971 = arg_as_int1 from_line  in
          let uu____63974 = arg_as_int1 from_col  in
          let uu____63977 = arg_as_int1 to_line  in
          let uu____63980 = arg_as_int1 to_col  in
          (uu____63967, uu____63971, uu____63974, uu____63977, uu____63980)
           in
        (match uu____63945 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____64015 =
                 let uu____64016 = FStar_BigInt.to_int_fs from_l  in
                 let uu____64018 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____64016 uu____64018  in
               let uu____64020 =
                 let uu____64021 = FStar_BigInt.to_int_fs to_l  in
                 let uu____64023 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____64021 uu____64023  in
               FStar_Range.mk_range fn1 uu____64015 uu____64020  in
             let uu____64025 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64025
         | uu____64026 -> FStar_Pervasives_Native.None)
    | uu____64048 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____64092)::(a1,uu____64094)::(a2,uu____64096)::[] ->
        let uu____64153 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____64153 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____64162 -> FStar_Pervasives_Native.None)
    | uu____64163 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____64206)::[] ->
        let uu____64223 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____64223 with
         | FStar_Pervasives_Native.Some r ->
             let uu____64229 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64229
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____64230 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____64250  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____64284 =
      let uu____64314 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____64314)
       in
    let uu____64348 =
      let uu____64380 =
        let uu____64410 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____64410)
         in
      let uu____64450 =
        let uu____64482 =
          let uu____64512 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____64512)
           in
        let uu____64552 =
          let uu____64584 =
            let uu____64614 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____64614)
             in
          let uu____64654 =
            let uu____64686 =
              let uu____64716 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____64716)
               in
            let uu____64756 =
              let uu____64788 =
                let uu____64818 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____64830 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____64830)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____64861 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____64861)), uu____64818)
                 in
              let uu____64864 =
                let uu____64896 =
                  let uu____64926 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____64938 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____64938)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____64969 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____64969)), uu____64926)
                   in
                let uu____64972 =
                  let uu____65004 =
                    let uu____65034 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____65046 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____65046)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____65077 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____65077)), uu____65034)
                     in
                  let uu____65080 =
                    let uu____65112 =
                      let uu____65142 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____65154 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____65154)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____65185 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____65185)), uu____65142)
                       in
                    let uu____65188 =
                      let uu____65220 =
                        let uu____65250 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____65250)
                         in
                      let uu____65290 =
                        let uu____65322 =
                          let uu____65352 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____65352)
                           in
                        let uu____65388 =
                          let uu____65420 =
                            let uu____65450 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____65450)
                             in
                          let uu____65494 =
                            let uu____65526 =
                              let uu____65556 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____65556)
                               in
                            let uu____65600 =
                              let uu____65632 =
                                let uu____65662 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____65662)
                                 in
                              let uu____65690 =
                                let uu____65722 =
                                  let uu____65752 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____65752)
                                   in
                                let uu____65782 =
                                  let uu____65814 =
                                    let uu____65844 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____65844)
                                     in
                                  let uu____65874 =
                                    let uu____65906 =
                                      let uu____65936 =
                                        FStar_TypeChecker_NBETerm.unary_op
                                          (FStar_TypeChecker_NBETerm.arg_as_list
                                             FStar_TypeChecker_NBETerm.e_char)
                                          FStar_TypeChecker_NBETerm.string_of_list'
                                         in
                                      (FStar_Parser_Const.string_string_of_list_lid,
                                        (Prims.parse_int "1"),
                                        (Prims.parse_int "0"),
                                        (unary_op1
                                           (arg_as_list1
                                              FStar_Syntax_Embeddings.e_char)
                                           string_of_list'1), uu____65936)
                                       in
                                    let uu____65972 =
                                      let uu____66004 =
                                        let uu____66036 =
                                          let uu____66068 =
                                            let uu____66098 =
                                              FStar_TypeChecker_NBETerm.binary_string_op
                                                (fun x  ->
                                                   fun y  ->
                                                     FStar_String.op_Hat x y)
                                               in
                                            (FStar_Parser_Const.prims_strcat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              (binary_string_op1
                                                 (fun x  ->
                                                    fun y  ->
                                                      FStar_String.op_Hat x y)),
                                              uu____66098)
                                             in
                                          let uu____66142 =
                                            let uu____66174 =
                                              let uu____66206 =
                                                let uu____66236 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____66236)
                                                 in
                                              let uu____66266 =
                                                let uu____66298 =
                                                  let uu____66328 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____66328)
                                                   in
                                                let uu____66358 =
                                                  let uu____66390 =
                                                    let uu____66420 =
                                                      FStar_TypeChecker_NBETerm.unary_op
                                                        FStar_TypeChecker_NBETerm.arg_as_string
                                                        FStar_TypeChecker_NBETerm.string_uppercase
                                                       in
                                                    (FStar_Parser_Const.string_uppercase_lid,
                                                      (Prims.parse_int "1"),
                                                      (Prims.parse_int "0"),
                                                      (unary_op1
                                                         arg_as_string1
                                                         uppercase1),
                                                      uu____66420)
                                                     in
                                                  let uu____66450 =
                                                    let uu____66482 =
                                                      let uu____66514 =
                                                        let uu____66546 =
                                                          let uu____66578 =
                                                            let uu____66610 =
                                                              let uu____66642
                                                                =
                                                                let uu____66672
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____66672,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____66699
                                                                =
                                                                let uu____66731
                                                                  =
                                                                  let uu____66761
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____66761,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____66731]
                                                                 in
                                                              uu____66642 ::
                                                                uu____66699
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____66610
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____66578
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____66546
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____66514
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____66482
                                                     in
                                                  uu____66390 :: uu____66450
                                                   in
                                                uu____66298 :: uu____66358
                                                 in
                                              uu____66206 :: uu____66266  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____66174
                                             in
                                          uu____66068 :: uu____66142  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____66036
                                         in
                                      (FStar_Parser_Const.string_make_lid,
                                        (Prims.parse_int "2"),
                                        (Prims.parse_int "0"),
                                        (mixed_binary_op1 arg_as_int1
                                           arg_as_char1
                                           (embed_simple
                                              FStar_Syntax_Embeddings.e_string)
                                           (fun r  ->
                                              fun x  ->
                                                fun y  ->
                                                  let uu____67408 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____67408 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____67419 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____67419
                                                  y)))
                                        :: uu____66004
                                       in
                                    uu____65906 :: uu____65972  in
                                  uu____65814 :: uu____65874  in
                                uu____65722 :: uu____65782  in
                              uu____65632 :: uu____65690  in
                            uu____65526 :: uu____65600  in
                          uu____65420 :: uu____65494  in
                        uu____65322 :: uu____65388  in
                      uu____65220 :: uu____65290  in
                    uu____65112 :: uu____65188  in
                  uu____65004 :: uu____65080  in
                uu____64896 :: uu____64972  in
              uu____64788 :: uu____64864  in
            uu____64686 :: uu____64756  in
          uu____64584 :: uu____64654  in
        uu____64482 :: uu____64552  in
      uu____64380 :: uu____64450  in
    uu____64284 :: uu____64348  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____68055 =
        let uu____68060 =
          let uu____68061 = FStar_Syntax_Syntax.as_arg c  in [uu____68061]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____68060  in
      uu____68055 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____68188 =
                let uu____68218 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____68225 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____68243  ->
                       fun uu____68244  ->
                         match (uu____68243, uu____68244) with
                         | ((int_to_t1,x),(uu____68263,y)) ->
                             let uu____68273 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____68273)
                   in
                (uu____68218, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____68308  ->
                          fun uu____68309  ->
                            match (uu____68308, uu____68309) with
                            | ((int_to_t1,x),(uu____68328,y)) ->
                                let uu____68338 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____68338)),
                  uu____68225)
                 in
              let uu____68339 =
                let uu____68371 =
                  let uu____68401 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____68408 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____68426  ->
                         fun uu____68427  ->
                           match (uu____68426, uu____68427) with
                           | ((int_to_t1,x),(uu____68446,y)) ->
                               let uu____68456 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____68456)
                     in
                  (uu____68401, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____68491  ->
                            fun uu____68492  ->
                              match (uu____68491, uu____68492) with
                              | ((int_to_t1,x),(uu____68511,y)) ->
                                  let uu____68521 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____68521)),
                    uu____68408)
                   in
                let uu____68522 =
                  let uu____68554 =
                    let uu____68584 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____68591 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____68609  ->
                           fun uu____68610  ->
                             match (uu____68609, uu____68610) with
                             | ((int_to_t1,x),(uu____68629,y)) ->
                                 let uu____68639 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____68639)
                       in
                    (uu____68584, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____68674  ->
                              fun uu____68675  ->
                                match (uu____68674, uu____68675) with
                                | ((int_to_t1,x),(uu____68694,y)) ->
                                    let uu____68704 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____68704)),
                      uu____68591)
                     in
                  let uu____68705 =
                    let uu____68737 =
                      let uu____68767 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____68774 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____68788  ->
                             match uu____68788 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____68767, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____68825  ->
                                match uu____68825 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____68774)
                       in
                    [uu____68737]  in
                  uu____68554 :: uu____68705  in
                uu____68371 :: uu____68522  in
              uu____68188 :: uu____68339))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____69078 =
                let uu____69108 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____69115 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69133  ->
                       fun uu____69134  ->
                         match (uu____69133, uu____69134) with
                         | ((int_to_t1,x),(uu____69153,y)) ->
                             let uu____69163 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69163)
                   in
                (uu____69108, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69198  ->
                          fun uu____69199  ->
                            match (uu____69198, uu____69199) with
                            | ((int_to_t1,x),(uu____69218,y)) ->
                                let uu____69228 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69228)),
                  uu____69115)
                 in
              let uu____69229 =
                let uu____69261 =
                  let uu____69291 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____69298 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____69316  ->
                         fun uu____69317  ->
                           match (uu____69316, uu____69317) with
                           | ((int_to_t1,x),(uu____69336,y)) ->
                               let uu____69346 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____69346)
                     in
                  (uu____69291, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____69381  ->
                            fun uu____69382  ->
                              match (uu____69381, uu____69382) with
                              | ((int_to_t1,x),(uu____69401,y)) ->
                                  let uu____69411 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____69411)),
                    uu____69298)
                   in
                [uu____69261]  in
              uu____69078 :: uu____69229))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____69517 ->
          let uu____69519 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____69519
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____69623 =
                let uu____69653 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____69660 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69678  ->
                       fun uu____69679  ->
                         match (uu____69678, uu____69679) with
                         | ((int_to_t1,x),(uu____69698,y)) ->
                             let uu____69708 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69708)
                   in
                (uu____69653, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69743  ->
                          fun uu____69744  ->
                            match (uu____69743, uu____69744) with
                            | ((int_to_t1,x),(uu____69763,y)) ->
                                let uu____69773 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69773)),
                  uu____69660)
                 in
              let uu____69774 =
                let uu____69806 =
                  let uu____69836 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____69843 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____69861  ->
                         fun uu____69862  ->
                           match (uu____69861, uu____69862) with
                           | ((int_to_t1,x),(uu____69881,y)) ->
                               let uu____69891 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____69891)
                     in
                  (uu____69836, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____69926  ->
                            fun uu____69927  ->
                              match (uu____69926, uu____69927) with
                              | ((int_to_t1,x),(uu____69946,y)) ->
                                  let uu____69956 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____69956)),
                    uu____69843)
                   in
                let uu____69957 =
                  let uu____69989 =
                    let uu____70019 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____70026 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____70044  ->
                           fun uu____70045  ->
                             match (uu____70044, uu____70045) with
                             | ((int_to_t1,x),(uu____70064,y)) ->
                                 let uu____70074 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70074)
                       in
                    (uu____70019, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____70109  ->
                              fun uu____70110  ->
                                match (uu____70109, uu____70110) with
                                | ((int_to_t1,x),(uu____70129,y)) ->
                                    let uu____70139 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____70139)),
                      uu____70026)
                     in
                  let uu____70140 =
                    let uu____70172 =
                      let uu____70202 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____70209 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____70224  ->
                             match uu____70224 with
                             | (int_to_t1,x) ->
                                 let uu____70231 =
                                   let uu____70232 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____70233 = mask m  in
                                   FStar_BigInt.logand_big_int uu____70232
                                     uu____70233
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70231)
                         in
                      (uu____70202, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____70265  ->
                                match uu____70265 with
                                | (int_to_t1,x) ->
                                    let uu____70272 =
                                      let uu____70273 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____70274 = mask m  in
                                      FStar_BigInt.logand_big_int uu____70273
                                        uu____70274
                                       in
                                    int_as_bounded1 r int_to_t1 uu____70272)),
                        uu____70209)
                       in
                    let uu____70275 =
                      let uu____70307 =
                        let uu____70337 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____70344 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____70362  ->
                               fun uu____70363  ->
                                 match (uu____70362, uu____70363) with
                                 | ((int_to_t1,x),(uu____70382,y)) ->
                                     let uu____70392 =
                                       let uu____70393 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____70394 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____70393 uu____70394
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____70392)
                           in
                        (uu____70337, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____70429  ->
                                  fun uu____70430  ->
                                    match (uu____70429, uu____70430) with
                                    | ((int_to_t1,x),(uu____70449,y)) ->
                                        let uu____70459 =
                                          let uu____70460 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____70461 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____70460 uu____70461
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____70459)), uu____70344)
                         in
                      let uu____70462 =
                        let uu____70494 =
                          let uu____70524 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____70531 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____70549  ->
                                 fun uu____70550  ->
                                   match (uu____70549, uu____70550) with
                                   | ((int_to_t1,x),(uu____70569,y)) ->
                                       let uu____70579 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____70579)
                             in
                          (uu____70524, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____70614  ->
                                    fun uu____70615  ->
                                      match (uu____70614, uu____70615) with
                                      | ((int_to_t1,x),(uu____70634,y)) ->
                                          let uu____70644 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____70644)), uu____70531)
                           in
                        [uu____70494]  in
                      uu____70307 :: uu____70462  in
                    uu____70172 :: uu____70275  in
                  uu____69989 :: uu____70140  in
                uu____69806 :: uu____69957  in
              uu____69623 :: uu____69774))
       in
    FStar_List.append add_sub_mul_v
      (FStar_List.append div_mod_unsigned bitwise)
     in
  let strong_steps =
    FStar_List.map (as_primitive_step true)
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  let weak_steps = FStar_List.map (as_primitive_step false) weak_ops  in
  FStar_All.pipe_left prim_from_list
    (FStar_List.append strong_steps weak_steps)
  
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop_eq21 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____71036)::(a1,uu____71038)::(a2,uu____71040)::[] ->
        let uu____71097 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____71097 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1406_71101 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1406_71101.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1406_71101.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1409_71103 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1409_71103.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1409_71103.FStar_Syntax_Syntax.vars)
                })
         | uu____71104 -> FStar_Pervasives_Native.None)
    | uu____71105 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____71135)::(t2,uu____71137)::(a1,uu____71139)::(a2,uu____71141)::[]
        ->
        let uu____71214 =
          let uu____71215 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____71216 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____71215 uu____71216  in
        (match uu____71214 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1432_71220 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1432_71220.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1432_71220.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1435_71222 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1435_71222.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1435_71222.FStar_Syntax_Syntax.vars)
                })
         | uu____71223 -> FStar_Pervasives_Native.None)
    | uu____71224 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      univ_arity = (Prims.parse_int "1");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop_eq21;
      interpretation_nbe =
        (fun _cb  -> FStar_TypeChecker_NBETerm.interp_prop_eq2)
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      univ_arity = (Prims.parse_int "2");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop_eq31;
      interpretation_nbe =
        (fun _cb  -> FStar_TypeChecker_NBETerm.interp_prop_eq3)
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (primop_time_map : Prims.int FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let (primop_time_reset : unit -> unit) =
  fun uu____71255  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____71272 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____71272 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____71301 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____71301 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____71312  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____71383  ->
           fun uu____71384  ->
             match (uu____71383, uu____71384) with
             | ((uu____71410,t1),(uu____71412,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____71446  ->
         fun rest  ->
           match uu____71446 with
           | (nm,ms) ->
               let uu____71462 =
                 let uu____71464 =
                   let uu____71466 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____71466  in
                 FStar_Util.format2 "%sms --- %s\n" uu____71464 nm  in
               FStar_String.op_Hat uu____71462 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____71497 =
      let uu____71500 = FStar_ST.op_Bang plugins  in p :: uu____71500  in
    FStar_ST.op_Colon_Equals plugins uu____71497  in
  let retrieve uu____71556 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____71609  ->
    let uu____71610 = FStar_Options.no_plugins ()  in
    if uu____71610 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____71631 = FStar_Options.use_nbe ()  in
    if uu____71631
    then
      let uu___1478_71634 = s  in
      {
        beta = (uu___1478_71634.beta);
        iota = (uu___1478_71634.iota);
        zeta = (uu___1478_71634.zeta);
        weak = (uu___1478_71634.weak);
        hnf = (uu___1478_71634.hnf);
        primops = (uu___1478_71634.primops);
        do_not_unfold_pure_lets = (uu___1478_71634.do_not_unfold_pure_lets);
        unfold_until = (uu___1478_71634.unfold_until);
        unfold_only = (uu___1478_71634.unfold_only);
        unfold_fully = (uu___1478_71634.unfold_fully);
        unfold_attr = (uu___1478_71634.unfold_attr);
        unfold_tac = (uu___1478_71634.unfold_tac);
        pure_subterms_within_computations =
          (uu___1478_71634.pure_subterms_within_computations);
        simplify = (uu___1478_71634.simplify);
        erase_universes = (uu___1478_71634.erase_universes);
        allow_unbound_universes = (uu___1478_71634.allow_unbound_universes);
        reify_ = (uu___1478_71634.reify_);
        compress_uvars = (uu___1478_71634.compress_uvars);
        no_full_norm = (uu___1478_71634.no_full_norm);
        check_no_uvars = (uu___1478_71634.check_no_uvars);
        unmeta = (uu___1478_71634.unmeta);
        unascribe = (uu___1478_71634.unascribe);
        in_full_norm_request = (uu___1478_71634.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1478_71634.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1478_71634.for_extraction)
      }
    else s
  
let (config' :
  primitive_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  =
  fun psteps  ->
    fun s  ->
      fun e  ->
        let d =
          FStar_All.pipe_right s
            (FStar_List.collect
               (fun uu___531_71671  ->
                  match uu___531_71671 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____71675 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____71681 -> d  in
        let uu____71684 =
          let uu____71685 = to_fsteps s  in
          FStar_All.pipe_right uu____71685 add_nbe  in
        let uu____71686 =
          let uu____71687 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____71690 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____71693 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____71696 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____71699 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____71702 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____71705 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____71708 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____71711 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____71687;
            top = uu____71690;
            cfg = uu____71693;
            primop = uu____71696;
            unfolding = uu____71699;
            b380 = uu____71702;
            wpe = uu____71705;
            norm_delayed = uu____71708;
            print_normalized = uu____71711
          }  in
        let uu____71714 =
          let uu____71717 =
            let uu____71720 = retrieve_plugins ()  in
            FStar_List.append uu____71720 psteps  in
          add_steps built_in_primitive_steps uu____71717  in
        let uu____71723 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____71726 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____71726)
           in
        {
          steps = uu____71684;
          tcenv = e;
          debug = uu____71686;
          delta_level = d1;
          primitive_steps = uu____71714;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____71723;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 