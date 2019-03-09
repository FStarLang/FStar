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
          let uu____60251 =
            let uu____60253 = f1 x  in FStar_String.op_Hat uu____60253 ")"
             in
          FStar_String.op_Hat "Some (" uu____60251
       in
    let b = FStar_Util.string_of_bool  in
    let uu____60264 =
      let uu____60268 = FStar_All.pipe_right f.beta b  in
      let uu____60272 =
        let uu____60276 = FStar_All.pipe_right f.iota b  in
        let uu____60280 =
          let uu____60284 = FStar_All.pipe_right f.zeta b  in
          let uu____60288 =
            let uu____60292 = FStar_All.pipe_right f.weak b  in
            let uu____60296 =
              let uu____60300 = FStar_All.pipe_right f.hnf b  in
              let uu____60304 =
                let uu____60308 = FStar_All.pipe_right f.primops b  in
                let uu____60312 =
                  let uu____60316 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____60320 =
                    let uu____60324 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____60329 =
                      let uu____60333 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____60347 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____60347
                                  (FStar_String.concat ", ")))
                         in
                      let uu____60357 =
                        let uu____60361 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____60375 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____60375
                                    (FStar_String.concat ", ")))
                           in
                        let uu____60385 =
                          let uu____60389 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____60403 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____60403
                                      (FStar_String.concat ", ")))
                             in
                          let uu____60413 =
                            let uu____60417 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____60421 =
                              let uu____60425 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____60429 =
                                let uu____60433 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____60437 =
                                  let uu____60441 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____60445 =
                                    let uu____60449 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____60453 =
                                      let uu____60457 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____60461 =
                                        let uu____60465 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____60469 =
                                          let uu____60473 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____60477 =
                                            let uu____60481 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____60485 =
                                              let uu____60489 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____60493 =
                                                let uu____60497 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____60501 =
                                                  let uu____60505 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____60509 =
                                                    let uu____60513 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____60513]  in
                                                  uu____60505 :: uu____60509
                                                   in
                                                uu____60497 :: uu____60501
                                                 in
                                              uu____60489 :: uu____60493  in
                                            uu____60481 :: uu____60485  in
                                          uu____60473 :: uu____60477  in
                                        uu____60465 :: uu____60469  in
                                      uu____60457 :: uu____60461  in
                                    uu____60449 :: uu____60453  in
                                  uu____60441 :: uu____60445  in
                                uu____60433 :: uu____60437  in
                              uu____60425 :: uu____60429  in
                            uu____60417 :: uu____60421  in
                          uu____60389 :: uu____60413  in
                        uu____60361 :: uu____60385  in
                      uu____60333 :: uu____60357  in
                    uu____60324 :: uu____60329  in
                  uu____60316 :: uu____60320  in
                uu____60308 :: uu____60312  in
              uu____60300 :: uu____60304  in
            uu____60292 :: uu____60296  in
          uu____60284 :: uu____60288  in
        uu____60276 :: uu____60280  in
      uu____60268 :: uu____60272  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____60264
  
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
          let uu___625_60583 = fs  in
          {
            beta = true;
            iota = (uu___625_60583.iota);
            zeta = (uu___625_60583.zeta);
            weak = (uu___625_60583.weak);
            hnf = (uu___625_60583.hnf);
            primops = (uu___625_60583.primops);
            do_not_unfold_pure_lets =
              (uu___625_60583.do_not_unfold_pure_lets);
            unfold_until = (uu___625_60583.unfold_until);
            unfold_only = (uu___625_60583.unfold_only);
            unfold_fully = (uu___625_60583.unfold_fully);
            unfold_attr = (uu___625_60583.unfold_attr);
            unfold_tac = (uu___625_60583.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_60583.pure_subterms_within_computations);
            simplify = (uu___625_60583.simplify);
            erase_universes = (uu___625_60583.erase_universes);
            allow_unbound_universes =
              (uu___625_60583.allow_unbound_universes);
            reify_ = (uu___625_60583.reify_);
            compress_uvars = (uu___625_60583.compress_uvars);
            no_full_norm = (uu___625_60583.no_full_norm);
            check_no_uvars = (uu___625_60583.check_no_uvars);
            unmeta = (uu___625_60583.unmeta);
            unascribe = (uu___625_60583.unascribe);
            in_full_norm_request = (uu___625_60583.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_60583.weakly_reduce_scrutinee);
            nbe_step = (uu___625_60583.nbe_step);
            for_extraction = (uu___625_60583.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_60585 = fs  in
          {
            beta = (uu___628_60585.beta);
            iota = true;
            zeta = (uu___628_60585.zeta);
            weak = (uu___628_60585.weak);
            hnf = (uu___628_60585.hnf);
            primops = (uu___628_60585.primops);
            do_not_unfold_pure_lets =
              (uu___628_60585.do_not_unfold_pure_lets);
            unfold_until = (uu___628_60585.unfold_until);
            unfold_only = (uu___628_60585.unfold_only);
            unfold_fully = (uu___628_60585.unfold_fully);
            unfold_attr = (uu___628_60585.unfold_attr);
            unfold_tac = (uu___628_60585.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_60585.pure_subterms_within_computations);
            simplify = (uu___628_60585.simplify);
            erase_universes = (uu___628_60585.erase_universes);
            allow_unbound_universes =
              (uu___628_60585.allow_unbound_universes);
            reify_ = (uu___628_60585.reify_);
            compress_uvars = (uu___628_60585.compress_uvars);
            no_full_norm = (uu___628_60585.no_full_norm);
            check_no_uvars = (uu___628_60585.check_no_uvars);
            unmeta = (uu___628_60585.unmeta);
            unascribe = (uu___628_60585.unascribe);
            in_full_norm_request = (uu___628_60585.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_60585.weakly_reduce_scrutinee);
            nbe_step = (uu___628_60585.nbe_step);
            for_extraction = (uu___628_60585.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_60587 = fs  in
          {
            beta = (uu___631_60587.beta);
            iota = (uu___631_60587.iota);
            zeta = true;
            weak = (uu___631_60587.weak);
            hnf = (uu___631_60587.hnf);
            primops = (uu___631_60587.primops);
            do_not_unfold_pure_lets =
              (uu___631_60587.do_not_unfold_pure_lets);
            unfold_until = (uu___631_60587.unfold_until);
            unfold_only = (uu___631_60587.unfold_only);
            unfold_fully = (uu___631_60587.unfold_fully);
            unfold_attr = (uu___631_60587.unfold_attr);
            unfold_tac = (uu___631_60587.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_60587.pure_subterms_within_computations);
            simplify = (uu___631_60587.simplify);
            erase_universes = (uu___631_60587.erase_universes);
            allow_unbound_universes =
              (uu___631_60587.allow_unbound_universes);
            reify_ = (uu___631_60587.reify_);
            compress_uvars = (uu___631_60587.compress_uvars);
            no_full_norm = (uu___631_60587.no_full_norm);
            check_no_uvars = (uu___631_60587.check_no_uvars);
            unmeta = (uu___631_60587.unmeta);
            unascribe = (uu___631_60587.unascribe);
            in_full_norm_request = (uu___631_60587.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_60587.weakly_reduce_scrutinee);
            nbe_step = (uu___631_60587.nbe_step);
            for_extraction = (uu___631_60587.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_60589 = fs  in
          {
            beta = false;
            iota = (uu___635_60589.iota);
            zeta = (uu___635_60589.zeta);
            weak = (uu___635_60589.weak);
            hnf = (uu___635_60589.hnf);
            primops = (uu___635_60589.primops);
            do_not_unfold_pure_lets =
              (uu___635_60589.do_not_unfold_pure_lets);
            unfold_until = (uu___635_60589.unfold_until);
            unfold_only = (uu___635_60589.unfold_only);
            unfold_fully = (uu___635_60589.unfold_fully);
            unfold_attr = (uu___635_60589.unfold_attr);
            unfold_tac = (uu___635_60589.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_60589.pure_subterms_within_computations);
            simplify = (uu___635_60589.simplify);
            erase_universes = (uu___635_60589.erase_universes);
            allow_unbound_universes =
              (uu___635_60589.allow_unbound_universes);
            reify_ = (uu___635_60589.reify_);
            compress_uvars = (uu___635_60589.compress_uvars);
            no_full_norm = (uu___635_60589.no_full_norm);
            check_no_uvars = (uu___635_60589.check_no_uvars);
            unmeta = (uu___635_60589.unmeta);
            unascribe = (uu___635_60589.unascribe);
            in_full_norm_request = (uu___635_60589.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_60589.weakly_reduce_scrutinee);
            nbe_step = (uu___635_60589.nbe_step);
            for_extraction = (uu___635_60589.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_60591 = fs  in
          {
            beta = (uu___639_60591.beta);
            iota = false;
            zeta = (uu___639_60591.zeta);
            weak = (uu___639_60591.weak);
            hnf = (uu___639_60591.hnf);
            primops = (uu___639_60591.primops);
            do_not_unfold_pure_lets =
              (uu___639_60591.do_not_unfold_pure_lets);
            unfold_until = (uu___639_60591.unfold_until);
            unfold_only = (uu___639_60591.unfold_only);
            unfold_fully = (uu___639_60591.unfold_fully);
            unfold_attr = (uu___639_60591.unfold_attr);
            unfold_tac = (uu___639_60591.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_60591.pure_subterms_within_computations);
            simplify = (uu___639_60591.simplify);
            erase_universes = (uu___639_60591.erase_universes);
            allow_unbound_universes =
              (uu___639_60591.allow_unbound_universes);
            reify_ = (uu___639_60591.reify_);
            compress_uvars = (uu___639_60591.compress_uvars);
            no_full_norm = (uu___639_60591.no_full_norm);
            check_no_uvars = (uu___639_60591.check_no_uvars);
            unmeta = (uu___639_60591.unmeta);
            unascribe = (uu___639_60591.unascribe);
            in_full_norm_request = (uu___639_60591.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_60591.weakly_reduce_scrutinee);
            nbe_step = (uu___639_60591.nbe_step);
            for_extraction = (uu___639_60591.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_60593 = fs  in
          {
            beta = (uu___643_60593.beta);
            iota = (uu___643_60593.iota);
            zeta = false;
            weak = (uu___643_60593.weak);
            hnf = (uu___643_60593.hnf);
            primops = (uu___643_60593.primops);
            do_not_unfold_pure_lets =
              (uu___643_60593.do_not_unfold_pure_lets);
            unfold_until = (uu___643_60593.unfold_until);
            unfold_only = (uu___643_60593.unfold_only);
            unfold_fully = (uu___643_60593.unfold_fully);
            unfold_attr = (uu___643_60593.unfold_attr);
            unfold_tac = (uu___643_60593.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_60593.pure_subterms_within_computations);
            simplify = (uu___643_60593.simplify);
            erase_universes = (uu___643_60593.erase_universes);
            allow_unbound_universes =
              (uu___643_60593.allow_unbound_universes);
            reify_ = (uu___643_60593.reify_);
            compress_uvars = (uu___643_60593.compress_uvars);
            no_full_norm = (uu___643_60593.no_full_norm);
            check_no_uvars = (uu___643_60593.check_no_uvars);
            unmeta = (uu___643_60593.unmeta);
            unascribe = (uu___643_60593.unascribe);
            in_full_norm_request = (uu___643_60593.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_60593.weakly_reduce_scrutinee);
            nbe_step = (uu___643_60593.nbe_step);
            for_extraction = (uu___643_60593.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____60595 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_60597 = fs  in
          {
            beta = (uu___648_60597.beta);
            iota = (uu___648_60597.iota);
            zeta = (uu___648_60597.zeta);
            weak = true;
            hnf = (uu___648_60597.hnf);
            primops = (uu___648_60597.primops);
            do_not_unfold_pure_lets =
              (uu___648_60597.do_not_unfold_pure_lets);
            unfold_until = (uu___648_60597.unfold_until);
            unfold_only = (uu___648_60597.unfold_only);
            unfold_fully = (uu___648_60597.unfold_fully);
            unfold_attr = (uu___648_60597.unfold_attr);
            unfold_tac = (uu___648_60597.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_60597.pure_subterms_within_computations);
            simplify = (uu___648_60597.simplify);
            erase_universes = (uu___648_60597.erase_universes);
            allow_unbound_universes =
              (uu___648_60597.allow_unbound_universes);
            reify_ = (uu___648_60597.reify_);
            compress_uvars = (uu___648_60597.compress_uvars);
            no_full_norm = (uu___648_60597.no_full_norm);
            check_no_uvars = (uu___648_60597.check_no_uvars);
            unmeta = (uu___648_60597.unmeta);
            unascribe = (uu___648_60597.unascribe);
            in_full_norm_request = (uu___648_60597.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_60597.weakly_reduce_scrutinee);
            nbe_step = (uu___648_60597.nbe_step);
            for_extraction = (uu___648_60597.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_60599 = fs  in
          {
            beta = (uu___651_60599.beta);
            iota = (uu___651_60599.iota);
            zeta = (uu___651_60599.zeta);
            weak = (uu___651_60599.weak);
            hnf = true;
            primops = (uu___651_60599.primops);
            do_not_unfold_pure_lets =
              (uu___651_60599.do_not_unfold_pure_lets);
            unfold_until = (uu___651_60599.unfold_until);
            unfold_only = (uu___651_60599.unfold_only);
            unfold_fully = (uu___651_60599.unfold_fully);
            unfold_attr = (uu___651_60599.unfold_attr);
            unfold_tac = (uu___651_60599.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_60599.pure_subterms_within_computations);
            simplify = (uu___651_60599.simplify);
            erase_universes = (uu___651_60599.erase_universes);
            allow_unbound_universes =
              (uu___651_60599.allow_unbound_universes);
            reify_ = (uu___651_60599.reify_);
            compress_uvars = (uu___651_60599.compress_uvars);
            no_full_norm = (uu___651_60599.no_full_norm);
            check_no_uvars = (uu___651_60599.check_no_uvars);
            unmeta = (uu___651_60599.unmeta);
            unascribe = (uu___651_60599.unascribe);
            in_full_norm_request = (uu___651_60599.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_60599.weakly_reduce_scrutinee);
            nbe_step = (uu___651_60599.nbe_step);
            for_extraction = (uu___651_60599.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_60601 = fs  in
          {
            beta = (uu___654_60601.beta);
            iota = (uu___654_60601.iota);
            zeta = (uu___654_60601.zeta);
            weak = (uu___654_60601.weak);
            hnf = (uu___654_60601.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_60601.do_not_unfold_pure_lets);
            unfold_until = (uu___654_60601.unfold_until);
            unfold_only = (uu___654_60601.unfold_only);
            unfold_fully = (uu___654_60601.unfold_fully);
            unfold_attr = (uu___654_60601.unfold_attr);
            unfold_tac = (uu___654_60601.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_60601.pure_subterms_within_computations);
            simplify = (uu___654_60601.simplify);
            erase_universes = (uu___654_60601.erase_universes);
            allow_unbound_universes =
              (uu___654_60601.allow_unbound_universes);
            reify_ = (uu___654_60601.reify_);
            compress_uvars = (uu___654_60601.compress_uvars);
            no_full_norm = (uu___654_60601.no_full_norm);
            check_no_uvars = (uu___654_60601.check_no_uvars);
            unmeta = (uu___654_60601.unmeta);
            unascribe = (uu___654_60601.unascribe);
            in_full_norm_request = (uu___654_60601.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_60601.weakly_reduce_scrutinee);
            nbe_step = (uu___654_60601.nbe_step);
            for_extraction = (uu___654_60601.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_60603 = fs  in
          {
            beta = (uu___659_60603.beta);
            iota = (uu___659_60603.iota);
            zeta = (uu___659_60603.zeta);
            weak = (uu___659_60603.weak);
            hnf = (uu___659_60603.hnf);
            primops = (uu___659_60603.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_60603.unfold_until);
            unfold_only = (uu___659_60603.unfold_only);
            unfold_fully = (uu___659_60603.unfold_fully);
            unfold_attr = (uu___659_60603.unfold_attr);
            unfold_tac = (uu___659_60603.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_60603.pure_subterms_within_computations);
            simplify = (uu___659_60603.simplify);
            erase_universes = (uu___659_60603.erase_universes);
            allow_unbound_universes =
              (uu___659_60603.allow_unbound_universes);
            reify_ = (uu___659_60603.reify_);
            compress_uvars = (uu___659_60603.compress_uvars);
            no_full_norm = (uu___659_60603.no_full_norm);
            check_no_uvars = (uu___659_60603.check_no_uvars);
            unmeta = (uu___659_60603.unmeta);
            unascribe = (uu___659_60603.unascribe);
            in_full_norm_request = (uu___659_60603.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_60603.weakly_reduce_scrutinee);
            nbe_step = (uu___659_60603.nbe_step);
            for_extraction = (uu___659_60603.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_60606 = fs  in
          {
            beta = (uu___663_60606.beta);
            iota = (uu___663_60606.iota);
            zeta = (uu___663_60606.zeta);
            weak = (uu___663_60606.weak);
            hnf = (uu___663_60606.hnf);
            primops = (uu___663_60606.primops);
            do_not_unfold_pure_lets =
              (uu___663_60606.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_60606.unfold_only);
            unfold_fully = (uu___663_60606.unfold_fully);
            unfold_attr = (uu___663_60606.unfold_attr);
            unfold_tac = (uu___663_60606.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_60606.pure_subterms_within_computations);
            simplify = (uu___663_60606.simplify);
            erase_universes = (uu___663_60606.erase_universes);
            allow_unbound_universes =
              (uu___663_60606.allow_unbound_universes);
            reify_ = (uu___663_60606.reify_);
            compress_uvars = (uu___663_60606.compress_uvars);
            no_full_norm = (uu___663_60606.no_full_norm);
            check_no_uvars = (uu___663_60606.check_no_uvars);
            unmeta = (uu___663_60606.unmeta);
            unascribe = (uu___663_60606.unascribe);
            in_full_norm_request = (uu___663_60606.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_60606.weakly_reduce_scrutinee);
            nbe_step = (uu___663_60606.nbe_step);
            for_extraction = (uu___663_60606.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_60610 = fs  in
          {
            beta = (uu___667_60610.beta);
            iota = (uu___667_60610.iota);
            zeta = (uu___667_60610.zeta);
            weak = (uu___667_60610.weak);
            hnf = (uu___667_60610.hnf);
            primops = (uu___667_60610.primops);
            do_not_unfold_pure_lets =
              (uu___667_60610.do_not_unfold_pure_lets);
            unfold_until = (uu___667_60610.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_60610.unfold_fully);
            unfold_attr = (uu___667_60610.unfold_attr);
            unfold_tac = (uu___667_60610.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_60610.pure_subterms_within_computations);
            simplify = (uu___667_60610.simplify);
            erase_universes = (uu___667_60610.erase_universes);
            allow_unbound_universes =
              (uu___667_60610.allow_unbound_universes);
            reify_ = (uu___667_60610.reify_);
            compress_uvars = (uu___667_60610.compress_uvars);
            no_full_norm = (uu___667_60610.no_full_norm);
            check_no_uvars = (uu___667_60610.check_no_uvars);
            unmeta = (uu___667_60610.unmeta);
            unascribe = (uu___667_60610.unascribe);
            in_full_norm_request = (uu___667_60610.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_60610.weakly_reduce_scrutinee);
            nbe_step = (uu___667_60610.nbe_step);
            for_extraction = (uu___667_60610.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_60616 = fs  in
          {
            beta = (uu___671_60616.beta);
            iota = (uu___671_60616.iota);
            zeta = (uu___671_60616.zeta);
            weak = (uu___671_60616.weak);
            hnf = (uu___671_60616.hnf);
            primops = (uu___671_60616.primops);
            do_not_unfold_pure_lets =
              (uu___671_60616.do_not_unfold_pure_lets);
            unfold_until = (uu___671_60616.unfold_until);
            unfold_only = (uu___671_60616.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_60616.unfold_attr);
            unfold_tac = (uu___671_60616.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_60616.pure_subterms_within_computations);
            simplify = (uu___671_60616.simplify);
            erase_universes = (uu___671_60616.erase_universes);
            allow_unbound_universes =
              (uu___671_60616.allow_unbound_universes);
            reify_ = (uu___671_60616.reify_);
            compress_uvars = (uu___671_60616.compress_uvars);
            no_full_norm = (uu___671_60616.no_full_norm);
            check_no_uvars = (uu___671_60616.check_no_uvars);
            unmeta = (uu___671_60616.unmeta);
            unascribe = (uu___671_60616.unascribe);
            in_full_norm_request = (uu___671_60616.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_60616.weakly_reduce_scrutinee);
            nbe_step = (uu___671_60616.nbe_step);
            for_extraction = (uu___671_60616.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_60622 = fs  in
          {
            beta = (uu___675_60622.beta);
            iota = (uu___675_60622.iota);
            zeta = (uu___675_60622.zeta);
            weak = (uu___675_60622.weak);
            hnf = (uu___675_60622.hnf);
            primops = (uu___675_60622.primops);
            do_not_unfold_pure_lets =
              (uu___675_60622.do_not_unfold_pure_lets);
            unfold_until = (uu___675_60622.unfold_until);
            unfold_only = (uu___675_60622.unfold_only);
            unfold_fully = (uu___675_60622.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_60622.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_60622.pure_subterms_within_computations);
            simplify = (uu___675_60622.simplify);
            erase_universes = (uu___675_60622.erase_universes);
            allow_unbound_universes =
              (uu___675_60622.allow_unbound_universes);
            reify_ = (uu___675_60622.reify_);
            compress_uvars = (uu___675_60622.compress_uvars);
            no_full_norm = (uu___675_60622.no_full_norm);
            check_no_uvars = (uu___675_60622.check_no_uvars);
            unmeta = (uu___675_60622.unmeta);
            unascribe = (uu___675_60622.unascribe);
            in_full_norm_request = (uu___675_60622.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_60622.weakly_reduce_scrutinee);
            nbe_step = (uu___675_60622.nbe_step);
            for_extraction = (uu___675_60622.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_60625 = fs  in
          {
            beta = (uu___678_60625.beta);
            iota = (uu___678_60625.iota);
            zeta = (uu___678_60625.zeta);
            weak = (uu___678_60625.weak);
            hnf = (uu___678_60625.hnf);
            primops = (uu___678_60625.primops);
            do_not_unfold_pure_lets =
              (uu___678_60625.do_not_unfold_pure_lets);
            unfold_until = (uu___678_60625.unfold_until);
            unfold_only = (uu___678_60625.unfold_only);
            unfold_fully = (uu___678_60625.unfold_fully);
            unfold_attr = (uu___678_60625.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_60625.pure_subterms_within_computations);
            simplify = (uu___678_60625.simplify);
            erase_universes = (uu___678_60625.erase_universes);
            allow_unbound_universes =
              (uu___678_60625.allow_unbound_universes);
            reify_ = (uu___678_60625.reify_);
            compress_uvars = (uu___678_60625.compress_uvars);
            no_full_norm = (uu___678_60625.no_full_norm);
            check_no_uvars = (uu___678_60625.check_no_uvars);
            unmeta = (uu___678_60625.unmeta);
            unascribe = (uu___678_60625.unascribe);
            in_full_norm_request = (uu___678_60625.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_60625.weakly_reduce_scrutinee);
            nbe_step = (uu___678_60625.nbe_step);
            for_extraction = (uu___678_60625.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_60627 = fs  in
          {
            beta = (uu___681_60627.beta);
            iota = (uu___681_60627.iota);
            zeta = (uu___681_60627.zeta);
            weak = (uu___681_60627.weak);
            hnf = (uu___681_60627.hnf);
            primops = (uu___681_60627.primops);
            do_not_unfold_pure_lets =
              (uu___681_60627.do_not_unfold_pure_lets);
            unfold_until = (uu___681_60627.unfold_until);
            unfold_only = (uu___681_60627.unfold_only);
            unfold_fully = (uu___681_60627.unfold_fully);
            unfold_attr = (uu___681_60627.unfold_attr);
            unfold_tac = (uu___681_60627.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_60627.simplify);
            erase_universes = (uu___681_60627.erase_universes);
            allow_unbound_universes =
              (uu___681_60627.allow_unbound_universes);
            reify_ = (uu___681_60627.reify_);
            compress_uvars = (uu___681_60627.compress_uvars);
            no_full_norm = (uu___681_60627.no_full_norm);
            check_no_uvars = (uu___681_60627.check_no_uvars);
            unmeta = (uu___681_60627.unmeta);
            unascribe = (uu___681_60627.unascribe);
            in_full_norm_request = (uu___681_60627.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_60627.weakly_reduce_scrutinee);
            nbe_step = (uu___681_60627.nbe_step);
            for_extraction = (uu___681_60627.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_60629 = fs  in
          {
            beta = (uu___684_60629.beta);
            iota = (uu___684_60629.iota);
            zeta = (uu___684_60629.zeta);
            weak = (uu___684_60629.weak);
            hnf = (uu___684_60629.hnf);
            primops = (uu___684_60629.primops);
            do_not_unfold_pure_lets =
              (uu___684_60629.do_not_unfold_pure_lets);
            unfold_until = (uu___684_60629.unfold_until);
            unfold_only = (uu___684_60629.unfold_only);
            unfold_fully = (uu___684_60629.unfold_fully);
            unfold_attr = (uu___684_60629.unfold_attr);
            unfold_tac = (uu___684_60629.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_60629.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_60629.erase_universes);
            allow_unbound_universes =
              (uu___684_60629.allow_unbound_universes);
            reify_ = (uu___684_60629.reify_);
            compress_uvars = (uu___684_60629.compress_uvars);
            no_full_norm = (uu___684_60629.no_full_norm);
            check_no_uvars = (uu___684_60629.check_no_uvars);
            unmeta = (uu___684_60629.unmeta);
            unascribe = (uu___684_60629.unascribe);
            in_full_norm_request = (uu___684_60629.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_60629.weakly_reduce_scrutinee);
            nbe_step = (uu___684_60629.nbe_step);
            for_extraction = (uu___684_60629.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_60631 = fs  in
          {
            beta = (uu___687_60631.beta);
            iota = (uu___687_60631.iota);
            zeta = (uu___687_60631.zeta);
            weak = (uu___687_60631.weak);
            hnf = (uu___687_60631.hnf);
            primops = (uu___687_60631.primops);
            do_not_unfold_pure_lets =
              (uu___687_60631.do_not_unfold_pure_lets);
            unfold_until = (uu___687_60631.unfold_until);
            unfold_only = (uu___687_60631.unfold_only);
            unfold_fully = (uu___687_60631.unfold_fully);
            unfold_attr = (uu___687_60631.unfold_attr);
            unfold_tac = (uu___687_60631.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_60631.pure_subterms_within_computations);
            simplify = (uu___687_60631.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_60631.allow_unbound_universes);
            reify_ = (uu___687_60631.reify_);
            compress_uvars = (uu___687_60631.compress_uvars);
            no_full_norm = (uu___687_60631.no_full_norm);
            check_no_uvars = (uu___687_60631.check_no_uvars);
            unmeta = (uu___687_60631.unmeta);
            unascribe = (uu___687_60631.unascribe);
            in_full_norm_request = (uu___687_60631.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_60631.weakly_reduce_scrutinee);
            nbe_step = (uu___687_60631.nbe_step);
            for_extraction = (uu___687_60631.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_60633 = fs  in
          {
            beta = (uu___690_60633.beta);
            iota = (uu___690_60633.iota);
            zeta = (uu___690_60633.zeta);
            weak = (uu___690_60633.weak);
            hnf = (uu___690_60633.hnf);
            primops = (uu___690_60633.primops);
            do_not_unfold_pure_lets =
              (uu___690_60633.do_not_unfold_pure_lets);
            unfold_until = (uu___690_60633.unfold_until);
            unfold_only = (uu___690_60633.unfold_only);
            unfold_fully = (uu___690_60633.unfold_fully);
            unfold_attr = (uu___690_60633.unfold_attr);
            unfold_tac = (uu___690_60633.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_60633.pure_subterms_within_computations);
            simplify = (uu___690_60633.simplify);
            erase_universes = (uu___690_60633.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_60633.reify_);
            compress_uvars = (uu___690_60633.compress_uvars);
            no_full_norm = (uu___690_60633.no_full_norm);
            check_no_uvars = (uu___690_60633.check_no_uvars);
            unmeta = (uu___690_60633.unmeta);
            unascribe = (uu___690_60633.unascribe);
            in_full_norm_request = (uu___690_60633.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_60633.weakly_reduce_scrutinee);
            nbe_step = (uu___690_60633.nbe_step);
            for_extraction = (uu___690_60633.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_60635 = fs  in
          {
            beta = (uu___693_60635.beta);
            iota = (uu___693_60635.iota);
            zeta = (uu___693_60635.zeta);
            weak = (uu___693_60635.weak);
            hnf = (uu___693_60635.hnf);
            primops = (uu___693_60635.primops);
            do_not_unfold_pure_lets =
              (uu___693_60635.do_not_unfold_pure_lets);
            unfold_until = (uu___693_60635.unfold_until);
            unfold_only = (uu___693_60635.unfold_only);
            unfold_fully = (uu___693_60635.unfold_fully);
            unfold_attr = (uu___693_60635.unfold_attr);
            unfold_tac = (uu___693_60635.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_60635.pure_subterms_within_computations);
            simplify = (uu___693_60635.simplify);
            erase_universes = (uu___693_60635.erase_universes);
            allow_unbound_universes =
              (uu___693_60635.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_60635.compress_uvars);
            no_full_norm = (uu___693_60635.no_full_norm);
            check_no_uvars = (uu___693_60635.check_no_uvars);
            unmeta = (uu___693_60635.unmeta);
            unascribe = (uu___693_60635.unascribe);
            in_full_norm_request = (uu___693_60635.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_60635.weakly_reduce_scrutinee);
            nbe_step = (uu___693_60635.nbe_step);
            for_extraction = (uu___693_60635.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_60637 = fs  in
          {
            beta = (uu___696_60637.beta);
            iota = (uu___696_60637.iota);
            zeta = (uu___696_60637.zeta);
            weak = (uu___696_60637.weak);
            hnf = (uu___696_60637.hnf);
            primops = (uu___696_60637.primops);
            do_not_unfold_pure_lets =
              (uu___696_60637.do_not_unfold_pure_lets);
            unfold_until = (uu___696_60637.unfold_until);
            unfold_only = (uu___696_60637.unfold_only);
            unfold_fully = (uu___696_60637.unfold_fully);
            unfold_attr = (uu___696_60637.unfold_attr);
            unfold_tac = (uu___696_60637.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_60637.pure_subterms_within_computations);
            simplify = (uu___696_60637.simplify);
            erase_universes = (uu___696_60637.erase_universes);
            allow_unbound_universes =
              (uu___696_60637.allow_unbound_universes);
            reify_ = (uu___696_60637.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_60637.no_full_norm);
            check_no_uvars = (uu___696_60637.check_no_uvars);
            unmeta = (uu___696_60637.unmeta);
            unascribe = (uu___696_60637.unascribe);
            in_full_norm_request = (uu___696_60637.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_60637.weakly_reduce_scrutinee);
            nbe_step = (uu___696_60637.nbe_step);
            for_extraction = (uu___696_60637.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_60639 = fs  in
          {
            beta = (uu___699_60639.beta);
            iota = (uu___699_60639.iota);
            zeta = (uu___699_60639.zeta);
            weak = (uu___699_60639.weak);
            hnf = (uu___699_60639.hnf);
            primops = (uu___699_60639.primops);
            do_not_unfold_pure_lets =
              (uu___699_60639.do_not_unfold_pure_lets);
            unfold_until = (uu___699_60639.unfold_until);
            unfold_only = (uu___699_60639.unfold_only);
            unfold_fully = (uu___699_60639.unfold_fully);
            unfold_attr = (uu___699_60639.unfold_attr);
            unfold_tac = (uu___699_60639.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_60639.pure_subterms_within_computations);
            simplify = (uu___699_60639.simplify);
            erase_universes = (uu___699_60639.erase_universes);
            allow_unbound_universes =
              (uu___699_60639.allow_unbound_universes);
            reify_ = (uu___699_60639.reify_);
            compress_uvars = (uu___699_60639.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_60639.check_no_uvars);
            unmeta = (uu___699_60639.unmeta);
            unascribe = (uu___699_60639.unascribe);
            in_full_norm_request = (uu___699_60639.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_60639.weakly_reduce_scrutinee);
            nbe_step = (uu___699_60639.nbe_step);
            for_extraction = (uu___699_60639.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_60641 = fs  in
          {
            beta = (uu___702_60641.beta);
            iota = (uu___702_60641.iota);
            zeta = (uu___702_60641.zeta);
            weak = (uu___702_60641.weak);
            hnf = (uu___702_60641.hnf);
            primops = (uu___702_60641.primops);
            do_not_unfold_pure_lets =
              (uu___702_60641.do_not_unfold_pure_lets);
            unfold_until = (uu___702_60641.unfold_until);
            unfold_only = (uu___702_60641.unfold_only);
            unfold_fully = (uu___702_60641.unfold_fully);
            unfold_attr = (uu___702_60641.unfold_attr);
            unfold_tac = (uu___702_60641.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_60641.pure_subterms_within_computations);
            simplify = (uu___702_60641.simplify);
            erase_universes = (uu___702_60641.erase_universes);
            allow_unbound_universes =
              (uu___702_60641.allow_unbound_universes);
            reify_ = (uu___702_60641.reify_);
            compress_uvars = (uu___702_60641.compress_uvars);
            no_full_norm = (uu___702_60641.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_60641.unmeta);
            unascribe = (uu___702_60641.unascribe);
            in_full_norm_request = (uu___702_60641.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_60641.weakly_reduce_scrutinee);
            nbe_step = (uu___702_60641.nbe_step);
            for_extraction = (uu___702_60641.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_60643 = fs  in
          {
            beta = (uu___705_60643.beta);
            iota = (uu___705_60643.iota);
            zeta = (uu___705_60643.zeta);
            weak = (uu___705_60643.weak);
            hnf = (uu___705_60643.hnf);
            primops = (uu___705_60643.primops);
            do_not_unfold_pure_lets =
              (uu___705_60643.do_not_unfold_pure_lets);
            unfold_until = (uu___705_60643.unfold_until);
            unfold_only = (uu___705_60643.unfold_only);
            unfold_fully = (uu___705_60643.unfold_fully);
            unfold_attr = (uu___705_60643.unfold_attr);
            unfold_tac = (uu___705_60643.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_60643.pure_subterms_within_computations);
            simplify = (uu___705_60643.simplify);
            erase_universes = (uu___705_60643.erase_universes);
            allow_unbound_universes =
              (uu___705_60643.allow_unbound_universes);
            reify_ = (uu___705_60643.reify_);
            compress_uvars = (uu___705_60643.compress_uvars);
            no_full_norm = (uu___705_60643.no_full_norm);
            check_no_uvars = (uu___705_60643.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_60643.unascribe);
            in_full_norm_request = (uu___705_60643.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_60643.weakly_reduce_scrutinee);
            nbe_step = (uu___705_60643.nbe_step);
            for_extraction = (uu___705_60643.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_60645 = fs  in
          {
            beta = (uu___708_60645.beta);
            iota = (uu___708_60645.iota);
            zeta = (uu___708_60645.zeta);
            weak = (uu___708_60645.weak);
            hnf = (uu___708_60645.hnf);
            primops = (uu___708_60645.primops);
            do_not_unfold_pure_lets =
              (uu___708_60645.do_not_unfold_pure_lets);
            unfold_until = (uu___708_60645.unfold_until);
            unfold_only = (uu___708_60645.unfold_only);
            unfold_fully = (uu___708_60645.unfold_fully);
            unfold_attr = (uu___708_60645.unfold_attr);
            unfold_tac = (uu___708_60645.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_60645.pure_subterms_within_computations);
            simplify = (uu___708_60645.simplify);
            erase_universes = (uu___708_60645.erase_universes);
            allow_unbound_universes =
              (uu___708_60645.allow_unbound_universes);
            reify_ = (uu___708_60645.reify_);
            compress_uvars = (uu___708_60645.compress_uvars);
            no_full_norm = (uu___708_60645.no_full_norm);
            check_no_uvars = (uu___708_60645.check_no_uvars);
            unmeta = (uu___708_60645.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_60645.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_60645.weakly_reduce_scrutinee);
            nbe_step = (uu___708_60645.nbe_step);
            for_extraction = (uu___708_60645.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_60647 = fs  in
          {
            beta = (uu___711_60647.beta);
            iota = (uu___711_60647.iota);
            zeta = (uu___711_60647.zeta);
            weak = (uu___711_60647.weak);
            hnf = (uu___711_60647.hnf);
            primops = (uu___711_60647.primops);
            do_not_unfold_pure_lets =
              (uu___711_60647.do_not_unfold_pure_lets);
            unfold_until = (uu___711_60647.unfold_until);
            unfold_only = (uu___711_60647.unfold_only);
            unfold_fully = (uu___711_60647.unfold_fully);
            unfold_attr = (uu___711_60647.unfold_attr);
            unfold_tac = (uu___711_60647.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_60647.pure_subterms_within_computations);
            simplify = (uu___711_60647.simplify);
            erase_universes = (uu___711_60647.erase_universes);
            allow_unbound_universes =
              (uu___711_60647.allow_unbound_universes);
            reify_ = (uu___711_60647.reify_);
            compress_uvars = (uu___711_60647.compress_uvars);
            no_full_norm = (uu___711_60647.no_full_norm);
            check_no_uvars = (uu___711_60647.check_no_uvars);
            unmeta = (uu___711_60647.unmeta);
            unascribe = (uu___711_60647.unascribe);
            in_full_norm_request = (uu___711_60647.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_60647.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_60647.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_60649 = fs  in
          {
            beta = (uu___714_60649.beta);
            iota = (uu___714_60649.iota);
            zeta = (uu___714_60649.zeta);
            weak = (uu___714_60649.weak);
            hnf = (uu___714_60649.hnf);
            primops = (uu___714_60649.primops);
            do_not_unfold_pure_lets =
              (uu___714_60649.do_not_unfold_pure_lets);
            unfold_until = (uu___714_60649.unfold_until);
            unfold_only = (uu___714_60649.unfold_only);
            unfold_fully = (uu___714_60649.unfold_fully);
            unfold_attr = (uu___714_60649.unfold_attr);
            unfold_tac = (uu___714_60649.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_60649.pure_subterms_within_computations);
            simplify = (uu___714_60649.simplify);
            erase_universes = (uu___714_60649.erase_universes);
            allow_unbound_universes =
              (uu___714_60649.allow_unbound_universes);
            reify_ = (uu___714_60649.reify_);
            compress_uvars = (uu___714_60649.compress_uvars);
            no_full_norm = (uu___714_60649.no_full_norm);
            check_no_uvars = (uu___714_60649.check_no_uvars);
            unmeta = (uu___714_60649.unmeta);
            unascribe = (uu___714_60649.unascribe);
            in_full_norm_request = (uu___714_60649.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_60649.weakly_reduce_scrutinee);
            nbe_step = (uu___714_60649.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____60707  -> [])
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
    let uu____61756 =
      let uu____61760 =
        let uu____61764 =
          let uu____61766 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____61766  in
        [uu____61764; "}"]  in
      "{" :: uu____61760  in
    FStar_String.concat "\n" uu____61756
  
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
             let uu____61814 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____61814 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____61830 = FStar_Util.psmap_empty ()  in add_steps uu____61830 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____61846 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____61846
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____61860 =
        let uu____61863 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____61863  in
      FStar_Util.is_some uu____61860
  
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
      let uu____61976 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____61976 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____62012 = FStar_Syntax_Embeddings.embed emb x  in
        uu____62012 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____62045 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____62045 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____62060 .
    'Auu____62060 ->
      FStar_Range.range -> 'Auu____62060 FStar_Syntax_Syntax.syntax
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
    let uu____62181 =
      let uu____62190 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____62190  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62181  in
  let arg_as_bounded_int1 uu____62220 =
    match uu____62220 with
    | (a,uu____62234) ->
        let uu____62245 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____62245 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____62289 =
               let uu____62304 =
                 let uu____62305 = FStar_Syntax_Subst.compress hd1  in
                 uu____62305.FStar_Syntax_Syntax.n  in
               (uu____62304, args)  in
             (match uu____62289 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____62326)::[]) when
                  let uu____62361 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____62361 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____62365 =
                    let uu____62366 = FStar_Syntax_Subst.compress arg1  in
                    uu____62366.FStar_Syntax_Syntax.n  in
                  (match uu____62365 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____62388 =
                         let uu____62393 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____62393)  in
                       FStar_Pervasives_Native.Some uu____62388
                   | uu____62398 -> FStar_Pervasives_Native.None)
              | uu____62403 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____62465 = f a  in FStar_Pervasives_Native.Some uu____62465
    | uu____62466 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____62522 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____62522
    | uu____62523 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____62590 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____62590  in
  let binary_op1 as_a f res n1 args =
    let uu____62672 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____62672  in
  let as_primitive_step is_strong uu____62727 =
    match uu____62727 with
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
           let uu____62835 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____62835)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____62877 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____62877)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____62918 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____62918)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____62971 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____62971)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____63024 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____63024)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____63177 =
          let uu____63186 = as_a a  in
          let uu____63189 = as_b b  in (uu____63186, uu____63189)  in
        (match uu____63177 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____63204 =
               let uu____63205 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____63205  in
             FStar_Pervasives_Native.Some uu____63204
         | uu____63206 -> FStar_Pervasives_Native.None)
    | uu____63215 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____63237 =
        let uu____63238 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____63238  in
      mk uu____63237 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____63252 =
      let uu____63255 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____63255  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____63252
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____63303 =
      let uu____63304 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____63304  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____63303  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____63390 = arg_as_string1 a1  in
        (match uu____63390 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63399 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____63399 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____63417 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____63417
              | uu____63419 -> FStar_Pervasives_Native.None)
         | uu____63425 -> FStar_Pervasives_Native.None)
    | uu____63429 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63510 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____63510 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63526 = arg_as_string1 a2  in
             (match uu____63526 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____63539 =
                    let uu____63540 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____63540 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____63539
              | uu____63550 -> FStar_Pervasives_Native.None)
         | uu____63554 -> FStar_Pervasives_Native.None)
    | uu____63560 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____63598 =
          let uu____63612 = arg_as_string1 a1  in
          let uu____63616 = arg_as_int1 a2  in
          let uu____63619 = arg_as_int1 a3  in
          (uu____63612, uu____63616, uu____63619)  in
        (match uu____63598 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_63652  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____63657 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63657) ()
              with | uu___1030_63660 -> FStar_Pervasives_Native.None)
         | uu____63663 -> FStar_Pervasives_Native.None)
    | uu____63677 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____63691 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____63691  in
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
        let uu____63770 =
          let uu____63780 = arg_as_string1 a1  in
          let uu____63784 = arg_as_int1 a2  in (uu____63780, uu____63784)  in
        (match uu____63770 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_63808  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____63813 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63813) ()
              with | uu___1064_63816 -> FStar_Pervasives_Native.None)
         | uu____63819 -> FStar_Pervasives_Native.None)
    | uu____63829 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63860 =
          let uu____63871 = arg_as_string1 a1  in
          let uu____63875 = arg_as_char1 a2  in (uu____63871, uu____63875)
           in
        (match uu____63860 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_63904  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____63908 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63908) ()
              with | uu___1085_63910 -> FStar_Pervasives_Native.None)
         | uu____63913 -> FStar_Pervasives_Native.None)
    | uu____63924 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____63958 =
          let uu____63980 = arg_as_string1 fn  in
          let uu____63984 = arg_as_int1 from_line  in
          let uu____63987 = arg_as_int1 from_col  in
          let uu____63990 = arg_as_int1 to_line  in
          let uu____63993 = arg_as_int1 to_col  in
          (uu____63980, uu____63984, uu____63987, uu____63990, uu____63993)
           in
        (match uu____63958 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____64028 =
                 let uu____64029 = FStar_BigInt.to_int_fs from_l  in
                 let uu____64031 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____64029 uu____64031  in
               let uu____64033 =
                 let uu____64034 = FStar_BigInt.to_int_fs to_l  in
                 let uu____64036 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____64034 uu____64036  in
               FStar_Range.mk_range fn1 uu____64028 uu____64033  in
             let uu____64038 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64038
         | uu____64039 -> FStar_Pervasives_Native.None)
    | uu____64061 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____64105)::(a1,uu____64107)::(a2,uu____64109)::[] ->
        let uu____64166 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____64166 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____64175 -> FStar_Pervasives_Native.None)
    | uu____64176 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____64219)::[] ->
        let uu____64236 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____64236 with
         | FStar_Pervasives_Native.Some r ->
             let uu____64242 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64242
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____64243 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____64263  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____64297 =
      let uu____64327 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____64327)
       in
    let uu____64361 =
      let uu____64393 =
        let uu____64423 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____64423)
         in
      let uu____64463 =
        let uu____64495 =
          let uu____64525 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____64525)
           in
        let uu____64565 =
          let uu____64597 =
            let uu____64627 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____64627)
             in
          let uu____64667 =
            let uu____64699 =
              let uu____64729 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____64729)
               in
            let uu____64769 =
              let uu____64801 =
                let uu____64831 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____64843 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____64843)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____64874 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____64874)), uu____64831)
                 in
              let uu____64877 =
                let uu____64909 =
                  let uu____64939 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____64951 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____64951)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____64982 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____64982)), uu____64939)
                   in
                let uu____64985 =
                  let uu____65017 =
                    let uu____65047 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____65059 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____65059)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____65090 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____65090)), uu____65047)
                     in
                  let uu____65093 =
                    let uu____65125 =
                      let uu____65155 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____65167 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____65167)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____65198 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____65198)), uu____65155)
                       in
                    let uu____65201 =
                      let uu____65233 =
                        let uu____65263 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____65263)
                         in
                      let uu____65303 =
                        let uu____65335 =
                          let uu____65365 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____65365)
                           in
                        let uu____65401 =
                          let uu____65433 =
                            let uu____65463 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____65463)
                             in
                          let uu____65507 =
                            let uu____65539 =
                              let uu____65569 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____65569)
                               in
                            let uu____65613 =
                              let uu____65645 =
                                let uu____65675 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____65675)
                                 in
                              let uu____65703 =
                                let uu____65735 =
                                  let uu____65765 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____65765)
                                   in
                                let uu____65795 =
                                  let uu____65827 =
                                    let uu____65857 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____65857)
                                     in
                                  let uu____65887 =
                                    let uu____65919 =
                                      let uu____65949 =
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
                                           string_of_list'1), uu____65949)
                                       in
                                    let uu____65985 =
                                      let uu____66017 =
                                        let uu____66049 =
                                          let uu____66081 =
                                            let uu____66111 =
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
                                              uu____66111)
                                             in
                                          let uu____66155 =
                                            let uu____66187 =
                                              let uu____66219 =
                                                let uu____66249 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____66249)
                                                 in
                                              let uu____66279 =
                                                let uu____66311 =
                                                  let uu____66341 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____66341)
                                                   in
                                                let uu____66371 =
                                                  let uu____66403 =
                                                    let uu____66433 =
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
                                                      uu____66433)
                                                     in
                                                  let uu____66463 =
                                                    let uu____66495 =
                                                      let uu____66527 =
                                                        let uu____66559 =
                                                          let uu____66591 =
                                                            let uu____66623 =
                                                              let uu____66655
                                                                =
                                                                let uu____66685
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____66685,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____66712
                                                                =
                                                                let uu____66744
                                                                  =
                                                                  let uu____66774
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____66774,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____66744]
                                                                 in
                                                              uu____66655 ::
                                                                uu____66712
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____66623
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____66591
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____66559
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____66527
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____66495
                                                     in
                                                  uu____66403 :: uu____66463
                                                   in
                                                uu____66311 :: uu____66371
                                                 in
                                              uu____66219 :: uu____66279  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____66187
                                             in
                                          uu____66081 :: uu____66155  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____66049
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
                                                  let uu____67421 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____67421 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____67432 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____67432
                                                  y)))
                                        :: uu____66017
                                       in
                                    uu____65919 :: uu____65985  in
                                  uu____65827 :: uu____65887  in
                                uu____65735 :: uu____65795  in
                              uu____65645 :: uu____65703  in
                            uu____65539 :: uu____65613  in
                          uu____65433 :: uu____65507  in
                        uu____65335 :: uu____65401  in
                      uu____65233 :: uu____65303  in
                    uu____65125 :: uu____65201  in
                  uu____65017 :: uu____65093  in
                uu____64909 :: uu____64985  in
              uu____64801 :: uu____64877  in
            uu____64699 :: uu____64769  in
          uu____64597 :: uu____64667  in
        uu____64495 :: uu____64565  in
      uu____64393 :: uu____64463  in
    uu____64297 :: uu____64361  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____68068 =
        let uu____68073 =
          let uu____68074 = FStar_Syntax_Syntax.as_arg c  in [uu____68074]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____68073  in
      uu____68068 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____68201 =
                let uu____68231 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____68238 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____68256  ->
                       fun uu____68257  ->
                         match (uu____68256, uu____68257) with
                         | ((int_to_t1,x),(uu____68276,y)) ->
                             let uu____68286 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____68286)
                   in
                (uu____68231, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____68321  ->
                          fun uu____68322  ->
                            match (uu____68321, uu____68322) with
                            | ((int_to_t1,x),(uu____68341,y)) ->
                                let uu____68351 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____68351)),
                  uu____68238)
                 in
              let uu____68352 =
                let uu____68384 =
                  let uu____68414 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____68421 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____68439  ->
                         fun uu____68440  ->
                           match (uu____68439, uu____68440) with
                           | ((int_to_t1,x),(uu____68459,y)) ->
                               let uu____68469 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____68469)
                     in
                  (uu____68414, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____68504  ->
                            fun uu____68505  ->
                              match (uu____68504, uu____68505) with
                              | ((int_to_t1,x),(uu____68524,y)) ->
                                  let uu____68534 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____68534)),
                    uu____68421)
                   in
                let uu____68535 =
                  let uu____68567 =
                    let uu____68597 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____68604 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____68622  ->
                           fun uu____68623  ->
                             match (uu____68622, uu____68623) with
                             | ((int_to_t1,x),(uu____68642,y)) ->
                                 let uu____68652 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____68652)
                       in
                    (uu____68597, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____68687  ->
                              fun uu____68688  ->
                                match (uu____68687, uu____68688) with
                                | ((int_to_t1,x),(uu____68707,y)) ->
                                    let uu____68717 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____68717)),
                      uu____68604)
                     in
                  let uu____68718 =
                    let uu____68750 =
                      let uu____68780 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____68787 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____68801  ->
                             match uu____68801 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____68780, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____68838  ->
                                match uu____68838 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____68787)
                       in
                    [uu____68750]  in
                  uu____68567 :: uu____68718  in
                uu____68384 :: uu____68535  in
              uu____68201 :: uu____68352))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____69091 =
                let uu____69121 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____69128 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69146  ->
                       fun uu____69147  ->
                         match (uu____69146, uu____69147) with
                         | ((int_to_t1,x),(uu____69166,y)) ->
                             let uu____69176 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69176)
                   in
                (uu____69121, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69211  ->
                          fun uu____69212  ->
                            match (uu____69211, uu____69212) with
                            | ((int_to_t1,x),(uu____69231,y)) ->
                                let uu____69241 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69241)),
                  uu____69128)
                 in
              let uu____69242 =
                let uu____69274 =
                  let uu____69304 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____69311 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____69329  ->
                         fun uu____69330  ->
                           match (uu____69329, uu____69330) with
                           | ((int_to_t1,x),(uu____69349,y)) ->
                               let uu____69359 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____69359)
                     in
                  (uu____69304, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____69394  ->
                            fun uu____69395  ->
                              match (uu____69394, uu____69395) with
                              | ((int_to_t1,x),(uu____69414,y)) ->
                                  let uu____69424 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____69424)),
                    uu____69311)
                   in
                [uu____69274]  in
              uu____69091 :: uu____69242))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____69530 ->
          let uu____69532 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____69532
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____69636 =
                let uu____69666 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____69673 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69691  ->
                       fun uu____69692  ->
                         match (uu____69691, uu____69692) with
                         | ((int_to_t1,x),(uu____69711,y)) ->
                             let uu____69721 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69721)
                   in
                (uu____69666, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69756  ->
                          fun uu____69757  ->
                            match (uu____69756, uu____69757) with
                            | ((int_to_t1,x),(uu____69776,y)) ->
                                let uu____69786 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69786)),
                  uu____69673)
                 in
              let uu____69787 =
                let uu____69819 =
                  let uu____69849 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____69856 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____69874  ->
                         fun uu____69875  ->
                           match (uu____69874, uu____69875) with
                           | ((int_to_t1,x),(uu____69894,y)) ->
                               let uu____69904 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____69904)
                     in
                  (uu____69849, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____69939  ->
                            fun uu____69940  ->
                              match (uu____69939, uu____69940) with
                              | ((int_to_t1,x),(uu____69959,y)) ->
                                  let uu____69969 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____69969)),
                    uu____69856)
                   in
                let uu____69970 =
                  let uu____70002 =
                    let uu____70032 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____70039 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____70057  ->
                           fun uu____70058  ->
                             match (uu____70057, uu____70058) with
                             | ((int_to_t1,x),(uu____70077,y)) ->
                                 let uu____70087 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70087)
                       in
                    (uu____70032, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____70122  ->
                              fun uu____70123  ->
                                match (uu____70122, uu____70123) with
                                | ((int_to_t1,x),(uu____70142,y)) ->
                                    let uu____70152 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____70152)),
                      uu____70039)
                     in
                  let uu____70153 =
                    let uu____70185 =
                      let uu____70215 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____70222 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____70237  ->
                             match uu____70237 with
                             | (int_to_t1,x) ->
                                 let uu____70244 =
                                   let uu____70245 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____70246 = mask m  in
                                   FStar_BigInt.logand_big_int uu____70245
                                     uu____70246
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70244)
                         in
                      (uu____70215, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____70278  ->
                                match uu____70278 with
                                | (int_to_t1,x) ->
                                    let uu____70285 =
                                      let uu____70286 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____70287 = mask m  in
                                      FStar_BigInt.logand_big_int uu____70286
                                        uu____70287
                                       in
                                    int_as_bounded1 r int_to_t1 uu____70285)),
                        uu____70222)
                       in
                    let uu____70288 =
                      let uu____70320 =
                        let uu____70350 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____70357 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____70375  ->
                               fun uu____70376  ->
                                 match (uu____70375, uu____70376) with
                                 | ((int_to_t1,x),(uu____70395,y)) ->
                                     let uu____70405 =
                                       let uu____70406 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____70407 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____70406 uu____70407
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____70405)
                           in
                        (uu____70350, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____70442  ->
                                  fun uu____70443  ->
                                    match (uu____70442, uu____70443) with
                                    | ((int_to_t1,x),(uu____70462,y)) ->
                                        let uu____70472 =
                                          let uu____70473 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____70474 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____70473 uu____70474
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____70472)), uu____70357)
                         in
                      let uu____70475 =
                        let uu____70507 =
                          let uu____70537 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____70544 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____70562  ->
                                 fun uu____70563  ->
                                   match (uu____70562, uu____70563) with
                                   | ((int_to_t1,x),(uu____70582,y)) ->
                                       let uu____70592 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____70592)
                             in
                          (uu____70537, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____70627  ->
                                    fun uu____70628  ->
                                      match (uu____70627, uu____70628) with
                                      | ((int_to_t1,x),(uu____70647,y)) ->
                                          let uu____70657 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____70657)), uu____70544)
                           in
                        [uu____70507]  in
                      uu____70320 :: uu____70475  in
                    uu____70185 :: uu____70288  in
                  uu____70002 :: uu____70153  in
                uu____69819 :: uu____69970  in
              uu____69636 :: uu____69787))
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
    | (_typ,uu____71049)::(a1,uu____71051)::(a2,uu____71053)::[] ->
        let uu____71110 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____71110 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1406_71114 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1406_71114.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1406_71114.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1409_71116 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1409_71116.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1409_71116.FStar_Syntax_Syntax.vars)
                })
         | uu____71117 -> FStar_Pervasives_Native.None)
    | uu____71118 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____71148)::(t2,uu____71150)::(a1,uu____71152)::(a2,uu____71154)::[]
        ->
        let uu____71227 =
          let uu____71228 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____71229 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____71228 uu____71229  in
        (match uu____71227 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1432_71233 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1432_71233.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1432_71233.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1435_71235 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1435_71235.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1435_71235.FStar_Syntax_Syntax.vars)
                })
         | uu____71236 -> FStar_Pervasives_Native.None)
    | uu____71237 -> failwith "Unexpected number of arguments"  in
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
  fun uu____71268  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____71285 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____71285 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____71314 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____71314 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____71325  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____71396  ->
           fun uu____71397  ->
             match (uu____71396, uu____71397) with
             | ((uu____71423,t1),(uu____71425,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____71459  ->
         fun rest  ->
           match uu____71459 with
           | (nm,ms) ->
               let uu____71475 =
                 let uu____71477 =
                   let uu____71479 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____71479  in
                 FStar_Util.format2 "%sms --- %s\n" uu____71477 nm  in
               FStar_String.op_Hat uu____71475 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____71510 =
      let uu____71513 = FStar_ST.op_Bang plugins  in p :: uu____71513  in
    FStar_ST.op_Colon_Equals plugins uu____71510  in
  let retrieve uu____71569 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____71622  ->
    let uu____71623 = FStar_Options.no_plugins ()  in
    if uu____71623 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____71644 = FStar_Options.use_nbe ()  in
    if uu____71644
    then
      let uu___1478_71647 = s  in
      {
        beta = (uu___1478_71647.beta);
        iota = (uu___1478_71647.iota);
        zeta = (uu___1478_71647.zeta);
        weak = (uu___1478_71647.weak);
        hnf = (uu___1478_71647.hnf);
        primops = (uu___1478_71647.primops);
        do_not_unfold_pure_lets = (uu___1478_71647.do_not_unfold_pure_lets);
        unfold_until = (uu___1478_71647.unfold_until);
        unfold_only = (uu___1478_71647.unfold_only);
        unfold_fully = (uu___1478_71647.unfold_fully);
        unfold_attr = (uu___1478_71647.unfold_attr);
        unfold_tac = (uu___1478_71647.unfold_tac);
        pure_subterms_within_computations =
          (uu___1478_71647.pure_subterms_within_computations);
        simplify = (uu___1478_71647.simplify);
        erase_universes = (uu___1478_71647.erase_universes);
        allow_unbound_universes = (uu___1478_71647.allow_unbound_universes);
        reify_ = (uu___1478_71647.reify_);
        compress_uvars = (uu___1478_71647.compress_uvars);
        no_full_norm = (uu___1478_71647.no_full_norm);
        check_no_uvars = (uu___1478_71647.check_no_uvars);
        unmeta = (uu___1478_71647.unmeta);
        unascribe = (uu___1478_71647.unascribe);
        in_full_norm_request = (uu___1478_71647.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1478_71647.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1478_71647.for_extraction)
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
               (fun uu___531_71684  ->
                  match uu___531_71684 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____71688 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____71694 -> d  in
        let uu____71697 =
          let uu____71698 = to_fsteps s  in
          FStar_All.pipe_right uu____71698 add_nbe  in
        let uu____71699 =
          let uu____71700 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____71703 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____71706 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____71709 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____71712 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____71715 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____71718 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____71721 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____71724 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____71700;
            top = uu____71703;
            cfg = uu____71706;
            primop = uu____71709;
            unfolding = uu____71712;
            b380 = uu____71715;
            wpe = uu____71718;
            norm_delayed = uu____71721;
            print_normalized = uu____71724
          }  in
        let uu____71727 =
          let uu____71730 =
            let uu____71733 = retrieve_plugins ()  in
            FStar_List.append uu____71733 psteps  in
          add_steps built_in_primitive_steps uu____71730  in
        let uu____71736 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____71739 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____71739)
           in
        {
          steps = uu____71697;
          tcenv = e;
          debug = uu____71699;
          delta_level = d1;
          primitive_steps = uu____71727;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____71736;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 