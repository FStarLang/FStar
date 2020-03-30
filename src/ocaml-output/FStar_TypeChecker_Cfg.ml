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
  reduce_div_lets: Prims.bool ;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> beta
  
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> iota1
  
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> zeta1
  
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> weak1
  
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> hnf1
  
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        do_not_unfold_pure_lets
  
let (__proj__Mkfsteps__item__reduce_div_lets : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        reduce_div_lets
  
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_attr
  
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> simplify1
  
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> reify_1
  
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> no_full_norm
  
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unmeta1
  
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unascribe1
  
let (__proj__Mkfsteps__item__in_full_norm_request : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> nbe_step
  
let (__proj__Mkfsteps__item__for_extraction : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; reduce_div_lets;
        unfold_until; unfold_only; unfold_fully; unfold_attr; unfold_tac;
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
          let uu____2231 =
            let uu____2233 = f1 x  in FStar_String.op_Hat uu____2233 ")"  in
          FStar_String.op_Hat "Some (" uu____2231
       in
    let b = FStar_Util.string_of_bool  in
    let uu____2244 =
      let uu____2248 = FStar_All.pipe_right f.beta b  in
      let uu____2252 =
        let uu____2256 = FStar_All.pipe_right f.iota b  in
        let uu____2260 =
          let uu____2264 = FStar_All.pipe_right f.zeta b  in
          let uu____2268 =
            let uu____2272 = FStar_All.pipe_right f.weak b  in
            let uu____2276 =
              let uu____2280 = FStar_All.pipe_right f.hnf b  in
              let uu____2284 =
                let uu____2288 = FStar_All.pipe_right f.primops b  in
                let uu____2292 =
                  let uu____2296 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____2300 =
                    let uu____2304 = FStar_All.pipe_right f.reduce_div_lets b
                       in
                    let uu____2308 =
                      let uu____2312 =
                        FStar_All.pipe_right f.unfold_until
                          (format_opt
                             FStar_Syntax_Print.delta_depth_to_string)
                         in
                      let uu____2317 =
                        let uu____2321 =
                          FStar_All.pipe_right f.unfold_only
                            (format_opt
                               (fun x  ->
                                  let uu____2335 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____2335
                                    (FStar_String.concat ", ")))
                           in
                        let uu____2345 =
                          let uu____2349 =
                            FStar_All.pipe_right f.unfold_fully
                              (format_opt
                                 (fun x  ->
                                    let uu____2363 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____2363
                                      (FStar_String.concat ", ")))
                             in
                          let uu____2373 =
                            let uu____2377 =
                              FStar_All.pipe_right f.unfold_attr
                                (format_opt
                                   (fun x  ->
                                      let uu____2391 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid x
                                         in
                                      FStar_All.pipe_right uu____2391
                                        (FStar_String.concat ", ")))
                               in
                            let uu____2401 =
                              let uu____2405 =
                                FStar_All.pipe_right f.unfold_tac b  in
                              let uu____2409 =
                                let uu____2413 =
                                  FStar_All.pipe_right
                                    f.pure_subterms_within_computations b
                                   in
                                let uu____2417 =
                                  let uu____2421 =
                                    FStar_All.pipe_right f.simplify b  in
                                  let uu____2425 =
                                    let uu____2429 =
                                      FStar_All.pipe_right f.erase_universes
                                        b
                                       in
                                    let uu____2433 =
                                      let uu____2437 =
                                        FStar_All.pipe_right
                                          f.allow_unbound_universes b
                                         in
                                      let uu____2441 =
                                        let uu____2445 =
                                          FStar_All.pipe_right f.reify_ b  in
                                        let uu____2449 =
                                          let uu____2453 =
                                            FStar_All.pipe_right
                                              f.compress_uvars b
                                             in
                                          let uu____2457 =
                                            let uu____2461 =
                                              FStar_All.pipe_right
                                                f.no_full_norm b
                                               in
                                            let uu____2465 =
                                              let uu____2469 =
                                                FStar_All.pipe_right
                                                  f.check_no_uvars b
                                                 in
                                              let uu____2473 =
                                                let uu____2477 =
                                                  FStar_All.pipe_right
                                                    f.unmeta b
                                                   in
                                                let uu____2481 =
                                                  let uu____2485 =
                                                    FStar_All.pipe_right
                                                      f.unascribe b
                                                     in
                                                  let uu____2489 =
                                                    let uu____2493 =
                                                      FStar_All.pipe_right
                                                        f.in_full_norm_request
                                                        b
                                                       in
                                                    let uu____2497 =
                                                      let uu____2501 =
                                                        FStar_All.pipe_right
                                                          f.weakly_reduce_scrutinee
                                                          b
                                                         in
                                                      [uu____2501]  in
                                                    uu____2493 :: uu____2497
                                                     in
                                                  uu____2485 :: uu____2489
                                                   in
                                                uu____2477 :: uu____2481  in
                                              uu____2469 :: uu____2473  in
                                            uu____2461 :: uu____2465  in
                                          uu____2453 :: uu____2457  in
                                        uu____2445 :: uu____2449  in
                                      uu____2437 :: uu____2441  in
                                    uu____2429 :: uu____2433  in
                                  uu____2421 :: uu____2425  in
                                uu____2413 :: uu____2417  in
                              uu____2405 :: uu____2409  in
                            uu____2377 :: uu____2401  in
                          uu____2349 :: uu____2373  in
                        uu____2321 :: uu____2345  in
                      uu____2312 :: uu____2317  in
                    uu____2304 :: uu____2308  in
                  uu____2296 :: uu____2300  in
                uu____2288 :: uu____2292  in
              uu____2280 :: uu____2284  in
            uu____2272 :: uu____2276  in
          uu____2264 :: uu____2268  in
        uu____2256 :: uu____2260  in
      uu____2248 :: uu____2252  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nreduce_div_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____2244
  
let (default_steps : fsteps) =
  {
    beta = true;
    iota = true;
    zeta = true;
    weak = false;
    hnf = false;
    primops = false;
    do_not_unfold_pure_lets = false;
    reduce_div_lets = false;
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
          let uu___97_2573 = fs  in
          {
            beta = true;
            iota = (uu___97_2573.iota);
            zeta = (uu___97_2573.zeta);
            weak = (uu___97_2573.weak);
            hnf = (uu___97_2573.hnf);
            primops = (uu___97_2573.primops);
            do_not_unfold_pure_lets = (uu___97_2573.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___97_2573.reduce_div_lets);
            unfold_until = (uu___97_2573.unfold_until);
            unfold_only = (uu___97_2573.unfold_only);
            unfold_fully = (uu___97_2573.unfold_fully);
            unfold_attr = (uu___97_2573.unfold_attr);
            unfold_tac = (uu___97_2573.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_2573.pure_subterms_within_computations);
            simplify = (uu___97_2573.simplify);
            erase_universes = (uu___97_2573.erase_universes);
            allow_unbound_universes = (uu___97_2573.allow_unbound_universes);
            reify_ = (uu___97_2573.reify_);
            compress_uvars = (uu___97_2573.compress_uvars);
            no_full_norm = (uu___97_2573.no_full_norm);
            check_no_uvars = (uu___97_2573.check_no_uvars);
            unmeta = (uu___97_2573.unmeta);
            unascribe = (uu___97_2573.unascribe);
            in_full_norm_request = (uu___97_2573.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___97_2573.weakly_reduce_scrutinee);
            nbe_step = (uu___97_2573.nbe_step);
            for_extraction = (uu___97_2573.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___100_2575 = fs  in
          {
            beta = (uu___100_2575.beta);
            iota = true;
            zeta = (uu___100_2575.zeta);
            weak = (uu___100_2575.weak);
            hnf = (uu___100_2575.hnf);
            primops = (uu___100_2575.primops);
            do_not_unfold_pure_lets = (uu___100_2575.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___100_2575.reduce_div_lets);
            unfold_until = (uu___100_2575.unfold_until);
            unfold_only = (uu___100_2575.unfold_only);
            unfold_fully = (uu___100_2575.unfold_fully);
            unfold_attr = (uu___100_2575.unfold_attr);
            unfold_tac = (uu___100_2575.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_2575.pure_subterms_within_computations);
            simplify = (uu___100_2575.simplify);
            erase_universes = (uu___100_2575.erase_universes);
            allow_unbound_universes = (uu___100_2575.allow_unbound_universes);
            reify_ = (uu___100_2575.reify_);
            compress_uvars = (uu___100_2575.compress_uvars);
            no_full_norm = (uu___100_2575.no_full_norm);
            check_no_uvars = (uu___100_2575.check_no_uvars);
            unmeta = (uu___100_2575.unmeta);
            unascribe = (uu___100_2575.unascribe);
            in_full_norm_request = (uu___100_2575.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_2575.weakly_reduce_scrutinee);
            nbe_step = (uu___100_2575.nbe_step);
            for_extraction = (uu___100_2575.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___103_2577 = fs  in
          {
            beta = (uu___103_2577.beta);
            iota = (uu___103_2577.iota);
            zeta = true;
            weak = (uu___103_2577.weak);
            hnf = (uu___103_2577.hnf);
            primops = (uu___103_2577.primops);
            do_not_unfold_pure_lets = (uu___103_2577.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___103_2577.reduce_div_lets);
            unfold_until = (uu___103_2577.unfold_until);
            unfold_only = (uu___103_2577.unfold_only);
            unfold_fully = (uu___103_2577.unfold_fully);
            unfold_attr = (uu___103_2577.unfold_attr);
            unfold_tac = (uu___103_2577.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_2577.pure_subterms_within_computations);
            simplify = (uu___103_2577.simplify);
            erase_universes = (uu___103_2577.erase_universes);
            allow_unbound_universes = (uu___103_2577.allow_unbound_universes);
            reify_ = (uu___103_2577.reify_);
            compress_uvars = (uu___103_2577.compress_uvars);
            no_full_norm = (uu___103_2577.no_full_norm);
            check_no_uvars = (uu___103_2577.check_no_uvars);
            unmeta = (uu___103_2577.unmeta);
            unascribe = (uu___103_2577.unascribe);
            in_full_norm_request = (uu___103_2577.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___103_2577.weakly_reduce_scrutinee);
            nbe_step = (uu___103_2577.nbe_step);
            for_extraction = (uu___103_2577.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___107_2579 = fs  in
          {
            beta = false;
            iota = (uu___107_2579.iota);
            zeta = (uu___107_2579.zeta);
            weak = (uu___107_2579.weak);
            hnf = (uu___107_2579.hnf);
            primops = (uu___107_2579.primops);
            do_not_unfold_pure_lets = (uu___107_2579.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___107_2579.reduce_div_lets);
            unfold_until = (uu___107_2579.unfold_until);
            unfold_only = (uu___107_2579.unfold_only);
            unfold_fully = (uu___107_2579.unfold_fully);
            unfold_attr = (uu___107_2579.unfold_attr);
            unfold_tac = (uu___107_2579.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_2579.pure_subterms_within_computations);
            simplify = (uu___107_2579.simplify);
            erase_universes = (uu___107_2579.erase_universes);
            allow_unbound_universes = (uu___107_2579.allow_unbound_universes);
            reify_ = (uu___107_2579.reify_);
            compress_uvars = (uu___107_2579.compress_uvars);
            no_full_norm = (uu___107_2579.no_full_norm);
            check_no_uvars = (uu___107_2579.check_no_uvars);
            unmeta = (uu___107_2579.unmeta);
            unascribe = (uu___107_2579.unascribe);
            in_full_norm_request = (uu___107_2579.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___107_2579.weakly_reduce_scrutinee);
            nbe_step = (uu___107_2579.nbe_step);
            for_extraction = (uu___107_2579.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___111_2581 = fs  in
          {
            beta = (uu___111_2581.beta);
            iota = false;
            zeta = (uu___111_2581.zeta);
            weak = (uu___111_2581.weak);
            hnf = (uu___111_2581.hnf);
            primops = (uu___111_2581.primops);
            do_not_unfold_pure_lets = (uu___111_2581.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___111_2581.reduce_div_lets);
            unfold_until = (uu___111_2581.unfold_until);
            unfold_only = (uu___111_2581.unfold_only);
            unfold_fully = (uu___111_2581.unfold_fully);
            unfold_attr = (uu___111_2581.unfold_attr);
            unfold_tac = (uu___111_2581.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_2581.pure_subterms_within_computations);
            simplify = (uu___111_2581.simplify);
            erase_universes = (uu___111_2581.erase_universes);
            allow_unbound_universes = (uu___111_2581.allow_unbound_universes);
            reify_ = (uu___111_2581.reify_);
            compress_uvars = (uu___111_2581.compress_uvars);
            no_full_norm = (uu___111_2581.no_full_norm);
            check_no_uvars = (uu___111_2581.check_no_uvars);
            unmeta = (uu___111_2581.unmeta);
            unascribe = (uu___111_2581.unascribe);
            in_full_norm_request = (uu___111_2581.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___111_2581.weakly_reduce_scrutinee);
            nbe_step = (uu___111_2581.nbe_step);
            for_extraction = (uu___111_2581.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___115_2583 = fs  in
          {
            beta = (uu___115_2583.beta);
            iota = (uu___115_2583.iota);
            zeta = false;
            weak = (uu___115_2583.weak);
            hnf = (uu___115_2583.hnf);
            primops = (uu___115_2583.primops);
            do_not_unfold_pure_lets = (uu___115_2583.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___115_2583.reduce_div_lets);
            unfold_until = (uu___115_2583.unfold_until);
            unfold_only = (uu___115_2583.unfold_only);
            unfold_fully = (uu___115_2583.unfold_fully);
            unfold_attr = (uu___115_2583.unfold_attr);
            unfold_tac = (uu___115_2583.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_2583.pure_subterms_within_computations);
            simplify = (uu___115_2583.simplify);
            erase_universes = (uu___115_2583.erase_universes);
            allow_unbound_universes = (uu___115_2583.allow_unbound_universes);
            reify_ = (uu___115_2583.reify_);
            compress_uvars = (uu___115_2583.compress_uvars);
            no_full_norm = (uu___115_2583.no_full_norm);
            check_no_uvars = (uu___115_2583.check_no_uvars);
            unmeta = (uu___115_2583.unmeta);
            unascribe = (uu___115_2583.unascribe);
            in_full_norm_request = (uu___115_2583.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___115_2583.weakly_reduce_scrutinee);
            nbe_step = (uu___115_2583.nbe_step);
            for_extraction = (uu___115_2583.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____2585 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___120_2587 = fs  in
          {
            beta = (uu___120_2587.beta);
            iota = (uu___120_2587.iota);
            zeta = (uu___120_2587.zeta);
            weak = true;
            hnf = (uu___120_2587.hnf);
            primops = (uu___120_2587.primops);
            do_not_unfold_pure_lets = (uu___120_2587.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___120_2587.reduce_div_lets);
            unfold_until = (uu___120_2587.unfold_until);
            unfold_only = (uu___120_2587.unfold_only);
            unfold_fully = (uu___120_2587.unfold_fully);
            unfold_attr = (uu___120_2587.unfold_attr);
            unfold_tac = (uu___120_2587.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_2587.pure_subterms_within_computations);
            simplify = (uu___120_2587.simplify);
            erase_universes = (uu___120_2587.erase_universes);
            allow_unbound_universes = (uu___120_2587.allow_unbound_universes);
            reify_ = (uu___120_2587.reify_);
            compress_uvars = (uu___120_2587.compress_uvars);
            no_full_norm = (uu___120_2587.no_full_norm);
            check_no_uvars = (uu___120_2587.check_no_uvars);
            unmeta = (uu___120_2587.unmeta);
            unascribe = (uu___120_2587.unascribe);
            in_full_norm_request = (uu___120_2587.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___120_2587.weakly_reduce_scrutinee);
            nbe_step = (uu___120_2587.nbe_step);
            for_extraction = (uu___120_2587.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___123_2589 = fs  in
          {
            beta = (uu___123_2589.beta);
            iota = (uu___123_2589.iota);
            zeta = (uu___123_2589.zeta);
            weak = (uu___123_2589.weak);
            hnf = true;
            primops = (uu___123_2589.primops);
            do_not_unfold_pure_lets = (uu___123_2589.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___123_2589.reduce_div_lets);
            unfold_until = (uu___123_2589.unfold_until);
            unfold_only = (uu___123_2589.unfold_only);
            unfold_fully = (uu___123_2589.unfold_fully);
            unfold_attr = (uu___123_2589.unfold_attr);
            unfold_tac = (uu___123_2589.unfold_tac);
            pure_subterms_within_computations =
              (uu___123_2589.pure_subterms_within_computations);
            simplify = (uu___123_2589.simplify);
            erase_universes = (uu___123_2589.erase_universes);
            allow_unbound_universes = (uu___123_2589.allow_unbound_universes);
            reify_ = (uu___123_2589.reify_);
            compress_uvars = (uu___123_2589.compress_uvars);
            no_full_norm = (uu___123_2589.no_full_norm);
            check_no_uvars = (uu___123_2589.check_no_uvars);
            unmeta = (uu___123_2589.unmeta);
            unascribe = (uu___123_2589.unascribe);
            in_full_norm_request = (uu___123_2589.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___123_2589.weakly_reduce_scrutinee);
            nbe_step = (uu___123_2589.nbe_step);
            for_extraction = (uu___123_2589.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___126_2591 = fs  in
          {
            beta = (uu___126_2591.beta);
            iota = (uu___126_2591.iota);
            zeta = (uu___126_2591.zeta);
            weak = (uu___126_2591.weak);
            hnf = (uu___126_2591.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___126_2591.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___126_2591.reduce_div_lets);
            unfold_until = (uu___126_2591.unfold_until);
            unfold_only = (uu___126_2591.unfold_only);
            unfold_fully = (uu___126_2591.unfold_fully);
            unfold_attr = (uu___126_2591.unfold_attr);
            unfold_tac = (uu___126_2591.unfold_tac);
            pure_subterms_within_computations =
              (uu___126_2591.pure_subterms_within_computations);
            simplify = (uu___126_2591.simplify);
            erase_universes = (uu___126_2591.erase_universes);
            allow_unbound_universes = (uu___126_2591.allow_unbound_universes);
            reify_ = (uu___126_2591.reify_);
            compress_uvars = (uu___126_2591.compress_uvars);
            no_full_norm = (uu___126_2591.no_full_norm);
            check_no_uvars = (uu___126_2591.check_no_uvars);
            unmeta = (uu___126_2591.unmeta);
            unascribe = (uu___126_2591.unascribe);
            in_full_norm_request = (uu___126_2591.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___126_2591.weakly_reduce_scrutinee);
            nbe_step = (uu___126_2591.nbe_step);
            for_extraction = (uu___126_2591.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___131_2593 = fs  in
          {
            beta = (uu___131_2593.beta);
            iota = (uu___131_2593.iota);
            zeta = (uu___131_2593.zeta);
            weak = (uu___131_2593.weak);
            hnf = (uu___131_2593.hnf);
            primops = (uu___131_2593.primops);
            do_not_unfold_pure_lets = true;
            reduce_div_lets = (uu___131_2593.reduce_div_lets);
            unfold_until = (uu___131_2593.unfold_until);
            unfold_only = (uu___131_2593.unfold_only);
            unfold_fully = (uu___131_2593.unfold_fully);
            unfold_attr = (uu___131_2593.unfold_attr);
            unfold_tac = (uu___131_2593.unfold_tac);
            pure_subterms_within_computations =
              (uu___131_2593.pure_subterms_within_computations);
            simplify = (uu___131_2593.simplify);
            erase_universes = (uu___131_2593.erase_universes);
            allow_unbound_universes = (uu___131_2593.allow_unbound_universes);
            reify_ = (uu___131_2593.reify_);
            compress_uvars = (uu___131_2593.compress_uvars);
            no_full_norm = (uu___131_2593.no_full_norm);
            check_no_uvars = (uu___131_2593.check_no_uvars);
            unmeta = (uu___131_2593.unmeta);
            unascribe = (uu___131_2593.unascribe);
            in_full_norm_request = (uu___131_2593.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___131_2593.weakly_reduce_scrutinee);
            nbe_step = (uu___131_2593.nbe_step);
            for_extraction = (uu___131_2593.for_extraction)
          }
      | FStar_TypeChecker_Env.ReduceDivLets  ->
          let uu___134_2595 = fs  in
          {
            beta = (uu___134_2595.beta);
            iota = (uu___134_2595.iota);
            zeta = (uu___134_2595.zeta);
            weak = (uu___134_2595.weak);
            hnf = (uu___134_2595.hnf);
            primops = (uu___134_2595.primops);
            do_not_unfold_pure_lets = (uu___134_2595.do_not_unfold_pure_lets);
            reduce_div_lets = true;
            unfold_until = (uu___134_2595.unfold_until);
            unfold_only = (uu___134_2595.unfold_only);
            unfold_fully = (uu___134_2595.unfold_fully);
            unfold_attr = (uu___134_2595.unfold_attr);
            unfold_tac = (uu___134_2595.unfold_tac);
            pure_subterms_within_computations =
              (uu___134_2595.pure_subterms_within_computations);
            simplify = (uu___134_2595.simplify);
            erase_universes = (uu___134_2595.erase_universes);
            allow_unbound_universes = (uu___134_2595.allow_unbound_universes);
            reify_ = (uu___134_2595.reify_);
            compress_uvars = (uu___134_2595.compress_uvars);
            no_full_norm = (uu___134_2595.no_full_norm);
            check_no_uvars = (uu___134_2595.check_no_uvars);
            unmeta = (uu___134_2595.unmeta);
            unascribe = (uu___134_2595.unascribe);
            in_full_norm_request = (uu___134_2595.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___134_2595.weakly_reduce_scrutinee);
            nbe_step = (uu___134_2595.nbe_step);
            for_extraction = (uu___134_2595.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___138_2598 = fs  in
          {
            beta = (uu___138_2598.beta);
            iota = (uu___138_2598.iota);
            zeta = (uu___138_2598.zeta);
            weak = (uu___138_2598.weak);
            hnf = (uu___138_2598.hnf);
            primops = (uu___138_2598.primops);
            do_not_unfold_pure_lets = (uu___138_2598.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___138_2598.reduce_div_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___138_2598.unfold_only);
            unfold_fully = (uu___138_2598.unfold_fully);
            unfold_attr = (uu___138_2598.unfold_attr);
            unfold_tac = (uu___138_2598.unfold_tac);
            pure_subterms_within_computations =
              (uu___138_2598.pure_subterms_within_computations);
            simplify = (uu___138_2598.simplify);
            erase_universes = (uu___138_2598.erase_universes);
            allow_unbound_universes = (uu___138_2598.allow_unbound_universes);
            reify_ = (uu___138_2598.reify_);
            compress_uvars = (uu___138_2598.compress_uvars);
            no_full_norm = (uu___138_2598.no_full_norm);
            check_no_uvars = (uu___138_2598.check_no_uvars);
            unmeta = (uu___138_2598.unmeta);
            unascribe = (uu___138_2598.unascribe);
            in_full_norm_request = (uu___138_2598.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___138_2598.weakly_reduce_scrutinee);
            nbe_step = (uu___138_2598.nbe_step);
            for_extraction = (uu___138_2598.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___142_2602 = fs  in
          {
            beta = (uu___142_2602.beta);
            iota = (uu___142_2602.iota);
            zeta = (uu___142_2602.zeta);
            weak = (uu___142_2602.weak);
            hnf = (uu___142_2602.hnf);
            primops = (uu___142_2602.primops);
            do_not_unfold_pure_lets = (uu___142_2602.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___142_2602.reduce_div_lets);
            unfold_until = (uu___142_2602.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___142_2602.unfold_fully);
            unfold_attr = (uu___142_2602.unfold_attr);
            unfold_tac = (uu___142_2602.unfold_tac);
            pure_subterms_within_computations =
              (uu___142_2602.pure_subterms_within_computations);
            simplify = (uu___142_2602.simplify);
            erase_universes = (uu___142_2602.erase_universes);
            allow_unbound_universes = (uu___142_2602.allow_unbound_universes);
            reify_ = (uu___142_2602.reify_);
            compress_uvars = (uu___142_2602.compress_uvars);
            no_full_norm = (uu___142_2602.no_full_norm);
            check_no_uvars = (uu___142_2602.check_no_uvars);
            unmeta = (uu___142_2602.unmeta);
            unascribe = (uu___142_2602.unascribe);
            in_full_norm_request = (uu___142_2602.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___142_2602.weakly_reduce_scrutinee);
            nbe_step = (uu___142_2602.nbe_step);
            for_extraction = (uu___142_2602.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___146_2608 = fs  in
          {
            beta = (uu___146_2608.beta);
            iota = (uu___146_2608.iota);
            zeta = (uu___146_2608.zeta);
            weak = (uu___146_2608.weak);
            hnf = (uu___146_2608.hnf);
            primops = (uu___146_2608.primops);
            do_not_unfold_pure_lets = (uu___146_2608.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___146_2608.reduce_div_lets);
            unfold_until = (uu___146_2608.unfold_until);
            unfold_only = (uu___146_2608.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___146_2608.unfold_attr);
            unfold_tac = (uu___146_2608.unfold_tac);
            pure_subterms_within_computations =
              (uu___146_2608.pure_subterms_within_computations);
            simplify = (uu___146_2608.simplify);
            erase_universes = (uu___146_2608.erase_universes);
            allow_unbound_universes = (uu___146_2608.allow_unbound_universes);
            reify_ = (uu___146_2608.reify_);
            compress_uvars = (uu___146_2608.compress_uvars);
            no_full_norm = (uu___146_2608.no_full_norm);
            check_no_uvars = (uu___146_2608.check_no_uvars);
            unmeta = (uu___146_2608.unmeta);
            unascribe = (uu___146_2608.unascribe);
            in_full_norm_request = (uu___146_2608.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___146_2608.weakly_reduce_scrutinee);
            nbe_step = (uu___146_2608.nbe_step);
            for_extraction = (uu___146_2608.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___150_2614 = fs  in
          {
            beta = (uu___150_2614.beta);
            iota = (uu___150_2614.iota);
            zeta = (uu___150_2614.zeta);
            weak = (uu___150_2614.weak);
            hnf = (uu___150_2614.hnf);
            primops = (uu___150_2614.primops);
            do_not_unfold_pure_lets = (uu___150_2614.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___150_2614.reduce_div_lets);
            unfold_until = (uu___150_2614.unfold_until);
            unfold_only = (uu___150_2614.unfold_only);
            unfold_fully = (uu___150_2614.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___150_2614.unfold_tac);
            pure_subterms_within_computations =
              (uu___150_2614.pure_subterms_within_computations);
            simplify = (uu___150_2614.simplify);
            erase_universes = (uu___150_2614.erase_universes);
            allow_unbound_universes = (uu___150_2614.allow_unbound_universes);
            reify_ = (uu___150_2614.reify_);
            compress_uvars = (uu___150_2614.compress_uvars);
            no_full_norm = (uu___150_2614.no_full_norm);
            check_no_uvars = (uu___150_2614.check_no_uvars);
            unmeta = (uu___150_2614.unmeta);
            unascribe = (uu___150_2614.unascribe);
            in_full_norm_request = (uu___150_2614.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___150_2614.weakly_reduce_scrutinee);
            nbe_step = (uu___150_2614.nbe_step);
            for_extraction = (uu___150_2614.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___153_2617 = fs  in
          {
            beta = (uu___153_2617.beta);
            iota = (uu___153_2617.iota);
            zeta = (uu___153_2617.zeta);
            weak = (uu___153_2617.weak);
            hnf = (uu___153_2617.hnf);
            primops = (uu___153_2617.primops);
            do_not_unfold_pure_lets = (uu___153_2617.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___153_2617.reduce_div_lets);
            unfold_until = (uu___153_2617.unfold_until);
            unfold_only = (uu___153_2617.unfold_only);
            unfold_fully = (uu___153_2617.unfold_fully);
            unfold_attr = (uu___153_2617.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___153_2617.pure_subterms_within_computations);
            simplify = (uu___153_2617.simplify);
            erase_universes = (uu___153_2617.erase_universes);
            allow_unbound_universes = (uu___153_2617.allow_unbound_universes);
            reify_ = (uu___153_2617.reify_);
            compress_uvars = (uu___153_2617.compress_uvars);
            no_full_norm = (uu___153_2617.no_full_norm);
            check_no_uvars = (uu___153_2617.check_no_uvars);
            unmeta = (uu___153_2617.unmeta);
            unascribe = (uu___153_2617.unascribe);
            in_full_norm_request = (uu___153_2617.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___153_2617.weakly_reduce_scrutinee);
            nbe_step = (uu___153_2617.nbe_step);
            for_extraction = (uu___153_2617.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___156_2619 = fs  in
          {
            beta = (uu___156_2619.beta);
            iota = (uu___156_2619.iota);
            zeta = (uu___156_2619.zeta);
            weak = (uu___156_2619.weak);
            hnf = (uu___156_2619.hnf);
            primops = (uu___156_2619.primops);
            do_not_unfold_pure_lets = (uu___156_2619.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___156_2619.reduce_div_lets);
            unfold_until = (uu___156_2619.unfold_until);
            unfold_only = (uu___156_2619.unfold_only);
            unfold_fully = (uu___156_2619.unfold_fully);
            unfold_attr = (uu___156_2619.unfold_attr);
            unfold_tac = (uu___156_2619.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___156_2619.simplify);
            erase_universes = (uu___156_2619.erase_universes);
            allow_unbound_universes = (uu___156_2619.allow_unbound_universes);
            reify_ = (uu___156_2619.reify_);
            compress_uvars = (uu___156_2619.compress_uvars);
            no_full_norm = (uu___156_2619.no_full_norm);
            check_no_uvars = (uu___156_2619.check_no_uvars);
            unmeta = (uu___156_2619.unmeta);
            unascribe = (uu___156_2619.unascribe);
            in_full_norm_request = (uu___156_2619.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___156_2619.weakly_reduce_scrutinee);
            nbe_step = (uu___156_2619.nbe_step);
            for_extraction = (uu___156_2619.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___159_2621 = fs  in
          {
            beta = (uu___159_2621.beta);
            iota = (uu___159_2621.iota);
            zeta = (uu___159_2621.zeta);
            weak = (uu___159_2621.weak);
            hnf = (uu___159_2621.hnf);
            primops = (uu___159_2621.primops);
            do_not_unfold_pure_lets = (uu___159_2621.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___159_2621.reduce_div_lets);
            unfold_until = (uu___159_2621.unfold_until);
            unfold_only = (uu___159_2621.unfold_only);
            unfold_fully = (uu___159_2621.unfold_fully);
            unfold_attr = (uu___159_2621.unfold_attr);
            unfold_tac = (uu___159_2621.unfold_tac);
            pure_subterms_within_computations =
              (uu___159_2621.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___159_2621.erase_universes);
            allow_unbound_universes = (uu___159_2621.allow_unbound_universes);
            reify_ = (uu___159_2621.reify_);
            compress_uvars = (uu___159_2621.compress_uvars);
            no_full_norm = (uu___159_2621.no_full_norm);
            check_no_uvars = (uu___159_2621.check_no_uvars);
            unmeta = (uu___159_2621.unmeta);
            unascribe = (uu___159_2621.unascribe);
            in_full_norm_request = (uu___159_2621.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___159_2621.weakly_reduce_scrutinee);
            nbe_step = (uu___159_2621.nbe_step);
            for_extraction = (uu___159_2621.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___162_2623 = fs  in
          {
            beta = (uu___162_2623.beta);
            iota = (uu___162_2623.iota);
            zeta = (uu___162_2623.zeta);
            weak = (uu___162_2623.weak);
            hnf = (uu___162_2623.hnf);
            primops = (uu___162_2623.primops);
            do_not_unfold_pure_lets = (uu___162_2623.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___162_2623.reduce_div_lets);
            unfold_until = (uu___162_2623.unfold_until);
            unfold_only = (uu___162_2623.unfold_only);
            unfold_fully = (uu___162_2623.unfold_fully);
            unfold_attr = (uu___162_2623.unfold_attr);
            unfold_tac = (uu___162_2623.unfold_tac);
            pure_subterms_within_computations =
              (uu___162_2623.pure_subterms_within_computations);
            simplify = (uu___162_2623.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___162_2623.allow_unbound_universes);
            reify_ = (uu___162_2623.reify_);
            compress_uvars = (uu___162_2623.compress_uvars);
            no_full_norm = (uu___162_2623.no_full_norm);
            check_no_uvars = (uu___162_2623.check_no_uvars);
            unmeta = (uu___162_2623.unmeta);
            unascribe = (uu___162_2623.unascribe);
            in_full_norm_request = (uu___162_2623.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___162_2623.weakly_reduce_scrutinee);
            nbe_step = (uu___162_2623.nbe_step);
            for_extraction = (uu___162_2623.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___165_2625 = fs  in
          {
            beta = (uu___165_2625.beta);
            iota = (uu___165_2625.iota);
            zeta = (uu___165_2625.zeta);
            weak = (uu___165_2625.weak);
            hnf = (uu___165_2625.hnf);
            primops = (uu___165_2625.primops);
            do_not_unfold_pure_lets = (uu___165_2625.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___165_2625.reduce_div_lets);
            unfold_until = (uu___165_2625.unfold_until);
            unfold_only = (uu___165_2625.unfold_only);
            unfold_fully = (uu___165_2625.unfold_fully);
            unfold_attr = (uu___165_2625.unfold_attr);
            unfold_tac = (uu___165_2625.unfold_tac);
            pure_subterms_within_computations =
              (uu___165_2625.pure_subterms_within_computations);
            simplify = (uu___165_2625.simplify);
            erase_universes = (uu___165_2625.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___165_2625.reify_);
            compress_uvars = (uu___165_2625.compress_uvars);
            no_full_norm = (uu___165_2625.no_full_norm);
            check_no_uvars = (uu___165_2625.check_no_uvars);
            unmeta = (uu___165_2625.unmeta);
            unascribe = (uu___165_2625.unascribe);
            in_full_norm_request = (uu___165_2625.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___165_2625.weakly_reduce_scrutinee);
            nbe_step = (uu___165_2625.nbe_step);
            for_extraction = (uu___165_2625.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___168_2627 = fs  in
          {
            beta = (uu___168_2627.beta);
            iota = (uu___168_2627.iota);
            zeta = (uu___168_2627.zeta);
            weak = (uu___168_2627.weak);
            hnf = (uu___168_2627.hnf);
            primops = (uu___168_2627.primops);
            do_not_unfold_pure_lets = (uu___168_2627.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___168_2627.reduce_div_lets);
            unfold_until = (uu___168_2627.unfold_until);
            unfold_only = (uu___168_2627.unfold_only);
            unfold_fully = (uu___168_2627.unfold_fully);
            unfold_attr = (uu___168_2627.unfold_attr);
            unfold_tac = (uu___168_2627.unfold_tac);
            pure_subterms_within_computations =
              (uu___168_2627.pure_subterms_within_computations);
            simplify = (uu___168_2627.simplify);
            erase_universes = (uu___168_2627.erase_universes);
            allow_unbound_universes = (uu___168_2627.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___168_2627.compress_uvars);
            no_full_norm = (uu___168_2627.no_full_norm);
            check_no_uvars = (uu___168_2627.check_no_uvars);
            unmeta = (uu___168_2627.unmeta);
            unascribe = (uu___168_2627.unascribe);
            in_full_norm_request = (uu___168_2627.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___168_2627.weakly_reduce_scrutinee);
            nbe_step = (uu___168_2627.nbe_step);
            for_extraction = (uu___168_2627.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___171_2629 = fs  in
          {
            beta = (uu___171_2629.beta);
            iota = (uu___171_2629.iota);
            zeta = (uu___171_2629.zeta);
            weak = (uu___171_2629.weak);
            hnf = (uu___171_2629.hnf);
            primops = (uu___171_2629.primops);
            do_not_unfold_pure_lets = (uu___171_2629.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___171_2629.reduce_div_lets);
            unfold_until = (uu___171_2629.unfold_until);
            unfold_only = (uu___171_2629.unfold_only);
            unfold_fully = (uu___171_2629.unfold_fully);
            unfold_attr = (uu___171_2629.unfold_attr);
            unfold_tac = (uu___171_2629.unfold_tac);
            pure_subterms_within_computations =
              (uu___171_2629.pure_subterms_within_computations);
            simplify = (uu___171_2629.simplify);
            erase_universes = (uu___171_2629.erase_universes);
            allow_unbound_universes = (uu___171_2629.allow_unbound_universes);
            reify_ = (uu___171_2629.reify_);
            compress_uvars = true;
            no_full_norm = (uu___171_2629.no_full_norm);
            check_no_uvars = (uu___171_2629.check_no_uvars);
            unmeta = (uu___171_2629.unmeta);
            unascribe = (uu___171_2629.unascribe);
            in_full_norm_request = (uu___171_2629.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___171_2629.weakly_reduce_scrutinee);
            nbe_step = (uu___171_2629.nbe_step);
            for_extraction = (uu___171_2629.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___174_2631 = fs  in
          {
            beta = (uu___174_2631.beta);
            iota = (uu___174_2631.iota);
            zeta = (uu___174_2631.zeta);
            weak = (uu___174_2631.weak);
            hnf = (uu___174_2631.hnf);
            primops = (uu___174_2631.primops);
            do_not_unfold_pure_lets = (uu___174_2631.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___174_2631.reduce_div_lets);
            unfold_until = (uu___174_2631.unfold_until);
            unfold_only = (uu___174_2631.unfold_only);
            unfold_fully = (uu___174_2631.unfold_fully);
            unfold_attr = (uu___174_2631.unfold_attr);
            unfold_tac = (uu___174_2631.unfold_tac);
            pure_subterms_within_computations =
              (uu___174_2631.pure_subterms_within_computations);
            simplify = (uu___174_2631.simplify);
            erase_universes = (uu___174_2631.erase_universes);
            allow_unbound_universes = (uu___174_2631.allow_unbound_universes);
            reify_ = (uu___174_2631.reify_);
            compress_uvars = (uu___174_2631.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___174_2631.check_no_uvars);
            unmeta = (uu___174_2631.unmeta);
            unascribe = (uu___174_2631.unascribe);
            in_full_norm_request = (uu___174_2631.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___174_2631.weakly_reduce_scrutinee);
            nbe_step = (uu___174_2631.nbe_step);
            for_extraction = (uu___174_2631.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___177_2633 = fs  in
          {
            beta = (uu___177_2633.beta);
            iota = (uu___177_2633.iota);
            zeta = (uu___177_2633.zeta);
            weak = (uu___177_2633.weak);
            hnf = (uu___177_2633.hnf);
            primops = (uu___177_2633.primops);
            do_not_unfold_pure_lets = (uu___177_2633.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___177_2633.reduce_div_lets);
            unfold_until = (uu___177_2633.unfold_until);
            unfold_only = (uu___177_2633.unfold_only);
            unfold_fully = (uu___177_2633.unfold_fully);
            unfold_attr = (uu___177_2633.unfold_attr);
            unfold_tac = (uu___177_2633.unfold_tac);
            pure_subterms_within_computations =
              (uu___177_2633.pure_subterms_within_computations);
            simplify = (uu___177_2633.simplify);
            erase_universes = (uu___177_2633.erase_universes);
            allow_unbound_universes = (uu___177_2633.allow_unbound_universes);
            reify_ = (uu___177_2633.reify_);
            compress_uvars = (uu___177_2633.compress_uvars);
            no_full_norm = (uu___177_2633.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___177_2633.unmeta);
            unascribe = (uu___177_2633.unascribe);
            in_full_norm_request = (uu___177_2633.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___177_2633.weakly_reduce_scrutinee);
            nbe_step = (uu___177_2633.nbe_step);
            for_extraction = (uu___177_2633.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___180_2635 = fs  in
          {
            beta = (uu___180_2635.beta);
            iota = (uu___180_2635.iota);
            zeta = (uu___180_2635.zeta);
            weak = (uu___180_2635.weak);
            hnf = (uu___180_2635.hnf);
            primops = (uu___180_2635.primops);
            do_not_unfold_pure_lets = (uu___180_2635.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___180_2635.reduce_div_lets);
            unfold_until = (uu___180_2635.unfold_until);
            unfold_only = (uu___180_2635.unfold_only);
            unfold_fully = (uu___180_2635.unfold_fully);
            unfold_attr = (uu___180_2635.unfold_attr);
            unfold_tac = (uu___180_2635.unfold_tac);
            pure_subterms_within_computations =
              (uu___180_2635.pure_subterms_within_computations);
            simplify = (uu___180_2635.simplify);
            erase_universes = (uu___180_2635.erase_universes);
            allow_unbound_universes = (uu___180_2635.allow_unbound_universes);
            reify_ = (uu___180_2635.reify_);
            compress_uvars = (uu___180_2635.compress_uvars);
            no_full_norm = (uu___180_2635.no_full_norm);
            check_no_uvars = (uu___180_2635.check_no_uvars);
            unmeta = true;
            unascribe = (uu___180_2635.unascribe);
            in_full_norm_request = (uu___180_2635.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___180_2635.weakly_reduce_scrutinee);
            nbe_step = (uu___180_2635.nbe_step);
            for_extraction = (uu___180_2635.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___183_2637 = fs  in
          {
            beta = (uu___183_2637.beta);
            iota = (uu___183_2637.iota);
            zeta = (uu___183_2637.zeta);
            weak = (uu___183_2637.weak);
            hnf = (uu___183_2637.hnf);
            primops = (uu___183_2637.primops);
            do_not_unfold_pure_lets = (uu___183_2637.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___183_2637.reduce_div_lets);
            unfold_until = (uu___183_2637.unfold_until);
            unfold_only = (uu___183_2637.unfold_only);
            unfold_fully = (uu___183_2637.unfold_fully);
            unfold_attr = (uu___183_2637.unfold_attr);
            unfold_tac = (uu___183_2637.unfold_tac);
            pure_subterms_within_computations =
              (uu___183_2637.pure_subterms_within_computations);
            simplify = (uu___183_2637.simplify);
            erase_universes = (uu___183_2637.erase_universes);
            allow_unbound_universes = (uu___183_2637.allow_unbound_universes);
            reify_ = (uu___183_2637.reify_);
            compress_uvars = (uu___183_2637.compress_uvars);
            no_full_norm = (uu___183_2637.no_full_norm);
            check_no_uvars = (uu___183_2637.check_no_uvars);
            unmeta = (uu___183_2637.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___183_2637.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___183_2637.weakly_reduce_scrutinee);
            nbe_step = (uu___183_2637.nbe_step);
            for_extraction = (uu___183_2637.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___186_2639 = fs  in
          {
            beta = (uu___186_2639.beta);
            iota = (uu___186_2639.iota);
            zeta = (uu___186_2639.zeta);
            weak = (uu___186_2639.weak);
            hnf = (uu___186_2639.hnf);
            primops = (uu___186_2639.primops);
            do_not_unfold_pure_lets = (uu___186_2639.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___186_2639.reduce_div_lets);
            unfold_until = (uu___186_2639.unfold_until);
            unfold_only = (uu___186_2639.unfold_only);
            unfold_fully = (uu___186_2639.unfold_fully);
            unfold_attr = (uu___186_2639.unfold_attr);
            unfold_tac = (uu___186_2639.unfold_tac);
            pure_subterms_within_computations =
              (uu___186_2639.pure_subterms_within_computations);
            simplify = (uu___186_2639.simplify);
            erase_universes = (uu___186_2639.erase_universes);
            allow_unbound_universes = (uu___186_2639.allow_unbound_universes);
            reify_ = (uu___186_2639.reify_);
            compress_uvars = (uu___186_2639.compress_uvars);
            no_full_norm = (uu___186_2639.no_full_norm);
            check_no_uvars = (uu___186_2639.check_no_uvars);
            unmeta = (uu___186_2639.unmeta);
            unascribe = (uu___186_2639.unascribe);
            in_full_norm_request = (uu___186_2639.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___186_2639.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___186_2639.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___189_2641 = fs  in
          {
            beta = (uu___189_2641.beta);
            iota = (uu___189_2641.iota);
            zeta = (uu___189_2641.zeta);
            weak = (uu___189_2641.weak);
            hnf = (uu___189_2641.hnf);
            primops = (uu___189_2641.primops);
            do_not_unfold_pure_lets = (uu___189_2641.do_not_unfold_pure_lets);
            reduce_div_lets = (uu___189_2641.reduce_div_lets);
            unfold_until = (uu___189_2641.unfold_until);
            unfold_only = (uu___189_2641.unfold_only);
            unfold_fully = (uu___189_2641.unfold_fully);
            unfold_attr = (uu___189_2641.unfold_attr);
            unfold_tac = (uu___189_2641.unfold_tac);
            pure_subterms_within_computations =
              (uu___189_2641.pure_subterms_within_computations);
            simplify = (uu___189_2641.simplify);
            erase_universes = (uu___189_2641.erase_universes);
            allow_unbound_universes = (uu___189_2641.allow_unbound_universes);
            reify_ = (uu___189_2641.reify_);
            compress_uvars = (uu___189_2641.compress_uvars);
            no_full_norm = (uu___189_2641.no_full_norm);
            check_no_uvars = (uu___189_2641.check_no_uvars);
            unmeta = (uu___189_2641.unmeta);
            unascribe = (uu___189_2641.unascribe);
            in_full_norm_request = (uu___189_2641.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___189_2641.weakly_reduce_scrutinee);
            nbe_step = (uu___189_2641.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____2699  -> []) } 
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
  print_normalized: Prims.bool ;
  debug_nbe: Prims.bool }
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> gen1
  
let (__proj__Mkdebug_switches__item__top : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> top
  
let (__proj__Mkdebug_switches__item__cfg : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> cfg
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> primop
  
let (__proj__Mkdebug_switches__item__unfolding :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> unfolding
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> b380
  
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> wpe
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> print_normalized
  
let (__proj__Mkdebug_switches__item__debug_nbe :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> debug_nbe
  
let (no_debug_switches : debug_switches) =
  {
    gen = false;
    top = false;
    cfg = false;
    primop = false;
    unfolding = false;
    b380 = false;
    wpe = false;
    norm_delayed = false;
    print_normalized = false;
    debug_nbe = false
  } 
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
  
type prim_step_set = primitive_step FStar_Util.psmap
let (empty_prim_steps : unit -> prim_step_set) =
  fun uu____3535  -> FStar_Util.psmap_empty () 
let (add_step :
  primitive_step -> prim_step_set -> primitive_step FStar_Util.psmap) =
  fun s  ->
    fun ss  ->
      let uu____3549 = FStar_Ident.text_of_lid s.name  in
      FStar_Util.psmap_add ss uu____3549 s
  
let (merge_steps : prim_step_set -> prim_step_set -> prim_step_set) =
  fun s1  -> fun s2  -> FStar_Util.psmap_merge s1 s2 
let (add_steps : prim_step_set -> primitive_step Prims.list -> prim_step_set)
  = fun m  -> fun l  -> FStar_List.fold_right add_step l m 
let (prim_from_list : primitive_step Prims.list -> prim_step_set) =
  fun l  -> let uu____3587 = empty_prim_steps ()  in add_steps uu____3587 l 
type cfg =
  {
  steps: fsteps ;
  tcenv: FStar_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: prim_step_set ;
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
  
let (__proj__Mkcfg__item__primitive_steps : cfg -> prim_step_set) =
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
    let uu____3847 =
      let uu____3851 =
        let uu____3855 =
          let uu____3857 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____3857  in
        [uu____3855; "}"]  in
      "{" :: uu____3851  in
    FStar_String.concat "\n" uu____3847
  
let (cfg_env : cfg -> FStar_TypeChecker_Env.env) = fun cfg  -> cfg.tcenv 
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____3886 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____3886
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____3900 =
        let uu____3903 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____3903  in
      FStar_Util.is_some uu____3900
  
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
  fun cfg  -> fun f  -> if (cfg.debug).debug_nbe then f () else () 
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____4048 = FStar_Syntax_Embeddings.embed emb x  in
        uu____4048 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____4081 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____4081 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____4096 .
    'Auu____4096 ->
      FStar_Range.range -> 'Auu____4096 FStar_Syntax_Syntax.syntax
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
    let uu____4215 =
      let uu____4224 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____4224  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4215  in
  let arg_as_bounded_int1 uu____4254 =
    match uu____4254 with
    | (a,uu____4268) ->
        let uu____4279 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____4279 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____4323 =
               let uu____4338 =
                 let uu____4339 = FStar_Syntax_Subst.compress hd1  in
                 uu____4339.FStar_Syntax_Syntax.n  in
               (uu____4338, args)  in
             (match uu____4323 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____4360)::[]) when
                  let uu____4395 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____4395 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____4399 =
                    let uu____4400 = FStar_Syntax_Subst.compress arg1  in
                    uu____4400.FStar_Syntax_Syntax.n  in
                  (match uu____4399 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____4422 =
                         let uu____4427 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____4427)  in
                       FStar_Pervasives_Native.Some uu____4422
                   | uu____4432 -> FStar_Pervasives_Native.None)
              | uu____4437 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4499 = f a  in FStar_Pervasives_Native.Some uu____4499
    | uu____4500 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4556 = f a0 a1  in FStar_Pervasives_Native.Some uu____4556
    | uu____4557 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____4624 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____4624  in
  let binary_op1 as_a f res n1 args =
    let uu____4706 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____4706  in
  let as_primitive_step is_strong uu____4761 =
    match uu____4761 with
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
           let uu____4869 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____4869)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4911 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____4911)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____4952 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____4952)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____5005 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____5005)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____5058 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____5058)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____5211 =
          let uu____5220 = as_a a  in
          let uu____5223 = as_b b  in (uu____5220, uu____5223)  in
        (match uu____5211 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5238 =
               let uu____5239 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5239  in
             FStar_Pervasives_Native.Some uu____5238
         | uu____5240 -> FStar_Pervasives_Native.None)
    | uu____5249 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____5271 =
        let uu____5272 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5272  in
      mk uu____5271 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5286 =
      let uu____5289 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5289  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5286  in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5337 =
      let uu____5338 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5338  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____5337  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____5424 = arg_as_string1 a1  in
        (match uu____5424 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5433 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____5433 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5451 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____5451
              | uu____5453 -> FStar_Pervasives_Native.None)
         | uu____5459 -> FStar_Pervasives_Native.None)
    | uu____5463 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5544 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____5544 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5560 = arg_as_string1 a2  in
             (match uu____5560 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____5573 =
                    let uu____5574 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____5574 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5573
              | uu____5584 -> FStar_Pervasives_Native.None)
         | uu____5588 -> FStar_Pervasives_Native.None)
    | uu____5594 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____5632 =
          let uu____5646 = arg_as_string1 a1  in
          let uu____5650 = arg_as_int1 a2  in
          let uu____5653 = arg_as_int1 a3  in
          (uu____5646, uu____5650, uu____5653)  in
        (match uu____5632 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___512_5686  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____5691 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5691) ()
              with | uu___511_5694 -> FStar_Pervasives_Native.None)
         | uu____5697 -> FStar_Pervasives_Native.None)
    | uu____5711 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5725 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____5725  in
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
        let uu____5804 =
          let uu____5814 = arg_as_string1 a1  in
          let uu____5818 = arg_as_int1 a2  in (uu____5814, uu____5818)  in
        (match uu____5804 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___546_5842  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____5847 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5847) ()
              with | uu___545_5850 -> FStar_Pervasives_Native.None)
         | uu____5853 -> FStar_Pervasives_Native.None)
    | uu____5863 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5894 =
          let uu____5905 = arg_as_string1 a1  in
          let uu____5909 = arg_as_char1 a2  in (uu____5905, uu____5909)  in
        (match uu____5894 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___567_5938  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____5942 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5942) ()
              with | uu___566_5944 -> FStar_Pervasives_Native.None)
         | uu____5947 -> FStar_Pervasives_Native.None)
    | uu____5958 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5992 =
          let uu____6014 = arg_as_string1 fn  in
          let uu____6018 = arg_as_int1 from_line  in
          let uu____6021 = arg_as_int1 from_col  in
          let uu____6024 = arg_as_int1 to_line  in
          let uu____6027 = arg_as_int1 to_col  in
          (uu____6014, uu____6018, uu____6021, uu____6024, uu____6027)  in
        (match uu____5992 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6062 =
                 let uu____6063 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6065 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6063 uu____6065  in
               let uu____6067 =
                 let uu____6068 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6070 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6068 uu____6070  in
               FStar_Range.mk_range fn1 uu____6062 uu____6067  in
             let uu____6072 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6072
         | uu____6073 -> FStar_Pervasives_Native.None)
    | uu____6095 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6139)::(a1,uu____6141)::(a2,uu____6143)::[] ->
        let uu____6200 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6200 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6209 -> FStar_Pervasives_Native.None)
    | uu____6210 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____6253)::[] ->
        let uu____6270 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____6270 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6276 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6276
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6277 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____6297  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____6331 =
      let uu____6361 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, Prims.int_one, Prims.int_zero,
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)), uu____6361)
       in
    let uu____6395 =
      let uu____6427 =
        let uu____6457 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.of_int (2)), Prims.int_zero,
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____6457)
         in
      let uu____6497 =
        let uu____6529 =
          let uu____6559 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.of_int (2)),
            Prims.int_zero,
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____6559)
           in
        let uu____6599 =
          let uu____6631 =
            let uu____6661 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.of_int (2)),
              Prims.int_zero,
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____6661)
             in
          let uu____6701 =
            let uu____6733 =
              let uu____6763 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.of_int (2)),
                Prims.int_zero,
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____6763)
               in
            let uu____6803 =
              let uu____6835 =
                let uu____6865 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____6877 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____6877)
                   in
                (FStar_Parser_Const.op_LT, (Prims.of_int (2)),
                  Prims.int_zero,
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____6908 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____6908)), uu____6865)
                 in
              let uu____6911 =
                let uu____6943 =
                  let uu____6973 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____6985 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____6985)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.of_int (2)),
                    Prims.int_zero,
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____7016 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____7016)), uu____6973)
                   in
                let uu____7019 =
                  let uu____7051 =
                    let uu____7081 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____7093 = FStar_BigInt.gt_big_int x y  in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____7093)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.of_int (2)),
                      Prims.int_zero,
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____7124 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____7124)), uu____7081)
                     in
                  let uu____7127 =
                    let uu____7159 =
                      let uu____7189 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____7201 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____7201)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.of_int (2)),
                        Prims.int_zero,
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____7232 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____7232)), uu____7189)
                       in
                    let uu____7235 =
                      let uu____7267 =
                        let uu____7297 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus, (Prims.of_int (2)),
                          Prims.int_zero,
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____7297)
                         in
                      let uu____7337 =
                        let uu____7369 =
                          let uu____7399 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation, Prims.int_one,
                            Prims.int_zero,
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____7399)
                           in
                        let uu____7435 =
                          let uu____7467 =
                            let uu____7497 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And, (Prims.of_int (2)),
                              Prims.int_zero,
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____7497)
                             in
                          let uu____7541 =
                            let uu____7573 =
                              let uu____7603 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or, (Prims.of_int (2)),
                                Prims.int_zero,
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____7603)
                               in
                            let uu____7647 =
                              let uu____7679 =
                                let uu____7709 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  Prims.int_one, Prims.int_zero,
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____7709)
                                 in
                              let uu____7737 =
                                let uu____7769 =
                                  let uu____7799 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    Prims.int_one, Prims.int_zero,
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____7799)
                                   in
                                let uu____7829 =
                                  let uu____7861 =
                                    let uu____7891 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      Prims.int_one, Prims.int_zero,
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____7891)
                                     in
                                  let uu____7921 =
                                    let uu____7953 =
                                      let uu____7983 =
                                        FStar_TypeChecker_NBETerm.unary_op
                                          (FStar_TypeChecker_NBETerm.arg_as_list
                                             FStar_TypeChecker_NBETerm.e_char)
                                          FStar_TypeChecker_NBETerm.string_of_list'
                                         in
                                      (FStar_Parser_Const.string_string_of_list_lid,
                                        Prims.int_one, Prims.int_zero,
                                        (unary_op1
                                           (arg_as_list1
                                              FStar_Syntax_Embeddings.e_char)
                                           string_of_list'1), uu____7983)
                                       in
                                    let uu____8019 =
                                      let uu____8051 =
                                        let uu____8083 =
                                          let uu____8115 =
                                            let uu____8145 =
                                              FStar_TypeChecker_NBETerm.binary_string_op
                                                (fun x  ->
                                                   fun y  ->
                                                     FStar_String.op_Hat x y)
                                               in
                                            (FStar_Parser_Const.prims_strcat_lid,
                                              (Prims.of_int (2)),
                                              Prims.int_zero,
                                              (binary_string_op1
                                                 (fun x  ->
                                                    fun y  ->
                                                      FStar_String.op_Hat x y)),
                                              uu____8145)
                                             in
                                          let uu____8189 =
                                            let uu____8221 =
                                              let uu____8253 =
                                                let uu____8283 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.of_int (2)),
                                                  Prims.int_zero,
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____8283)
                                                 in
                                              let uu____8313 =
                                                let uu____8345 =
                                                  let uu____8375 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    Prims.int_one,
                                                    Prims.int_zero,
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____8375)
                                                   in
                                                let uu____8405 =
                                                  let uu____8437 =
                                                    let uu____8467 =
                                                      FStar_TypeChecker_NBETerm.unary_op
                                                        FStar_TypeChecker_NBETerm.arg_as_string
                                                        FStar_TypeChecker_NBETerm.string_uppercase
                                                       in
                                                    (FStar_Parser_Const.string_uppercase_lid,
                                                      Prims.int_one,
                                                      Prims.int_zero,
                                                      (unary_op1
                                                         arg_as_string1
                                                         uppercase1),
                                                      uu____8467)
                                                     in
                                                  let uu____8497 =
                                                    let uu____8529 =
                                                      let uu____8561 =
                                                        let uu____8593 =
                                                          let uu____8625 =
                                                            let uu____8657 =
                                                              let uu____8689
                                                                =
                                                                let uu____8719
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____8719,
                                                                  (Prims.of_int (5)),
                                                                  Prims.int_zero,
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____8746
                                                                =
                                                                let uu____8778
                                                                  =
                                                                  let uu____8808
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____8808,
                                                                    Prims.int_one,
                                                                    Prims.int_zero,
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____8778]
                                                                 in
                                                              uu____8689 ::
                                                                uu____8746
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.of_int (3)),
                                                              Prims.int_zero,
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____8657
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.of_int (3)),
                                                            Prims.int_zero,
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____8625
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.of_int (3)),
                                                          Prims.int_zero,
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____8593
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.of_int (2)),
                                                        Prims.int_zero,
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____8561
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.of_int (2)),
                                                      Prims.int_zero,
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____8529
                                                     in
                                                  uu____8437 :: uu____8497
                                                   in
                                                uu____8345 :: uu____8405  in
                                              uu____8253 :: uu____8313  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.of_int (2)),
                                              Prims.int_zero,
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____8221
                                             in
                                          uu____8115 :: uu____8189  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.of_int (2)), Prims.int_zero,
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____8083
                                         in
                                      (FStar_Parser_Const.string_make_lid,
                                        (Prims.of_int (2)), Prims.int_zero,
                                        (mixed_binary_op1 arg_as_int1
                                           arg_as_char1
                                           (embed_simple
                                              FStar_Syntax_Embeddings.e_string)
                                           (fun r  ->
                                              fun x  ->
                                                fun y  ->
                                                  let uu____9455 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____9455 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____9466 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____9466
                                                  y)))
                                        :: uu____8051
                                       in
                                    uu____7953 :: uu____8019  in
                                  uu____7861 :: uu____7921  in
                                uu____7769 :: uu____7829  in
                              uu____7679 :: uu____7737  in
                            uu____7573 :: uu____7647  in
                          uu____7467 :: uu____7541  in
                        uu____7369 :: uu____7435  in
                      uu____7267 :: uu____7337  in
                    uu____7159 :: uu____7235  in
                  uu____7051 :: uu____7127  in
                uu____6943 :: uu____7019  in
              uu____6835 :: uu____6911  in
            uu____6733 :: uu____6803  in
          uu____6631 :: uu____6701  in
        uu____6529 :: uu____6599  in
      uu____6427 :: uu____6497  in
    uu____6331 :: uu____6395  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____10102 =
        let uu____10107 =
          let uu____10108 = FStar_Syntax_Syntax.as_arg c  in [uu____10108]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____10107  in
      uu____10102 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____10235 =
                let uu____10265 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____10272 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10290  ->
                       fun uu____10291  ->
                         match (uu____10290, uu____10291) with
                         | ((int_to_t1,x),(uu____10310,y)) ->
                             let uu____10320 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____10320)
                   in
                (uu____10265, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____10355  ->
                          fun uu____10356  ->
                            match (uu____10355, uu____10356) with
                            | ((int_to_t1,x),(uu____10375,y)) ->
                                let uu____10385 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____10385)),
                  uu____10272)
                 in
              let uu____10386 =
                let uu____10418 =
                  let uu____10448 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____10455 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____10473  ->
                         fun uu____10474  ->
                           match (uu____10473, uu____10474) with
                           | ((int_to_t1,x),(uu____10493,y)) ->
                               let uu____10503 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____10503)
                     in
                  (uu____10448, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____10538  ->
                            fun uu____10539  ->
                              match (uu____10538, uu____10539) with
                              | ((int_to_t1,x),(uu____10558,y)) ->
                                  let uu____10568 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____10568)),
                    uu____10455)
                   in
                let uu____10569 =
                  let uu____10601 =
                    let uu____10631 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____10638 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____10656  ->
                           fun uu____10657  ->
                             match (uu____10656, uu____10657) with
                             | ((int_to_t1,x),(uu____10676,y)) ->
                                 let uu____10686 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____10686)
                       in
                    (uu____10631, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____10721  ->
                              fun uu____10722  ->
                                match (uu____10721, uu____10722) with
                                | ((int_to_t1,x),(uu____10741,y)) ->
                                    let uu____10751 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____10751)),
                      uu____10638)
                     in
                  let uu____10752 =
                    let uu____10784 =
                      let uu____10814 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____10821 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____10835  ->
                             match uu____10835 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____10814, Prims.int_one, Prims.int_zero,
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____10872  ->
                                match uu____10872 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____10821)
                       in
                    [uu____10784]  in
                  uu____10601 :: uu____10752  in
                uu____10418 :: uu____10569  in
              uu____10235 :: uu____10386))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____11125 =
                let uu____11155 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____11162 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11180  ->
                       fun uu____11181  ->
                         match (uu____11180, uu____11181) with
                         | ((int_to_t1,x),(uu____11200,y)) ->
                             let uu____11210 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11210)
                   in
                (uu____11155, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11245  ->
                          fun uu____11246  ->
                            match (uu____11245, uu____11246) with
                            | ((int_to_t1,x),(uu____11265,y)) ->
                                let uu____11275 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11275)),
                  uu____11162)
                 in
              let uu____11276 =
                let uu____11308 =
                  let uu____11338 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____11345 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11363  ->
                         fun uu____11364  ->
                           match (uu____11363, uu____11364) with
                           | ((int_to_t1,x),(uu____11383,y)) ->
                               let uu____11393 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11393)
                     in
                  (uu____11338, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11428  ->
                            fun uu____11429  ->
                              match (uu____11428, uu____11429) with
                              | ((int_to_t1,x),(uu____11448,y)) ->
                                  let uu____11458 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11458)),
                    uu____11345)
                   in
                [uu____11308]  in
              uu____11125 :: uu____11276))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____11564 ->
          let uu____11566 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____11566
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____11670 =
                let uu____11700 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____11707 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11725  ->
                       fun uu____11726  ->
                         match (uu____11725, uu____11726) with
                         | ((int_to_t1,x),(uu____11745,y)) ->
                             let uu____11755 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11755)
                   in
                (uu____11700, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11790  ->
                          fun uu____11791  ->
                            match (uu____11790, uu____11791) with
                            | ((int_to_t1,x),(uu____11810,y)) ->
                                let uu____11820 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11820)),
                  uu____11707)
                 in
              let uu____11821 =
                let uu____11853 =
                  let uu____11883 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____11890 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11908  ->
                         fun uu____11909  ->
                           match (uu____11908, uu____11909) with
                           | ((int_to_t1,x),(uu____11928,y)) ->
                               let uu____11938 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11938)
                     in
                  (uu____11883, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11973  ->
                            fun uu____11974  ->
                              match (uu____11973, uu____11974) with
                              | ((int_to_t1,x),(uu____11993,y)) ->
                                  let uu____12003 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____12003)),
                    uu____11890)
                   in
                let uu____12004 =
                  let uu____12036 =
                    let uu____12066 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____12073 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____12091  ->
                           fun uu____12092  ->
                             match (uu____12091, uu____12092) with
                             | ((int_to_t1,x),(uu____12111,y)) ->
                                 let uu____12121 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____12121)
                       in
                    (uu____12066, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____12156  ->
                              fun uu____12157  ->
                                match (uu____12156, uu____12157) with
                                | ((int_to_t1,x),(uu____12176,y)) ->
                                    let uu____12186 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____12186)),
                      uu____12073)
                     in
                  let uu____12187 =
                    let uu____12219 =
                      let uu____12249 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____12256 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____12271  ->
                             match uu____12271 with
                             | (int_to_t1,x) ->
                                 let uu____12278 =
                                   let uu____12279 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____12280 = mask m  in
                                   FStar_BigInt.logand_big_int uu____12279
                                     uu____12280
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____12278)
                         in
                      (uu____12249, Prims.int_one, Prims.int_zero,
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____12312  ->
                                match uu____12312 with
                                | (int_to_t1,x) ->
                                    let uu____12319 =
                                      let uu____12320 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____12321 = mask m  in
                                      FStar_BigInt.logand_big_int uu____12320
                                        uu____12321
                                       in
                                    int_as_bounded1 r int_to_t1 uu____12319)),
                        uu____12256)
                       in
                    let uu____12322 =
                      let uu____12354 =
                        let uu____12384 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____12391 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____12409  ->
                               fun uu____12410  ->
                                 match (uu____12409, uu____12410) with
                                 | ((int_to_t1,x),(uu____12429,y)) ->
                                     let uu____12439 =
                                       let uu____12440 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____12441 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____12440 uu____12441
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____12439)
                           in
                        (uu____12384, (Prims.of_int (2)), Prims.int_zero,
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____12476  ->
                                  fun uu____12477  ->
                                    match (uu____12476, uu____12477) with
                                    | ((int_to_t1,x),(uu____12496,y)) ->
                                        let uu____12506 =
                                          let uu____12507 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____12508 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____12507 uu____12508
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____12506)), uu____12391)
                         in
                      let uu____12509 =
                        let uu____12541 =
                          let uu____12571 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____12578 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____12596  ->
                                 fun uu____12597  ->
                                   match (uu____12596, uu____12597) with
                                   | ((int_to_t1,x),(uu____12616,y)) ->
                                       let uu____12626 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____12626)
                             in
                          (uu____12571, (Prims.of_int (2)), Prims.int_zero,
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____12661  ->
                                    fun uu____12662  ->
                                      match (uu____12661, uu____12662) with
                                      | ((int_to_t1,x),(uu____12681,y)) ->
                                          let uu____12691 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____12691)), uu____12578)
                           in
                        [uu____12541]  in
                      uu____12354 :: uu____12509  in
                    uu____12219 :: uu____12322  in
                  uu____12036 :: uu____12187  in
                uu____11853 :: uu____12004  in
              uu____11670 :: uu____11821))
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
    | (_typ,uu____13079)::(a1,uu____13081)::(a2,uu____13083)::[] ->
        let uu____13140 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____13140 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___887_13144 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___887_13144.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___887_13144.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___890_13146 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___890_13146.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___890_13146.FStar_Syntax_Syntax.vars)
                })
         | uu____13147 -> FStar_Pervasives_Native.None)
    | uu____13148 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____13178)::(t2,uu____13180)::(a1,uu____13182)::(a2,uu____13184)::[]
        ->
        let uu____13257 =
          let uu____13258 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____13259 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____13258 uu____13259  in
        (match uu____13257 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___913_13263 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___913_13263.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___913_13263.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___916_13265 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___916_13265.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___916_13265.FStar_Syntax_Syntax.vars)
                })
         | uu____13266 -> FStar_Pervasives_Native.None)
    | uu____13267 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.of_int (3));
      univ_arity = Prims.int_one;
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
      arity = (Prims.of_int (4));
      univ_arity = (Prims.of_int (2));
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop_eq31;
      interpretation_nbe =
        (fun _cb  -> FStar_TypeChecker_NBETerm.interp_prop_eq3)
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (primop_time_map : Prims.int FStar_Util.smap) =
  FStar_Util.smap_create (Prims.of_int (50)) 
let (primop_time_reset : unit -> unit) =
  fun uu____13298  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____13315 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____13315 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____13344 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____13344 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____13355  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____13426  ->
           fun uu____13427  ->
             match (uu____13426, uu____13427) with
             | ((uu____13453,t1),(uu____13455,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____13489  ->
         fun rest  ->
           match uu____13489 with
           | (nm,ms) ->
               let uu____13505 =
                 let uu____13507 =
                   let uu____13509 = FStar_Util.string_of_int ms  in
                   fixto (Prims.of_int (10)) uu____13509  in
                 FStar_Util.format2 "%sms --- %s\n" uu____13507 nm  in
               FStar_String.op_Hat uu____13505 rest) pairs1 ""
  
let (extendable_primops_dirty : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref true 
type register_prim_step_t = primitive_step -> unit
type retrieve_prim_step_t = unit -> prim_step_set
let (mk_extendable_primop_set :
  unit -> (register_prim_step_t * retrieve_prim_step_t)) =
  fun uu____13537  ->
    let steps =
      let uu____13547 = empty_prim_steps ()  in FStar_Util.mk_ref uu____13547
       in
    let register p =
      FStar_ST.op_Colon_Equals extendable_primops_dirty true;
      (let uu____13577 =
         let uu____13578 = FStar_ST.op_Bang steps  in add_step p uu____13578
          in
       FStar_ST.op_Colon_Equals steps uu____13577)
       in
    let retrieve uu____13622 = FStar_ST.op_Bang steps  in
    (register, retrieve)
  
let (plugins : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set () 
let (extra_steps : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set () 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> prim_step_set) =
  fun uu____13671  ->
    let uu____13672 = FStar_Options.no_plugins ()  in
    if uu____13672
    then empty_prim_steps ()
    else FStar_Pervasives_Native.snd plugins ()
  
let (register_extra_step : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst extra_steps p 
let (retrieve_extra_steps : unit -> prim_step_set) =
  fun uu____13692  -> FStar_Pervasives_Native.snd extra_steps () 
let (cached_steps : unit -> prim_step_set) =
  let memo =
    let uu____13703 = empty_prim_steps ()  in FStar_Util.mk_ref uu____13703
     in
  fun uu____13704  ->
    let uu____13705 = FStar_ST.op_Bang extendable_primops_dirty  in
    if uu____13705
    then
      let steps =
        let uu____13730 =
          let uu____13731 = retrieve_plugins ()  in
          let uu____13732 = retrieve_extra_steps ()  in
          merge_steps uu____13731 uu____13732  in
        merge_steps built_in_primitive_steps uu____13730  in
      (FStar_ST.op_Colon_Equals memo steps;
       FStar_ST.op_Colon_Equals extendable_primops_dirty false;
       steps)
    else FStar_ST.op_Bang memo
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____13803 = FStar_Options.use_nbe ()  in
    if uu____13803
    then
      let uu___969_13806 = s  in
      {
        beta = (uu___969_13806.beta);
        iota = (uu___969_13806.iota);
        zeta = (uu___969_13806.zeta);
        weak = (uu___969_13806.weak);
        hnf = (uu___969_13806.hnf);
        primops = (uu___969_13806.primops);
        do_not_unfold_pure_lets = (uu___969_13806.do_not_unfold_pure_lets);
        reduce_div_lets = (uu___969_13806.reduce_div_lets);
        unfold_until = (uu___969_13806.unfold_until);
        unfold_only = (uu___969_13806.unfold_only);
        unfold_fully = (uu___969_13806.unfold_fully);
        unfold_attr = (uu___969_13806.unfold_attr);
        unfold_tac = (uu___969_13806.unfold_tac);
        pure_subterms_within_computations =
          (uu___969_13806.pure_subterms_within_computations);
        simplify = (uu___969_13806.simplify);
        erase_universes = (uu___969_13806.erase_universes);
        allow_unbound_universes = (uu___969_13806.allow_unbound_universes);
        reify_ = (uu___969_13806.reify_);
        compress_uvars = (uu___969_13806.compress_uvars);
        no_full_norm = (uu___969_13806.no_full_norm);
        check_no_uvars = (uu___969_13806.check_no_uvars);
        unmeta = (uu___969_13806.unmeta);
        unascribe = (uu___969_13806.unascribe);
        in_full_norm_request = (uu___969_13806.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___969_13806.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___969_13806.for_extraction)
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
               (fun uu___0_13843  ->
                  match uu___0_13843 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____13847 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____13853 -> d  in
        let steps =
          let uu____13857 = to_fsteps s  in
          FStar_All.pipe_right uu____13857 add_nbe  in
        let psteps1 =
          let uu____13859 = cached_steps ()  in add_steps uu____13859 psteps
           in
        let uu____13860 =
          let uu____13861 = FStar_Options.debug_any ()  in
          if uu____13861
          then
            let uu____13864 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
            let uu____13867 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")
               in
            let uu____13870 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")
               in
            let uu____13873 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")
               in
            let uu____13876 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
               in
            let uu____13879 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
            let uu____13882 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
            let uu____13885 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "NormDelayed")
               in
            let uu____13888 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "print_normalized_terms")
               in
            let uu____13891 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NBE")  in
            {
              gen = uu____13864;
              top = uu____13867;
              cfg = uu____13870;
              primop = uu____13873;
              unfolding = uu____13876;
              b380 = uu____13879;
              wpe = uu____13882;
              norm_delayed = uu____13885;
              print_normalized = uu____13888;
              debug_nbe = uu____13891
            }
          else no_debug_switches  in
        let uu____13896 =
          (Prims.op_Negation steps.pure_subterms_within_computations) ||
            (FStar_Options.normalize_pure_terms_for_extraction ())
           in
        {
          steps;
          tcenv = e;
          debug = uu____13860;
          delta_level = d1;
          primitive_steps = psteps1;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____13896;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 
let (should_reduce_local_let :
  cfg -> FStar_Syntax_Syntax.letbinding -> Prims.bool) =
  fun cfg  ->
    fun lb  ->
      if (cfg.steps).do_not_unfold_pure_lets
      then false
      else
        (let uu____13933 =
           (cfg.steps).pure_subterms_within_computations &&
             (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs
                FStar_Parser_Const.inline_let_attr)
            in
         if uu____13933
         then true
         else
           (let n1 =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                lb.FStar_Syntax_Syntax.lbeff
               in
            let uu____13941 =
              (FStar_Syntax_Util.is_pure_effect n1) &&
                (cfg.normalize_pure_lets ||
                   (FStar_Syntax_Util.has_attribute
                      lb.FStar_Syntax_Syntax.lbattrs
                      FStar_Parser_Const.inline_let_attr))
               in
            if uu____13941
            then true
            else
              (FStar_Syntax_Util.is_ghost_effect n1) &&
                (Prims.op_Negation
                   (cfg.steps).pure_subterms_within_computations)))
  