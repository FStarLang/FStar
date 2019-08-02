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
          let uu____2099 =
            let uu____2101 = f1 x  in FStar_String.op_Hat uu____2101 ")"  in
          FStar_String.op_Hat "Some (" uu____2099
       in
    let b = FStar_Util.string_of_bool  in
    let uu____2112 =
      let uu____2116 = FStar_All.pipe_right f.beta b  in
      let uu____2120 =
        let uu____2124 = FStar_All.pipe_right f.iota b  in
        let uu____2128 =
          let uu____2132 = FStar_All.pipe_right f.zeta b  in
          let uu____2136 =
            let uu____2140 = FStar_All.pipe_right f.weak b  in
            let uu____2144 =
              let uu____2148 = FStar_All.pipe_right f.hnf b  in
              let uu____2152 =
                let uu____2156 = FStar_All.pipe_right f.primops b  in
                let uu____2160 =
                  let uu____2164 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____2168 =
                    let uu____2172 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____2177 =
                      let uu____2181 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____2195 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____2195
                                  (FStar_String.concat ", ")))
                         in
                      let uu____2205 =
                        let uu____2209 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____2223 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____2223
                                    (FStar_String.concat ", ")))
                           in
                        let uu____2233 =
                          let uu____2237 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____2251 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____2251
                                      (FStar_String.concat ", ")))
                             in
                          let uu____2261 =
                            let uu____2265 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____2269 =
                              let uu____2273 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____2277 =
                                let uu____2281 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____2285 =
                                  let uu____2289 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____2293 =
                                    let uu____2297 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____2301 =
                                      let uu____2305 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____2309 =
                                        let uu____2313 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____2317 =
                                          let uu____2321 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____2325 =
                                            let uu____2329 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____2333 =
                                              let uu____2337 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____2341 =
                                                let uu____2345 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____2349 =
                                                  let uu____2353 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____2357 =
                                                    let uu____2361 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____2361]  in
                                                  uu____2353 :: uu____2357
                                                   in
                                                uu____2345 :: uu____2349  in
                                              uu____2337 :: uu____2341  in
                                            uu____2329 :: uu____2333  in
                                          uu____2321 :: uu____2325  in
                                        uu____2313 :: uu____2317  in
                                      uu____2305 :: uu____2309  in
                                    uu____2297 :: uu____2301  in
                                  uu____2289 :: uu____2293  in
                                uu____2281 :: uu____2285  in
                              uu____2273 :: uu____2277  in
                            uu____2265 :: uu____2269  in
                          uu____2237 :: uu____2261  in
                        uu____2209 :: uu____2233  in
                      uu____2181 :: uu____2205  in
                    uu____2172 :: uu____2177  in
                  uu____2164 :: uu____2168  in
                uu____2156 :: uu____2160  in
              uu____2148 :: uu____2152  in
            uu____2140 :: uu____2144  in
          uu____2132 :: uu____2136  in
        uu____2124 :: uu____2128  in
      uu____2116 :: uu____2120  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____2112
  
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
          let uu___94_2431 = fs  in
          {
            beta = true;
            iota = (uu___94_2431.iota);
            zeta = (uu___94_2431.zeta);
            weak = (uu___94_2431.weak);
            hnf = (uu___94_2431.hnf);
            primops = (uu___94_2431.primops);
            do_not_unfold_pure_lets = (uu___94_2431.do_not_unfold_pure_lets);
            unfold_until = (uu___94_2431.unfold_until);
            unfold_only = (uu___94_2431.unfold_only);
            unfold_fully = (uu___94_2431.unfold_fully);
            unfold_attr = (uu___94_2431.unfold_attr);
            unfold_tac = (uu___94_2431.unfold_tac);
            pure_subterms_within_computations =
              (uu___94_2431.pure_subterms_within_computations);
            simplify = (uu___94_2431.simplify);
            erase_universes = (uu___94_2431.erase_universes);
            allow_unbound_universes = (uu___94_2431.allow_unbound_universes);
            reify_ = (uu___94_2431.reify_);
            compress_uvars = (uu___94_2431.compress_uvars);
            no_full_norm = (uu___94_2431.no_full_norm);
            check_no_uvars = (uu___94_2431.check_no_uvars);
            unmeta = (uu___94_2431.unmeta);
            unascribe = (uu___94_2431.unascribe);
            in_full_norm_request = (uu___94_2431.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___94_2431.weakly_reduce_scrutinee);
            nbe_step = (uu___94_2431.nbe_step);
            for_extraction = (uu___94_2431.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___97_2433 = fs  in
          {
            beta = (uu___97_2433.beta);
            iota = true;
            zeta = (uu___97_2433.zeta);
            weak = (uu___97_2433.weak);
            hnf = (uu___97_2433.hnf);
            primops = (uu___97_2433.primops);
            do_not_unfold_pure_lets = (uu___97_2433.do_not_unfold_pure_lets);
            unfold_until = (uu___97_2433.unfold_until);
            unfold_only = (uu___97_2433.unfold_only);
            unfold_fully = (uu___97_2433.unfold_fully);
            unfold_attr = (uu___97_2433.unfold_attr);
            unfold_tac = (uu___97_2433.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_2433.pure_subterms_within_computations);
            simplify = (uu___97_2433.simplify);
            erase_universes = (uu___97_2433.erase_universes);
            allow_unbound_universes = (uu___97_2433.allow_unbound_universes);
            reify_ = (uu___97_2433.reify_);
            compress_uvars = (uu___97_2433.compress_uvars);
            no_full_norm = (uu___97_2433.no_full_norm);
            check_no_uvars = (uu___97_2433.check_no_uvars);
            unmeta = (uu___97_2433.unmeta);
            unascribe = (uu___97_2433.unascribe);
            in_full_norm_request = (uu___97_2433.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___97_2433.weakly_reduce_scrutinee);
            nbe_step = (uu___97_2433.nbe_step);
            for_extraction = (uu___97_2433.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___100_2435 = fs  in
          {
            beta = (uu___100_2435.beta);
            iota = (uu___100_2435.iota);
            zeta = true;
            weak = (uu___100_2435.weak);
            hnf = (uu___100_2435.hnf);
            primops = (uu___100_2435.primops);
            do_not_unfold_pure_lets = (uu___100_2435.do_not_unfold_pure_lets);
            unfold_until = (uu___100_2435.unfold_until);
            unfold_only = (uu___100_2435.unfold_only);
            unfold_fully = (uu___100_2435.unfold_fully);
            unfold_attr = (uu___100_2435.unfold_attr);
            unfold_tac = (uu___100_2435.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_2435.pure_subterms_within_computations);
            simplify = (uu___100_2435.simplify);
            erase_universes = (uu___100_2435.erase_universes);
            allow_unbound_universes = (uu___100_2435.allow_unbound_universes);
            reify_ = (uu___100_2435.reify_);
            compress_uvars = (uu___100_2435.compress_uvars);
            no_full_norm = (uu___100_2435.no_full_norm);
            check_no_uvars = (uu___100_2435.check_no_uvars);
            unmeta = (uu___100_2435.unmeta);
            unascribe = (uu___100_2435.unascribe);
            in_full_norm_request = (uu___100_2435.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_2435.weakly_reduce_scrutinee);
            nbe_step = (uu___100_2435.nbe_step);
            for_extraction = (uu___100_2435.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___104_2437 = fs  in
          {
            beta = false;
            iota = (uu___104_2437.iota);
            zeta = (uu___104_2437.zeta);
            weak = (uu___104_2437.weak);
            hnf = (uu___104_2437.hnf);
            primops = (uu___104_2437.primops);
            do_not_unfold_pure_lets = (uu___104_2437.do_not_unfold_pure_lets);
            unfold_until = (uu___104_2437.unfold_until);
            unfold_only = (uu___104_2437.unfold_only);
            unfold_fully = (uu___104_2437.unfold_fully);
            unfold_attr = (uu___104_2437.unfold_attr);
            unfold_tac = (uu___104_2437.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_2437.pure_subterms_within_computations);
            simplify = (uu___104_2437.simplify);
            erase_universes = (uu___104_2437.erase_universes);
            allow_unbound_universes = (uu___104_2437.allow_unbound_universes);
            reify_ = (uu___104_2437.reify_);
            compress_uvars = (uu___104_2437.compress_uvars);
            no_full_norm = (uu___104_2437.no_full_norm);
            check_no_uvars = (uu___104_2437.check_no_uvars);
            unmeta = (uu___104_2437.unmeta);
            unascribe = (uu___104_2437.unascribe);
            in_full_norm_request = (uu___104_2437.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___104_2437.weakly_reduce_scrutinee);
            nbe_step = (uu___104_2437.nbe_step);
            for_extraction = (uu___104_2437.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___108_2439 = fs  in
          {
            beta = (uu___108_2439.beta);
            iota = false;
            zeta = (uu___108_2439.zeta);
            weak = (uu___108_2439.weak);
            hnf = (uu___108_2439.hnf);
            primops = (uu___108_2439.primops);
            do_not_unfold_pure_lets = (uu___108_2439.do_not_unfold_pure_lets);
            unfold_until = (uu___108_2439.unfold_until);
            unfold_only = (uu___108_2439.unfold_only);
            unfold_fully = (uu___108_2439.unfold_fully);
            unfold_attr = (uu___108_2439.unfold_attr);
            unfold_tac = (uu___108_2439.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_2439.pure_subterms_within_computations);
            simplify = (uu___108_2439.simplify);
            erase_universes = (uu___108_2439.erase_universes);
            allow_unbound_universes = (uu___108_2439.allow_unbound_universes);
            reify_ = (uu___108_2439.reify_);
            compress_uvars = (uu___108_2439.compress_uvars);
            no_full_norm = (uu___108_2439.no_full_norm);
            check_no_uvars = (uu___108_2439.check_no_uvars);
            unmeta = (uu___108_2439.unmeta);
            unascribe = (uu___108_2439.unascribe);
            in_full_norm_request = (uu___108_2439.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___108_2439.weakly_reduce_scrutinee);
            nbe_step = (uu___108_2439.nbe_step);
            for_extraction = (uu___108_2439.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___112_2441 = fs  in
          {
            beta = (uu___112_2441.beta);
            iota = (uu___112_2441.iota);
            zeta = false;
            weak = (uu___112_2441.weak);
            hnf = (uu___112_2441.hnf);
            primops = (uu___112_2441.primops);
            do_not_unfold_pure_lets = (uu___112_2441.do_not_unfold_pure_lets);
            unfold_until = (uu___112_2441.unfold_until);
            unfold_only = (uu___112_2441.unfold_only);
            unfold_fully = (uu___112_2441.unfold_fully);
            unfold_attr = (uu___112_2441.unfold_attr);
            unfold_tac = (uu___112_2441.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_2441.pure_subterms_within_computations);
            simplify = (uu___112_2441.simplify);
            erase_universes = (uu___112_2441.erase_universes);
            allow_unbound_universes = (uu___112_2441.allow_unbound_universes);
            reify_ = (uu___112_2441.reify_);
            compress_uvars = (uu___112_2441.compress_uvars);
            no_full_norm = (uu___112_2441.no_full_norm);
            check_no_uvars = (uu___112_2441.check_no_uvars);
            unmeta = (uu___112_2441.unmeta);
            unascribe = (uu___112_2441.unascribe);
            in_full_norm_request = (uu___112_2441.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___112_2441.weakly_reduce_scrutinee);
            nbe_step = (uu___112_2441.nbe_step);
            for_extraction = (uu___112_2441.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____2443 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___117_2445 = fs  in
          {
            beta = (uu___117_2445.beta);
            iota = (uu___117_2445.iota);
            zeta = (uu___117_2445.zeta);
            weak = true;
            hnf = (uu___117_2445.hnf);
            primops = (uu___117_2445.primops);
            do_not_unfold_pure_lets = (uu___117_2445.do_not_unfold_pure_lets);
            unfold_until = (uu___117_2445.unfold_until);
            unfold_only = (uu___117_2445.unfold_only);
            unfold_fully = (uu___117_2445.unfold_fully);
            unfold_attr = (uu___117_2445.unfold_attr);
            unfold_tac = (uu___117_2445.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_2445.pure_subterms_within_computations);
            simplify = (uu___117_2445.simplify);
            erase_universes = (uu___117_2445.erase_universes);
            allow_unbound_universes = (uu___117_2445.allow_unbound_universes);
            reify_ = (uu___117_2445.reify_);
            compress_uvars = (uu___117_2445.compress_uvars);
            no_full_norm = (uu___117_2445.no_full_norm);
            check_no_uvars = (uu___117_2445.check_no_uvars);
            unmeta = (uu___117_2445.unmeta);
            unascribe = (uu___117_2445.unascribe);
            in_full_norm_request = (uu___117_2445.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___117_2445.weakly_reduce_scrutinee);
            nbe_step = (uu___117_2445.nbe_step);
            for_extraction = (uu___117_2445.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___120_2447 = fs  in
          {
            beta = (uu___120_2447.beta);
            iota = (uu___120_2447.iota);
            zeta = (uu___120_2447.zeta);
            weak = (uu___120_2447.weak);
            hnf = true;
            primops = (uu___120_2447.primops);
            do_not_unfold_pure_lets = (uu___120_2447.do_not_unfold_pure_lets);
            unfold_until = (uu___120_2447.unfold_until);
            unfold_only = (uu___120_2447.unfold_only);
            unfold_fully = (uu___120_2447.unfold_fully);
            unfold_attr = (uu___120_2447.unfold_attr);
            unfold_tac = (uu___120_2447.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_2447.pure_subterms_within_computations);
            simplify = (uu___120_2447.simplify);
            erase_universes = (uu___120_2447.erase_universes);
            allow_unbound_universes = (uu___120_2447.allow_unbound_universes);
            reify_ = (uu___120_2447.reify_);
            compress_uvars = (uu___120_2447.compress_uvars);
            no_full_norm = (uu___120_2447.no_full_norm);
            check_no_uvars = (uu___120_2447.check_no_uvars);
            unmeta = (uu___120_2447.unmeta);
            unascribe = (uu___120_2447.unascribe);
            in_full_norm_request = (uu___120_2447.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___120_2447.weakly_reduce_scrutinee);
            nbe_step = (uu___120_2447.nbe_step);
            for_extraction = (uu___120_2447.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___123_2449 = fs  in
          {
            beta = (uu___123_2449.beta);
            iota = (uu___123_2449.iota);
            zeta = (uu___123_2449.zeta);
            weak = (uu___123_2449.weak);
            hnf = (uu___123_2449.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___123_2449.do_not_unfold_pure_lets);
            unfold_until = (uu___123_2449.unfold_until);
            unfold_only = (uu___123_2449.unfold_only);
            unfold_fully = (uu___123_2449.unfold_fully);
            unfold_attr = (uu___123_2449.unfold_attr);
            unfold_tac = (uu___123_2449.unfold_tac);
            pure_subterms_within_computations =
              (uu___123_2449.pure_subterms_within_computations);
            simplify = (uu___123_2449.simplify);
            erase_universes = (uu___123_2449.erase_universes);
            allow_unbound_universes = (uu___123_2449.allow_unbound_universes);
            reify_ = (uu___123_2449.reify_);
            compress_uvars = (uu___123_2449.compress_uvars);
            no_full_norm = (uu___123_2449.no_full_norm);
            check_no_uvars = (uu___123_2449.check_no_uvars);
            unmeta = (uu___123_2449.unmeta);
            unascribe = (uu___123_2449.unascribe);
            in_full_norm_request = (uu___123_2449.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___123_2449.weakly_reduce_scrutinee);
            nbe_step = (uu___123_2449.nbe_step);
            for_extraction = (uu___123_2449.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding uu____2451 -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___129_2453 = fs  in
          {
            beta = (uu___129_2453.beta);
            iota = (uu___129_2453.iota);
            zeta = (uu___129_2453.zeta);
            weak = (uu___129_2453.weak);
            hnf = (uu___129_2453.hnf);
            primops = (uu___129_2453.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___129_2453.unfold_until);
            unfold_only = (uu___129_2453.unfold_only);
            unfold_fully = (uu___129_2453.unfold_fully);
            unfold_attr = (uu___129_2453.unfold_attr);
            unfold_tac = (uu___129_2453.unfold_tac);
            pure_subterms_within_computations =
              (uu___129_2453.pure_subterms_within_computations);
            simplify = (uu___129_2453.simplify);
            erase_universes = (uu___129_2453.erase_universes);
            allow_unbound_universes = (uu___129_2453.allow_unbound_universes);
            reify_ = (uu___129_2453.reify_);
            compress_uvars = (uu___129_2453.compress_uvars);
            no_full_norm = (uu___129_2453.no_full_norm);
            check_no_uvars = (uu___129_2453.check_no_uvars);
            unmeta = (uu___129_2453.unmeta);
            unascribe = (uu___129_2453.unascribe);
            in_full_norm_request = (uu___129_2453.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___129_2453.weakly_reduce_scrutinee);
            nbe_step = (uu___129_2453.nbe_step);
            for_extraction = (uu___129_2453.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___133_2456 = fs  in
          {
            beta = (uu___133_2456.beta);
            iota = (uu___133_2456.iota);
            zeta = (uu___133_2456.zeta);
            weak = (uu___133_2456.weak);
            hnf = (uu___133_2456.hnf);
            primops = (uu___133_2456.primops);
            do_not_unfold_pure_lets = (uu___133_2456.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___133_2456.unfold_only);
            unfold_fully = (uu___133_2456.unfold_fully);
            unfold_attr = (uu___133_2456.unfold_attr);
            unfold_tac = (uu___133_2456.unfold_tac);
            pure_subterms_within_computations =
              (uu___133_2456.pure_subterms_within_computations);
            simplify = (uu___133_2456.simplify);
            erase_universes = (uu___133_2456.erase_universes);
            allow_unbound_universes = (uu___133_2456.allow_unbound_universes);
            reify_ = (uu___133_2456.reify_);
            compress_uvars = (uu___133_2456.compress_uvars);
            no_full_norm = (uu___133_2456.no_full_norm);
            check_no_uvars = (uu___133_2456.check_no_uvars);
            unmeta = (uu___133_2456.unmeta);
            unascribe = (uu___133_2456.unascribe);
            in_full_norm_request = (uu___133_2456.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___133_2456.weakly_reduce_scrutinee);
            nbe_step = (uu___133_2456.nbe_step);
            for_extraction = (uu___133_2456.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___137_2460 = fs  in
          {
            beta = (uu___137_2460.beta);
            iota = (uu___137_2460.iota);
            zeta = (uu___137_2460.zeta);
            weak = (uu___137_2460.weak);
            hnf = (uu___137_2460.hnf);
            primops = (uu___137_2460.primops);
            do_not_unfold_pure_lets = (uu___137_2460.do_not_unfold_pure_lets);
            unfold_until = (uu___137_2460.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___137_2460.unfold_fully);
            unfold_attr = (uu___137_2460.unfold_attr);
            unfold_tac = (uu___137_2460.unfold_tac);
            pure_subterms_within_computations =
              (uu___137_2460.pure_subterms_within_computations);
            simplify = (uu___137_2460.simplify);
            erase_universes = (uu___137_2460.erase_universes);
            allow_unbound_universes = (uu___137_2460.allow_unbound_universes);
            reify_ = (uu___137_2460.reify_);
            compress_uvars = (uu___137_2460.compress_uvars);
            no_full_norm = (uu___137_2460.no_full_norm);
            check_no_uvars = (uu___137_2460.check_no_uvars);
            unmeta = (uu___137_2460.unmeta);
            unascribe = (uu___137_2460.unascribe);
            in_full_norm_request = (uu___137_2460.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___137_2460.weakly_reduce_scrutinee);
            nbe_step = (uu___137_2460.nbe_step);
            for_extraction = (uu___137_2460.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___141_2466 = fs  in
          {
            beta = (uu___141_2466.beta);
            iota = (uu___141_2466.iota);
            zeta = (uu___141_2466.zeta);
            weak = (uu___141_2466.weak);
            hnf = (uu___141_2466.hnf);
            primops = (uu___141_2466.primops);
            do_not_unfold_pure_lets = (uu___141_2466.do_not_unfold_pure_lets);
            unfold_until = (uu___141_2466.unfold_until);
            unfold_only = (uu___141_2466.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___141_2466.unfold_attr);
            unfold_tac = (uu___141_2466.unfold_tac);
            pure_subterms_within_computations =
              (uu___141_2466.pure_subterms_within_computations);
            simplify = (uu___141_2466.simplify);
            erase_universes = (uu___141_2466.erase_universes);
            allow_unbound_universes = (uu___141_2466.allow_unbound_universes);
            reify_ = (uu___141_2466.reify_);
            compress_uvars = (uu___141_2466.compress_uvars);
            no_full_norm = (uu___141_2466.no_full_norm);
            check_no_uvars = (uu___141_2466.check_no_uvars);
            unmeta = (uu___141_2466.unmeta);
            unascribe = (uu___141_2466.unascribe);
            in_full_norm_request = (uu___141_2466.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___141_2466.weakly_reduce_scrutinee);
            nbe_step = (uu___141_2466.nbe_step);
            for_extraction = (uu___141_2466.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___145_2472 = fs  in
          {
            beta = (uu___145_2472.beta);
            iota = (uu___145_2472.iota);
            zeta = (uu___145_2472.zeta);
            weak = (uu___145_2472.weak);
            hnf = (uu___145_2472.hnf);
            primops = (uu___145_2472.primops);
            do_not_unfold_pure_lets = (uu___145_2472.do_not_unfold_pure_lets);
            unfold_until = (uu___145_2472.unfold_until);
            unfold_only = (uu___145_2472.unfold_only);
            unfold_fully = (uu___145_2472.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___145_2472.unfold_tac);
            pure_subterms_within_computations =
              (uu___145_2472.pure_subterms_within_computations);
            simplify = (uu___145_2472.simplify);
            erase_universes = (uu___145_2472.erase_universes);
            allow_unbound_universes = (uu___145_2472.allow_unbound_universes);
            reify_ = (uu___145_2472.reify_);
            compress_uvars = (uu___145_2472.compress_uvars);
            no_full_norm = (uu___145_2472.no_full_norm);
            check_no_uvars = (uu___145_2472.check_no_uvars);
            unmeta = (uu___145_2472.unmeta);
            unascribe = (uu___145_2472.unascribe);
            in_full_norm_request = (uu___145_2472.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___145_2472.weakly_reduce_scrutinee);
            nbe_step = (uu___145_2472.nbe_step);
            for_extraction = (uu___145_2472.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___148_2475 = fs  in
          {
            beta = (uu___148_2475.beta);
            iota = (uu___148_2475.iota);
            zeta = (uu___148_2475.zeta);
            weak = (uu___148_2475.weak);
            hnf = (uu___148_2475.hnf);
            primops = (uu___148_2475.primops);
            do_not_unfold_pure_lets = (uu___148_2475.do_not_unfold_pure_lets);
            unfold_until = (uu___148_2475.unfold_until);
            unfold_only = (uu___148_2475.unfold_only);
            unfold_fully = (uu___148_2475.unfold_fully);
            unfold_attr = (uu___148_2475.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___148_2475.pure_subterms_within_computations);
            simplify = (uu___148_2475.simplify);
            erase_universes = (uu___148_2475.erase_universes);
            allow_unbound_universes = (uu___148_2475.allow_unbound_universes);
            reify_ = (uu___148_2475.reify_);
            compress_uvars = (uu___148_2475.compress_uvars);
            no_full_norm = (uu___148_2475.no_full_norm);
            check_no_uvars = (uu___148_2475.check_no_uvars);
            unmeta = (uu___148_2475.unmeta);
            unascribe = (uu___148_2475.unascribe);
            in_full_norm_request = (uu___148_2475.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___148_2475.weakly_reduce_scrutinee);
            nbe_step = (uu___148_2475.nbe_step);
            for_extraction = (uu___148_2475.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___151_2477 = fs  in
          {
            beta = (uu___151_2477.beta);
            iota = (uu___151_2477.iota);
            zeta = (uu___151_2477.zeta);
            weak = (uu___151_2477.weak);
            hnf = (uu___151_2477.hnf);
            primops = (uu___151_2477.primops);
            do_not_unfold_pure_lets = (uu___151_2477.do_not_unfold_pure_lets);
            unfold_until = (uu___151_2477.unfold_until);
            unfold_only = (uu___151_2477.unfold_only);
            unfold_fully = (uu___151_2477.unfold_fully);
            unfold_attr = (uu___151_2477.unfold_attr);
            unfold_tac = (uu___151_2477.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___151_2477.simplify);
            erase_universes = (uu___151_2477.erase_universes);
            allow_unbound_universes = (uu___151_2477.allow_unbound_universes);
            reify_ = (uu___151_2477.reify_);
            compress_uvars = (uu___151_2477.compress_uvars);
            no_full_norm = (uu___151_2477.no_full_norm);
            check_no_uvars = (uu___151_2477.check_no_uvars);
            unmeta = (uu___151_2477.unmeta);
            unascribe = (uu___151_2477.unascribe);
            in_full_norm_request = (uu___151_2477.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___151_2477.weakly_reduce_scrutinee);
            nbe_step = (uu___151_2477.nbe_step);
            for_extraction = (uu___151_2477.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___154_2479 = fs  in
          {
            beta = (uu___154_2479.beta);
            iota = (uu___154_2479.iota);
            zeta = (uu___154_2479.zeta);
            weak = (uu___154_2479.weak);
            hnf = (uu___154_2479.hnf);
            primops = (uu___154_2479.primops);
            do_not_unfold_pure_lets = (uu___154_2479.do_not_unfold_pure_lets);
            unfold_until = (uu___154_2479.unfold_until);
            unfold_only = (uu___154_2479.unfold_only);
            unfold_fully = (uu___154_2479.unfold_fully);
            unfold_attr = (uu___154_2479.unfold_attr);
            unfold_tac = (uu___154_2479.unfold_tac);
            pure_subterms_within_computations =
              (uu___154_2479.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___154_2479.erase_universes);
            allow_unbound_universes = (uu___154_2479.allow_unbound_universes);
            reify_ = (uu___154_2479.reify_);
            compress_uvars = (uu___154_2479.compress_uvars);
            no_full_norm = (uu___154_2479.no_full_norm);
            check_no_uvars = (uu___154_2479.check_no_uvars);
            unmeta = (uu___154_2479.unmeta);
            unascribe = (uu___154_2479.unascribe);
            in_full_norm_request = (uu___154_2479.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___154_2479.weakly_reduce_scrutinee);
            nbe_step = (uu___154_2479.nbe_step);
            for_extraction = (uu___154_2479.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___157_2481 = fs  in
          {
            beta = (uu___157_2481.beta);
            iota = (uu___157_2481.iota);
            zeta = (uu___157_2481.zeta);
            weak = (uu___157_2481.weak);
            hnf = (uu___157_2481.hnf);
            primops = (uu___157_2481.primops);
            do_not_unfold_pure_lets = (uu___157_2481.do_not_unfold_pure_lets);
            unfold_until = (uu___157_2481.unfold_until);
            unfold_only = (uu___157_2481.unfold_only);
            unfold_fully = (uu___157_2481.unfold_fully);
            unfold_attr = (uu___157_2481.unfold_attr);
            unfold_tac = (uu___157_2481.unfold_tac);
            pure_subterms_within_computations =
              (uu___157_2481.pure_subterms_within_computations);
            simplify = (uu___157_2481.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___157_2481.allow_unbound_universes);
            reify_ = (uu___157_2481.reify_);
            compress_uvars = (uu___157_2481.compress_uvars);
            no_full_norm = (uu___157_2481.no_full_norm);
            check_no_uvars = (uu___157_2481.check_no_uvars);
            unmeta = (uu___157_2481.unmeta);
            unascribe = (uu___157_2481.unascribe);
            in_full_norm_request = (uu___157_2481.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___157_2481.weakly_reduce_scrutinee);
            nbe_step = (uu___157_2481.nbe_step);
            for_extraction = (uu___157_2481.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___160_2483 = fs  in
          {
            beta = (uu___160_2483.beta);
            iota = (uu___160_2483.iota);
            zeta = (uu___160_2483.zeta);
            weak = (uu___160_2483.weak);
            hnf = (uu___160_2483.hnf);
            primops = (uu___160_2483.primops);
            do_not_unfold_pure_lets = (uu___160_2483.do_not_unfold_pure_lets);
            unfold_until = (uu___160_2483.unfold_until);
            unfold_only = (uu___160_2483.unfold_only);
            unfold_fully = (uu___160_2483.unfold_fully);
            unfold_attr = (uu___160_2483.unfold_attr);
            unfold_tac = (uu___160_2483.unfold_tac);
            pure_subterms_within_computations =
              (uu___160_2483.pure_subterms_within_computations);
            simplify = (uu___160_2483.simplify);
            erase_universes = (uu___160_2483.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___160_2483.reify_);
            compress_uvars = (uu___160_2483.compress_uvars);
            no_full_norm = (uu___160_2483.no_full_norm);
            check_no_uvars = (uu___160_2483.check_no_uvars);
            unmeta = (uu___160_2483.unmeta);
            unascribe = (uu___160_2483.unascribe);
            in_full_norm_request = (uu___160_2483.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___160_2483.weakly_reduce_scrutinee);
            nbe_step = (uu___160_2483.nbe_step);
            for_extraction = (uu___160_2483.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___163_2485 = fs  in
          {
            beta = (uu___163_2485.beta);
            iota = (uu___163_2485.iota);
            zeta = (uu___163_2485.zeta);
            weak = (uu___163_2485.weak);
            hnf = (uu___163_2485.hnf);
            primops = (uu___163_2485.primops);
            do_not_unfold_pure_lets = (uu___163_2485.do_not_unfold_pure_lets);
            unfold_until = (uu___163_2485.unfold_until);
            unfold_only = (uu___163_2485.unfold_only);
            unfold_fully = (uu___163_2485.unfold_fully);
            unfold_attr = (uu___163_2485.unfold_attr);
            unfold_tac = (uu___163_2485.unfold_tac);
            pure_subterms_within_computations =
              (uu___163_2485.pure_subterms_within_computations);
            simplify = (uu___163_2485.simplify);
            erase_universes = (uu___163_2485.erase_universes);
            allow_unbound_universes = (uu___163_2485.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___163_2485.compress_uvars);
            no_full_norm = (uu___163_2485.no_full_norm);
            check_no_uvars = (uu___163_2485.check_no_uvars);
            unmeta = (uu___163_2485.unmeta);
            unascribe = (uu___163_2485.unascribe);
            in_full_norm_request = (uu___163_2485.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___163_2485.weakly_reduce_scrutinee);
            nbe_step = (uu___163_2485.nbe_step);
            for_extraction = (uu___163_2485.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___166_2487 = fs  in
          {
            beta = (uu___166_2487.beta);
            iota = (uu___166_2487.iota);
            zeta = (uu___166_2487.zeta);
            weak = (uu___166_2487.weak);
            hnf = (uu___166_2487.hnf);
            primops = (uu___166_2487.primops);
            do_not_unfold_pure_lets = (uu___166_2487.do_not_unfold_pure_lets);
            unfold_until = (uu___166_2487.unfold_until);
            unfold_only = (uu___166_2487.unfold_only);
            unfold_fully = (uu___166_2487.unfold_fully);
            unfold_attr = (uu___166_2487.unfold_attr);
            unfold_tac = (uu___166_2487.unfold_tac);
            pure_subterms_within_computations =
              (uu___166_2487.pure_subterms_within_computations);
            simplify = (uu___166_2487.simplify);
            erase_universes = (uu___166_2487.erase_universes);
            allow_unbound_universes = (uu___166_2487.allow_unbound_universes);
            reify_ = (uu___166_2487.reify_);
            compress_uvars = true;
            no_full_norm = (uu___166_2487.no_full_norm);
            check_no_uvars = (uu___166_2487.check_no_uvars);
            unmeta = (uu___166_2487.unmeta);
            unascribe = (uu___166_2487.unascribe);
            in_full_norm_request = (uu___166_2487.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___166_2487.weakly_reduce_scrutinee);
            nbe_step = (uu___166_2487.nbe_step);
            for_extraction = (uu___166_2487.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___169_2489 = fs  in
          {
            beta = (uu___169_2489.beta);
            iota = (uu___169_2489.iota);
            zeta = (uu___169_2489.zeta);
            weak = (uu___169_2489.weak);
            hnf = (uu___169_2489.hnf);
            primops = (uu___169_2489.primops);
            do_not_unfold_pure_lets = (uu___169_2489.do_not_unfold_pure_lets);
            unfold_until = (uu___169_2489.unfold_until);
            unfold_only = (uu___169_2489.unfold_only);
            unfold_fully = (uu___169_2489.unfold_fully);
            unfold_attr = (uu___169_2489.unfold_attr);
            unfold_tac = (uu___169_2489.unfold_tac);
            pure_subterms_within_computations =
              (uu___169_2489.pure_subterms_within_computations);
            simplify = (uu___169_2489.simplify);
            erase_universes = (uu___169_2489.erase_universes);
            allow_unbound_universes = (uu___169_2489.allow_unbound_universes);
            reify_ = (uu___169_2489.reify_);
            compress_uvars = (uu___169_2489.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___169_2489.check_no_uvars);
            unmeta = (uu___169_2489.unmeta);
            unascribe = (uu___169_2489.unascribe);
            in_full_norm_request = (uu___169_2489.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___169_2489.weakly_reduce_scrutinee);
            nbe_step = (uu___169_2489.nbe_step);
            for_extraction = (uu___169_2489.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___172_2491 = fs  in
          {
            beta = (uu___172_2491.beta);
            iota = (uu___172_2491.iota);
            zeta = (uu___172_2491.zeta);
            weak = (uu___172_2491.weak);
            hnf = (uu___172_2491.hnf);
            primops = (uu___172_2491.primops);
            do_not_unfold_pure_lets = (uu___172_2491.do_not_unfold_pure_lets);
            unfold_until = (uu___172_2491.unfold_until);
            unfold_only = (uu___172_2491.unfold_only);
            unfold_fully = (uu___172_2491.unfold_fully);
            unfold_attr = (uu___172_2491.unfold_attr);
            unfold_tac = (uu___172_2491.unfold_tac);
            pure_subterms_within_computations =
              (uu___172_2491.pure_subterms_within_computations);
            simplify = (uu___172_2491.simplify);
            erase_universes = (uu___172_2491.erase_universes);
            allow_unbound_universes = (uu___172_2491.allow_unbound_universes);
            reify_ = (uu___172_2491.reify_);
            compress_uvars = (uu___172_2491.compress_uvars);
            no_full_norm = (uu___172_2491.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___172_2491.unmeta);
            unascribe = (uu___172_2491.unascribe);
            in_full_norm_request = (uu___172_2491.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___172_2491.weakly_reduce_scrutinee);
            nbe_step = (uu___172_2491.nbe_step);
            for_extraction = (uu___172_2491.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___175_2493 = fs  in
          {
            beta = (uu___175_2493.beta);
            iota = (uu___175_2493.iota);
            zeta = (uu___175_2493.zeta);
            weak = (uu___175_2493.weak);
            hnf = (uu___175_2493.hnf);
            primops = (uu___175_2493.primops);
            do_not_unfold_pure_lets = (uu___175_2493.do_not_unfold_pure_lets);
            unfold_until = (uu___175_2493.unfold_until);
            unfold_only = (uu___175_2493.unfold_only);
            unfold_fully = (uu___175_2493.unfold_fully);
            unfold_attr = (uu___175_2493.unfold_attr);
            unfold_tac = (uu___175_2493.unfold_tac);
            pure_subterms_within_computations =
              (uu___175_2493.pure_subterms_within_computations);
            simplify = (uu___175_2493.simplify);
            erase_universes = (uu___175_2493.erase_universes);
            allow_unbound_universes = (uu___175_2493.allow_unbound_universes);
            reify_ = (uu___175_2493.reify_);
            compress_uvars = (uu___175_2493.compress_uvars);
            no_full_norm = (uu___175_2493.no_full_norm);
            check_no_uvars = (uu___175_2493.check_no_uvars);
            unmeta = true;
            unascribe = (uu___175_2493.unascribe);
            in_full_norm_request = (uu___175_2493.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___175_2493.weakly_reduce_scrutinee);
            nbe_step = (uu___175_2493.nbe_step);
            for_extraction = (uu___175_2493.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___178_2495 = fs  in
          {
            beta = (uu___178_2495.beta);
            iota = (uu___178_2495.iota);
            zeta = (uu___178_2495.zeta);
            weak = (uu___178_2495.weak);
            hnf = (uu___178_2495.hnf);
            primops = (uu___178_2495.primops);
            do_not_unfold_pure_lets = (uu___178_2495.do_not_unfold_pure_lets);
            unfold_until = (uu___178_2495.unfold_until);
            unfold_only = (uu___178_2495.unfold_only);
            unfold_fully = (uu___178_2495.unfold_fully);
            unfold_attr = (uu___178_2495.unfold_attr);
            unfold_tac = (uu___178_2495.unfold_tac);
            pure_subterms_within_computations =
              (uu___178_2495.pure_subterms_within_computations);
            simplify = (uu___178_2495.simplify);
            erase_universes = (uu___178_2495.erase_universes);
            allow_unbound_universes = (uu___178_2495.allow_unbound_universes);
            reify_ = (uu___178_2495.reify_);
            compress_uvars = (uu___178_2495.compress_uvars);
            no_full_norm = (uu___178_2495.no_full_norm);
            check_no_uvars = (uu___178_2495.check_no_uvars);
            unmeta = (uu___178_2495.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___178_2495.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___178_2495.weakly_reduce_scrutinee);
            nbe_step = (uu___178_2495.nbe_step);
            for_extraction = (uu___178_2495.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___181_2497 = fs  in
          {
            beta = (uu___181_2497.beta);
            iota = (uu___181_2497.iota);
            zeta = (uu___181_2497.zeta);
            weak = (uu___181_2497.weak);
            hnf = (uu___181_2497.hnf);
            primops = (uu___181_2497.primops);
            do_not_unfold_pure_lets = (uu___181_2497.do_not_unfold_pure_lets);
            unfold_until = (uu___181_2497.unfold_until);
            unfold_only = (uu___181_2497.unfold_only);
            unfold_fully = (uu___181_2497.unfold_fully);
            unfold_attr = (uu___181_2497.unfold_attr);
            unfold_tac = (uu___181_2497.unfold_tac);
            pure_subterms_within_computations =
              (uu___181_2497.pure_subterms_within_computations);
            simplify = (uu___181_2497.simplify);
            erase_universes = (uu___181_2497.erase_universes);
            allow_unbound_universes = (uu___181_2497.allow_unbound_universes);
            reify_ = (uu___181_2497.reify_);
            compress_uvars = (uu___181_2497.compress_uvars);
            no_full_norm = (uu___181_2497.no_full_norm);
            check_no_uvars = (uu___181_2497.check_no_uvars);
            unmeta = (uu___181_2497.unmeta);
            unascribe = (uu___181_2497.unascribe);
            in_full_norm_request = (uu___181_2497.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___181_2497.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___181_2497.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___184_2499 = fs  in
          {
            beta = (uu___184_2499.beta);
            iota = (uu___184_2499.iota);
            zeta = (uu___184_2499.zeta);
            weak = (uu___184_2499.weak);
            hnf = (uu___184_2499.hnf);
            primops = (uu___184_2499.primops);
            do_not_unfold_pure_lets = (uu___184_2499.do_not_unfold_pure_lets);
            unfold_until = (uu___184_2499.unfold_until);
            unfold_only = (uu___184_2499.unfold_only);
            unfold_fully = (uu___184_2499.unfold_fully);
            unfold_attr = (uu___184_2499.unfold_attr);
            unfold_tac = (uu___184_2499.unfold_tac);
            pure_subterms_within_computations =
              (uu___184_2499.pure_subterms_within_computations);
            simplify = (uu___184_2499.simplify);
            erase_universes = (uu___184_2499.erase_universes);
            allow_unbound_universes = (uu___184_2499.allow_unbound_universes);
            reify_ = (uu___184_2499.reify_);
            compress_uvars = (uu___184_2499.compress_uvars);
            no_full_norm = (uu___184_2499.no_full_norm);
            check_no_uvars = (uu___184_2499.check_no_uvars);
            unmeta = (uu___184_2499.unmeta);
            unascribe = (uu___184_2499.unascribe);
            in_full_norm_request = (uu___184_2499.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___184_2499.weakly_reduce_scrutinee);
            nbe_step = (uu___184_2499.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____2557  -> []) } 
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
    print_normalized = false
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
  fun uu____3340  -> FStar_Util.psmap_empty () 
let (add_step :
  primitive_step -> prim_step_set -> primitive_step FStar_Util.psmap) =
  fun s  ->
    fun ss  ->
      let uu____3354 = FStar_Ident.text_of_lid s.name  in
      FStar_Util.psmap_add ss uu____3354 s
  
let (merge_steps : prim_step_set -> prim_step_set -> prim_step_set) =
  fun s1  -> fun s2  -> FStar_Util.psmap_merge s1 s2 
let (add_steps : prim_step_set -> primitive_step Prims.list -> prim_step_set)
  = fun m  -> fun l  -> FStar_List.fold_right add_step l m 
let (prim_from_list : primitive_step Prims.list -> prim_step_set) =
  fun l  -> let uu____3392 = empty_prim_steps ()  in add_steps uu____3392 l 
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
    let uu____3652 =
      let uu____3656 =
        let uu____3660 =
          let uu____3662 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____3662  in
        [uu____3660; "}"]  in
      "{" :: uu____3656  in
    FStar_String.concat "\n" uu____3652
  
let (cfg_env : cfg -> FStar_TypeChecker_Env.env) = fun cfg  -> cfg.tcenv 
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____3691 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____3691
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____3705 =
        let uu____3708 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____3708  in
      FStar_Util.is_some uu____3705
  
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
      let uu____3821 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____3821 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____3857 = FStar_Syntax_Embeddings.embed emb x  in
        uu____3857 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____3890 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____3890 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____3905 .
    'Auu____3905 ->
      FStar_Range.range -> 'Auu____3905 FStar_Syntax_Syntax.syntax
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
    let uu____4024 =
      let uu____4033 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____4033  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4024  in
  let arg_as_bounded_int1 uu____4063 =
    match uu____4063 with
    | (a,uu____4077) ->
        let uu____4088 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____4088 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____4132 =
               let uu____4147 =
                 let uu____4148 = FStar_Syntax_Subst.compress hd1  in
                 uu____4148.FStar_Syntax_Syntax.n  in
               (uu____4147, args)  in
             (match uu____4132 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____4169)::[]) when
                  (let uu____4206 =
                     FStar_Ident.text_of_lid
                       (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   FStar_Util.ends_with uu____4206 "int_to_t") ||
                    (let uu____4210 =
                       FStar_Ident.text_of_lid
                         (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        in
                     FStar_Util.ends_with uu____4210 "Mk")
                  ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____4214 =
                    let uu____4215 = FStar_Syntax_Subst.compress arg1  in
                    uu____4215.FStar_Syntax_Syntax.n  in
                  (match uu____4214 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____4237 =
                         let uu____4242 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____4242)  in
                       FStar_Pervasives_Native.Some uu____4237
                   | uu____4247 -> FStar_Pervasives_Native.None)
              | uu____4252 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4314 = f a  in FStar_Pervasives_Native.Some uu____4314
    | uu____4315 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4371 = f a0 a1  in FStar_Pervasives_Native.Some uu____4371
    | uu____4372 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____4439 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____4439  in
  let binary_op1 as_a f res n1 args =
    let uu____4521 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____4521  in
  let as_primitive_step is_strong uu____4576 =
    match uu____4576 with
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
           let uu____4684 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____4684)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4726 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____4726)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____4767 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____4767)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4820 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____4820)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4873 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____4873)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____5026 =
          let uu____5035 = as_a a  in
          let uu____5038 = as_b b  in (uu____5035, uu____5038)  in
        (match uu____5026 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5053 =
               let uu____5054 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5054  in
             FStar_Pervasives_Native.Some uu____5053
         | uu____5055 -> FStar_Pervasives_Native.None)
    | uu____5064 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____5086 =
        let uu____5087 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5087  in
      mk uu____5086 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5101 =
      let uu____5104 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5104  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5101  in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5152 =
      let uu____5153 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5153  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____5152  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____5239 = arg_as_string1 a1  in
        (match uu____5239 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5248 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____5248 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5266 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____5266
              | uu____5268 -> FStar_Pervasives_Native.None)
         | uu____5274 -> FStar_Pervasives_Native.None)
    | uu____5278 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5359 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____5359 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5375 = arg_as_string1 a2  in
             (match uu____5375 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____5388 =
                    let uu____5389 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____5389 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5388
              | uu____5399 -> FStar_Pervasives_Native.None)
         | uu____5403 -> FStar_Pervasives_Native.None)
    | uu____5409 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____5447 =
          let uu____5461 = arg_as_string1 a1  in
          let uu____5465 = arg_as_int1 a2  in
          let uu____5468 = arg_as_int1 a3  in
          (uu____5461, uu____5465, uu____5468)  in
        (match uu____5447 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___504_5501  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____5506 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5506) ()
              with | uu___503_5509 -> FStar_Pervasives_Native.None)
         | uu____5512 -> FStar_Pervasives_Native.None)
    | uu____5526 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5540 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____5540  in
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
        let uu____5619 =
          let uu____5629 = arg_as_string1 a1  in
          let uu____5633 = arg_as_int1 a2  in (uu____5629, uu____5633)  in
        (match uu____5619 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___538_5657  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____5662 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5662) ()
              with | uu___537_5665 -> FStar_Pervasives_Native.None)
         | uu____5668 -> FStar_Pervasives_Native.None)
    | uu____5678 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5709 =
          let uu____5720 = arg_as_string1 a1  in
          let uu____5724 = arg_as_char1 a2  in (uu____5720, uu____5724)  in
        (match uu____5709 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___559_5753  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____5757 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5757) ()
              with | uu___558_5759 -> FStar_Pervasives_Native.None)
         | uu____5762 -> FStar_Pervasives_Native.None)
    | uu____5773 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5807 =
          let uu____5829 = arg_as_string1 fn  in
          let uu____5833 = arg_as_int1 from_line  in
          let uu____5836 = arg_as_int1 from_col  in
          let uu____5839 = arg_as_int1 to_line  in
          let uu____5842 = arg_as_int1 to_col  in
          (uu____5829, uu____5833, uu____5836, uu____5839, uu____5842)  in
        (match uu____5807 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5877 =
                 let uu____5878 = FStar_BigInt.to_int_fs from_l  in
                 let uu____5880 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____5878 uu____5880  in
               let uu____5882 =
                 let uu____5883 = FStar_BigInt.to_int_fs to_l  in
                 let uu____5885 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____5883 uu____5885  in
               FStar_Range.mk_range fn1 uu____5877 uu____5882  in
             let uu____5887 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____5887
         | uu____5888 -> FStar_Pervasives_Native.None)
    | uu____5910 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____5954)::(a1,uu____5956)::(a2,uu____5958)::[] ->
        let uu____6015 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6015 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6024 -> FStar_Pervasives_Native.None)
    | uu____6025 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____6068)::[] ->
        let uu____6085 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____6085 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6091 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6091
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6092 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____6112  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____6146 =
      let uu____6176 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, Prims.int_one, Prims.int_zero,
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)), uu____6176)
       in
    let uu____6210 =
      let uu____6242 =
        let uu____6272 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.of_int (2)), Prims.int_zero,
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____6272)
         in
      let uu____6312 =
        let uu____6344 =
          let uu____6374 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.of_int (2)),
            Prims.int_zero,
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____6374)
           in
        let uu____6414 =
          let uu____6446 =
            let uu____6476 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.of_int (2)),
              Prims.int_zero,
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____6476)
             in
          let uu____6516 =
            let uu____6548 =
              let uu____6578 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.of_int (2)),
                Prims.int_zero,
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____6578)
               in
            let uu____6618 =
              let uu____6650 =
                let uu____6680 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____6692 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____6692)
                   in
                (FStar_Parser_Const.op_LT, (Prims.of_int (2)),
                  Prims.int_zero,
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____6723 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____6723)), uu____6680)
                 in
              let uu____6726 =
                let uu____6758 =
                  let uu____6788 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____6800 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____6800)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.of_int (2)),
                    Prims.int_zero,
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____6831 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____6831)), uu____6788)
                   in
                let uu____6834 =
                  let uu____6866 =
                    let uu____6896 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____6908 = FStar_BigInt.gt_big_int x y  in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____6908)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.of_int (2)),
                      Prims.int_zero,
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____6939 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____6939)), uu____6896)
                     in
                  let uu____6942 =
                    let uu____6974 =
                      let uu____7004 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____7016 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____7016)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.of_int (2)),
                        Prims.int_zero,
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____7047 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____7047)), uu____7004)
                       in
                    let uu____7050 =
                      let uu____7082 =
                        let uu____7112 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus, (Prims.of_int (2)),
                          Prims.int_zero,
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____7112)
                         in
                      let uu____7152 =
                        let uu____7184 =
                          let uu____7214 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation, Prims.int_one,
                            Prims.int_zero,
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____7214)
                           in
                        let uu____7250 =
                          let uu____7282 =
                            let uu____7312 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And, (Prims.of_int (2)),
                              Prims.int_zero,
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____7312)
                             in
                          let uu____7356 =
                            let uu____7388 =
                              let uu____7418 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or, (Prims.of_int (2)),
                                Prims.int_zero,
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____7418)
                               in
                            let uu____7462 =
                              let uu____7494 =
                                let uu____7524 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  Prims.int_one, Prims.int_zero,
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____7524)
                                 in
                              let uu____7552 =
                                let uu____7584 =
                                  let uu____7614 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    Prims.int_one, Prims.int_zero,
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____7614)
                                   in
                                let uu____7644 =
                                  let uu____7676 =
                                    let uu____7706 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      Prims.int_one, Prims.int_zero,
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____7706)
                                     in
                                  let uu____7736 =
                                    let uu____7768 =
                                      let uu____7798 =
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
                                           string_of_list'1), uu____7798)
                                       in
                                    let uu____7834 =
                                      let uu____7866 =
                                        let uu____7898 =
                                          let uu____7930 =
                                            let uu____7960 =
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
                                              uu____7960)
                                             in
                                          let uu____8004 =
                                            let uu____8036 =
                                              let uu____8068 =
                                                let uu____8098 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.of_int (2)),
                                                  Prims.int_zero,
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____8098)
                                                 in
                                              let uu____8128 =
                                                let uu____8160 =
                                                  let uu____8190 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    Prims.int_one,
                                                    Prims.int_zero,
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____8190)
                                                   in
                                                let uu____8220 =
                                                  let uu____8252 =
                                                    let uu____8282 =
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
                                                      uu____8282)
                                                     in
                                                  let uu____8312 =
                                                    let uu____8344 =
                                                      let uu____8376 =
                                                        let uu____8408 =
                                                          let uu____8440 =
                                                            let uu____8472 =
                                                              let uu____8504
                                                                =
                                                                let uu____8534
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____8534,
                                                                  (Prims.of_int (5)),
                                                                  Prims.int_zero,
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____8561
                                                                =
                                                                let uu____8593
                                                                  =
                                                                  let uu____8623
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____8623,
                                                                    Prims.int_one,
                                                                    Prims.int_zero,
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____8593]
                                                                 in
                                                              uu____8504 ::
                                                                uu____8561
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.of_int (3)),
                                                              Prims.int_zero,
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____8472
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.of_int (3)),
                                                            Prims.int_zero,
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____8440
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.of_int (3)),
                                                          Prims.int_zero,
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____8408
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.of_int (2)),
                                                        Prims.int_zero,
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____8376
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.of_int (2)),
                                                      Prims.int_zero,
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____8344
                                                     in
                                                  uu____8252 :: uu____8312
                                                   in
                                                uu____8160 :: uu____8220  in
                                              uu____8068 :: uu____8128  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.of_int (2)),
                                              Prims.int_zero,
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____8036
                                             in
                                          uu____7930 :: uu____8004  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.of_int (2)), Prims.int_zero,
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____7898
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
                                                  let uu____9270 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____9270 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____9281 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____9281
                                                  y)))
                                        :: uu____7866
                                       in
                                    uu____7768 :: uu____7834  in
                                  uu____7676 :: uu____7736  in
                                uu____7584 :: uu____7644  in
                              uu____7494 :: uu____7552  in
                            uu____7388 :: uu____7462  in
                          uu____7282 :: uu____7356  in
                        uu____7184 :: uu____7250  in
                      uu____7082 :: uu____7152  in
                    uu____6974 :: uu____7050  in
                  uu____6866 :: uu____6942  in
                uu____6758 :: uu____6834  in
              uu____6650 :: uu____6726  in
            uu____6548 :: uu____6618  in
          uu____6446 :: uu____6516  in
        uu____6344 :: uu____6414  in
      uu____6242 :: uu____6312  in
    uu____6146 :: uu____6210  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = []  in
    let bounded_unsigned_int_types = ["UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9901 =
        let uu____9906 =
          let uu____9907 = FStar_Syntax_Syntax.as_arg c  in [uu____9907]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9906  in
      uu____9901 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____10034 =
                let uu____10064 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____10071 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10089  ->
                       fun uu____10090  ->
                         match (uu____10089, uu____10090) with
                         | ((int_to_t1,x),(uu____10109,y)) ->
                             let uu____10119 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____10119)
                   in
                (uu____10064, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____10154  ->
                          fun uu____10155  ->
                            match (uu____10154, uu____10155) with
                            | ((int_to_t1,x),(uu____10174,y)) ->
                                let uu____10184 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____10184)),
                  uu____10071)
                 in
              let uu____10185 =
                let uu____10217 =
                  let uu____10247 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____10254 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____10272  ->
                         fun uu____10273  ->
                           match (uu____10272, uu____10273) with
                           | ((int_to_t1,x),(uu____10292,y)) ->
                               let uu____10302 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____10302)
                     in
                  (uu____10247, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____10337  ->
                            fun uu____10338  ->
                              match (uu____10337, uu____10338) with
                              | ((int_to_t1,x),(uu____10357,y)) ->
                                  let uu____10367 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____10367)),
                    uu____10254)
                   in
                let uu____10368 =
                  let uu____10400 =
                    let uu____10430 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____10437 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____10455  ->
                           fun uu____10456  ->
                             match (uu____10455, uu____10456) with
                             | ((int_to_t1,x),(uu____10475,y)) ->
                                 let uu____10485 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____10485)
                       in
                    (uu____10430, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____10520  ->
                              fun uu____10521  ->
                                match (uu____10520, uu____10521) with
                                | ((int_to_t1,x),(uu____10540,y)) ->
                                    let uu____10550 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____10550)),
                      uu____10437)
                     in
                  let uu____10551 =
                    let uu____10583 =
                      let uu____10613 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____10620 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____10634  ->
                             match uu____10634 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____10613, Prims.int_one, Prims.int_zero,
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____10671  ->
                                match uu____10671 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____10620)
                       in
                    [uu____10583]  in
                  uu____10400 :: uu____10551  in
                uu____10217 :: uu____10368  in
              uu____10034 :: uu____10185))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____10924 =
                let uu____10954 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____10961 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10979  ->
                       fun uu____10980  ->
                         match (uu____10979, uu____10980) with
                         | ((int_to_t1,x),(uu____10999,y)) ->
                             let uu____11009 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11009)
                   in
                (uu____10954, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11044  ->
                          fun uu____11045  ->
                            match (uu____11044, uu____11045) with
                            | ((int_to_t1,x),(uu____11064,y)) ->
                                let uu____11074 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11074)),
                  uu____10961)
                 in
              let uu____11075 =
                let uu____11107 =
                  let uu____11137 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____11144 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11162  ->
                         fun uu____11163  ->
                           match (uu____11162, uu____11163) with
                           | ((int_to_t1,x),(uu____11182,y)) ->
                               let uu____11192 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11192)
                     in
                  (uu____11137, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11227  ->
                            fun uu____11228  ->
                              match (uu____11227, uu____11228) with
                              | ((int_to_t1,x),(uu____11247,y)) ->
                                  let uu____11257 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11257)),
                    uu____11144)
                   in
                [uu____11107]  in
              uu____10924 :: uu____11075))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____11363 ->
          let uu____11365 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____11365
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____11469 =
                let uu____11499 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____11506 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11524  ->
                       fun uu____11525  ->
                         match (uu____11524, uu____11525) with
                         | ((int_to_t1,x),(uu____11544,y)) ->
                             let uu____11554 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11554)
                   in
                (uu____11499, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11589  ->
                          fun uu____11590  ->
                            match (uu____11589, uu____11590) with
                            | ((int_to_t1,x),(uu____11609,y)) ->
                                let uu____11619 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11619)),
                  uu____11506)
                 in
              let uu____11620 =
                let uu____11652 =
                  let uu____11682 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____11689 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11707  ->
                         fun uu____11708  ->
                           match (uu____11707, uu____11708) with
                           | ((int_to_t1,x),(uu____11727,y)) ->
                               let uu____11737 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11737)
                     in
                  (uu____11682, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11772  ->
                            fun uu____11773  ->
                              match (uu____11772, uu____11773) with
                              | ((int_to_t1,x),(uu____11792,y)) ->
                                  let uu____11802 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11802)),
                    uu____11689)
                   in
                let uu____11803 =
                  let uu____11835 =
                    let uu____11865 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____11872 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____11890  ->
                           fun uu____11891  ->
                             match (uu____11890, uu____11891) with
                             | ((int_to_t1,x),(uu____11910,y)) ->
                                 let uu____11920 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____11920)
                       in
                    (uu____11865, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____11955  ->
                              fun uu____11956  ->
                                match (uu____11955, uu____11956) with
                                | ((int_to_t1,x),(uu____11975,y)) ->
                                    let uu____11985 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____11985)),
                      uu____11872)
                     in
                  let uu____11986 =
                    let uu____12018 =
                      let uu____12048 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____12055 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____12070  ->
                             match uu____12070 with
                             | (int_to_t1,x) ->
                                 let uu____12077 =
                                   let uu____12078 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____12079 = mask m  in
                                   FStar_BigInt.logand_big_int uu____12078
                                     uu____12079
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____12077)
                         in
                      (uu____12048, Prims.int_one, Prims.int_zero,
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____12111  ->
                                match uu____12111 with
                                | (int_to_t1,x) ->
                                    let uu____12118 =
                                      let uu____12119 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____12120 = mask m  in
                                      FStar_BigInt.logand_big_int uu____12119
                                        uu____12120
                                       in
                                    int_as_bounded1 r int_to_t1 uu____12118)),
                        uu____12055)
                       in
                    let uu____12121 =
                      let uu____12153 =
                        let uu____12183 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____12190 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____12208  ->
                               fun uu____12209  ->
                                 match (uu____12208, uu____12209) with
                                 | ((int_to_t1,x),(uu____12228,y)) ->
                                     let uu____12238 =
                                       let uu____12239 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____12240 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____12239 uu____12240
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____12238)
                           in
                        (uu____12183, (Prims.of_int (2)), Prims.int_zero,
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____12275  ->
                                  fun uu____12276  ->
                                    match (uu____12275, uu____12276) with
                                    | ((int_to_t1,x),(uu____12295,y)) ->
                                        let uu____12305 =
                                          let uu____12306 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____12307 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____12306 uu____12307
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____12305)), uu____12190)
                         in
                      let uu____12308 =
                        let uu____12340 =
                          let uu____12370 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____12377 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____12395  ->
                                 fun uu____12396  ->
                                   match (uu____12395, uu____12396) with
                                   | ((int_to_t1,x),(uu____12415,y)) ->
                                       let uu____12425 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____12425)
                             in
                          (uu____12370, (Prims.of_int (2)), Prims.int_zero,
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____12460  ->
                                    fun uu____12461  ->
                                      match (uu____12460, uu____12461) with
                                      | ((int_to_t1,x),(uu____12480,y)) ->
                                          let uu____12490 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____12490)), uu____12377)
                           in
                        [uu____12340]  in
                      uu____12153 :: uu____12308  in
                    uu____12018 :: uu____12121  in
                  uu____11835 :: uu____11986  in
                uu____11652 :: uu____11803  in
              uu____11469 :: uu____11620))
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
    | (_typ,uu____12878)::(a1,uu____12880)::(a2,uu____12882)::[] ->
        let uu____12939 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____12939 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___879_12943 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___879_12943.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___879_12943.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___882_12945 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___882_12945.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___882_12945.FStar_Syntax_Syntax.vars)
                })
         | uu____12946 -> FStar_Pervasives_Native.None)
    | uu____12947 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____12977)::(t2,uu____12979)::(a1,uu____12981)::(a2,uu____12983)::[]
        ->
        let uu____13056 =
          let uu____13057 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____13058 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____13057 uu____13058  in
        (match uu____13056 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___905_13062 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___905_13062.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___905_13062.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___908_13064 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___908_13064.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___908_13064.FStar_Syntax_Syntax.vars)
                })
         | uu____13065 -> FStar_Pervasives_Native.None)
    | uu____13066 -> failwith "Unexpected number of arguments"  in
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
  fun uu____13097  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____13114 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____13114 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____13143 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____13143 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____13154  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____13225  ->
           fun uu____13226  ->
             match (uu____13225, uu____13226) with
             | ((uu____13252,t1),(uu____13254,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____13288  ->
         fun rest  ->
           match uu____13288 with
           | (nm,ms) ->
               let uu____13304 =
                 let uu____13306 =
                   let uu____13308 = FStar_Util.string_of_int ms  in
                   fixto (Prims.of_int (10)) uu____13308  in
                 FStar_Util.format2 "%sms --- %s\n" uu____13306 nm  in
               FStar_String.op_Hat uu____13304 rest) pairs1 ""
  
let (extendable_primops_dirty : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref true 
let (mk_extendable_primop_set :
  unit -> ((primitive_step -> unit) * (unit -> prim_step_set))) =
  fun uu____13334  ->
    let steps =
      let uu____13338 = empty_prim_steps ()  in FStar_Util.mk_ref uu____13338
       in
    let register p =
      FStar_ST.op_Colon_Equals extendable_primops_dirty true;
      (let uu____13368 =
         let uu____13369 = FStar_ST.op_Bang steps  in add_step p uu____13369
          in
       FStar_ST.op_Colon_Equals steps uu____13368)
       in
    let retrieve uu____13413 = FStar_ST.op_Bang steps  in
    (register, retrieve)
  
let (plugins : ((primitive_step -> unit) * (unit -> prim_step_set))) =
  mk_extendable_primop_set () 
let (extra_steps : ((primitive_step -> unit) * (unit -> prim_step_set))) =
  mk_extendable_primop_set () 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> prim_step_set) =
  fun uu____13478  ->
    let uu____13479 = FStar_Options.no_plugins ()  in
    if uu____13479
    then empty_prim_steps ()
    else FStar_Pervasives_Native.snd plugins ()
  
let (register_extra_step : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst extra_steps p 
let (retrieve_extra_steps : unit -> prim_step_set) =
  fun uu____13507  -> FStar_Pervasives_Native.snd extra_steps () 
let (cached_steps : unit -> prim_step_set) =
  let memo =
    let uu____13522 = empty_prim_steps ()  in FStar_Util.mk_ref uu____13522
     in
  fun uu____13523  ->
    let uu____13524 = FStar_ST.op_Bang extendable_primops_dirty  in
    if uu____13524
    then
      let steps =
        let uu____13549 =
          let uu____13550 = retrieve_plugins ()  in
          let uu____13551 = retrieve_extra_steps ()  in
          merge_steps uu____13550 uu____13551  in
        merge_steps built_in_primitive_steps uu____13549  in
      (FStar_ST.op_Colon_Equals memo steps;
       FStar_ST.op_Colon_Equals extendable_primops_dirty false;
       steps)
    else FStar_ST.op_Bang memo
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____13622 = FStar_Options.use_nbe ()  in
    if uu____13622
    then
      let uu___961_13625 = s  in
      {
        beta = (uu___961_13625.beta);
        iota = (uu___961_13625.iota);
        zeta = (uu___961_13625.zeta);
        weak = (uu___961_13625.weak);
        hnf = (uu___961_13625.hnf);
        primops = (uu___961_13625.primops);
        do_not_unfold_pure_lets = (uu___961_13625.do_not_unfold_pure_lets);
        unfold_until = (uu___961_13625.unfold_until);
        unfold_only = (uu___961_13625.unfold_only);
        unfold_fully = (uu___961_13625.unfold_fully);
        unfold_attr = (uu___961_13625.unfold_attr);
        unfold_tac = (uu___961_13625.unfold_tac);
        pure_subterms_within_computations =
          (uu___961_13625.pure_subterms_within_computations);
        simplify = (uu___961_13625.simplify);
        erase_universes = (uu___961_13625.erase_universes);
        allow_unbound_universes = (uu___961_13625.allow_unbound_universes);
        reify_ = (uu___961_13625.reify_);
        compress_uvars = (uu___961_13625.compress_uvars);
        no_full_norm = (uu___961_13625.no_full_norm);
        check_no_uvars = (uu___961_13625.check_no_uvars);
        unmeta = (uu___961_13625.unmeta);
        unascribe = (uu___961_13625.unascribe);
        in_full_norm_request = (uu___961_13625.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___961_13625.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___961_13625.for_extraction)
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
               (fun uu___0_13662  ->
                  match uu___0_13662 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding b ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only b]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____13668 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____13674 -> d  in
        let steps =
          let uu____13678 = to_fsteps s  in
          FStar_All.pipe_right uu____13678 add_nbe  in
        let psteps1 =
          let uu____13680 = cached_steps ()  in add_steps uu____13680 psteps
           in
        let uu____13681 =
          let uu____13682 = FStar_Options.debug_any ()  in
          if uu____13682
          then
            let uu____13685 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
            let uu____13688 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")
               in
            let uu____13691 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")
               in
            let uu____13694 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")
               in
            let uu____13697 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
               in
            let uu____13700 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
            let uu____13703 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
            let uu____13706 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "NormDelayed")
               in
            let uu____13709 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "print_normalized_terms")
               in
            {
              gen = uu____13685;
              top = uu____13688;
              cfg = uu____13691;
              primop = uu____13694;
              unfolding = uu____13697;
              b380 = uu____13700;
              wpe = uu____13703;
              norm_delayed = uu____13706;
              print_normalized = uu____13709
            }
          else no_debug_switches  in
        let uu____13714 =
          (Prims.op_Negation steps.pure_subterms_within_computations) ||
            (FStar_Options.normalize_pure_terms_for_extraction ())
           in
        {
          steps;
          tcenv = e;
          debug = uu____13681;
          delta_level = d1;
          primitive_steps = psteps1;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____13714;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 