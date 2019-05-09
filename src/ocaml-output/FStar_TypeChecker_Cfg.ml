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
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___128_2451 = fs  in
          {
            beta = (uu___128_2451.beta);
            iota = (uu___128_2451.iota);
            zeta = (uu___128_2451.zeta);
            weak = (uu___128_2451.weak);
            hnf = (uu___128_2451.hnf);
            primops = (uu___128_2451.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___128_2451.unfold_until);
            unfold_only = (uu___128_2451.unfold_only);
            unfold_fully = (uu___128_2451.unfold_fully);
            unfold_attr = (uu___128_2451.unfold_attr);
            unfold_tac = (uu___128_2451.unfold_tac);
            pure_subterms_within_computations =
              (uu___128_2451.pure_subterms_within_computations);
            simplify = (uu___128_2451.simplify);
            erase_universes = (uu___128_2451.erase_universes);
            allow_unbound_universes = (uu___128_2451.allow_unbound_universes);
            reify_ = (uu___128_2451.reify_);
            compress_uvars = (uu___128_2451.compress_uvars);
            no_full_norm = (uu___128_2451.no_full_norm);
            check_no_uvars = (uu___128_2451.check_no_uvars);
            unmeta = (uu___128_2451.unmeta);
            unascribe = (uu___128_2451.unascribe);
            in_full_norm_request = (uu___128_2451.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___128_2451.weakly_reduce_scrutinee);
            nbe_step = (uu___128_2451.nbe_step);
            for_extraction = (uu___128_2451.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___132_2454 = fs  in
          {
            beta = (uu___132_2454.beta);
            iota = (uu___132_2454.iota);
            zeta = (uu___132_2454.zeta);
            weak = (uu___132_2454.weak);
            hnf = (uu___132_2454.hnf);
            primops = (uu___132_2454.primops);
            do_not_unfold_pure_lets = (uu___132_2454.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___132_2454.unfold_only);
            unfold_fully = (uu___132_2454.unfold_fully);
            unfold_attr = (uu___132_2454.unfold_attr);
            unfold_tac = (uu___132_2454.unfold_tac);
            pure_subterms_within_computations =
              (uu___132_2454.pure_subterms_within_computations);
            simplify = (uu___132_2454.simplify);
            erase_universes = (uu___132_2454.erase_universes);
            allow_unbound_universes = (uu___132_2454.allow_unbound_universes);
            reify_ = (uu___132_2454.reify_);
            compress_uvars = (uu___132_2454.compress_uvars);
            no_full_norm = (uu___132_2454.no_full_norm);
            check_no_uvars = (uu___132_2454.check_no_uvars);
            unmeta = (uu___132_2454.unmeta);
            unascribe = (uu___132_2454.unascribe);
            in_full_norm_request = (uu___132_2454.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___132_2454.weakly_reduce_scrutinee);
            nbe_step = (uu___132_2454.nbe_step);
            for_extraction = (uu___132_2454.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___136_2458 = fs  in
          {
            beta = (uu___136_2458.beta);
            iota = (uu___136_2458.iota);
            zeta = (uu___136_2458.zeta);
            weak = (uu___136_2458.weak);
            hnf = (uu___136_2458.hnf);
            primops = (uu___136_2458.primops);
            do_not_unfold_pure_lets = (uu___136_2458.do_not_unfold_pure_lets);
            unfold_until = (uu___136_2458.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___136_2458.unfold_fully);
            unfold_attr = (uu___136_2458.unfold_attr);
            unfold_tac = (uu___136_2458.unfold_tac);
            pure_subterms_within_computations =
              (uu___136_2458.pure_subterms_within_computations);
            simplify = (uu___136_2458.simplify);
            erase_universes = (uu___136_2458.erase_universes);
            allow_unbound_universes = (uu___136_2458.allow_unbound_universes);
            reify_ = (uu___136_2458.reify_);
            compress_uvars = (uu___136_2458.compress_uvars);
            no_full_norm = (uu___136_2458.no_full_norm);
            check_no_uvars = (uu___136_2458.check_no_uvars);
            unmeta = (uu___136_2458.unmeta);
            unascribe = (uu___136_2458.unascribe);
            in_full_norm_request = (uu___136_2458.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___136_2458.weakly_reduce_scrutinee);
            nbe_step = (uu___136_2458.nbe_step);
            for_extraction = (uu___136_2458.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___140_2464 = fs  in
          {
            beta = (uu___140_2464.beta);
            iota = (uu___140_2464.iota);
            zeta = (uu___140_2464.zeta);
            weak = (uu___140_2464.weak);
            hnf = (uu___140_2464.hnf);
            primops = (uu___140_2464.primops);
            do_not_unfold_pure_lets = (uu___140_2464.do_not_unfold_pure_lets);
            unfold_until = (uu___140_2464.unfold_until);
            unfold_only = (uu___140_2464.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___140_2464.unfold_attr);
            unfold_tac = (uu___140_2464.unfold_tac);
            pure_subterms_within_computations =
              (uu___140_2464.pure_subterms_within_computations);
            simplify = (uu___140_2464.simplify);
            erase_universes = (uu___140_2464.erase_universes);
            allow_unbound_universes = (uu___140_2464.allow_unbound_universes);
            reify_ = (uu___140_2464.reify_);
            compress_uvars = (uu___140_2464.compress_uvars);
            no_full_norm = (uu___140_2464.no_full_norm);
            check_no_uvars = (uu___140_2464.check_no_uvars);
            unmeta = (uu___140_2464.unmeta);
            unascribe = (uu___140_2464.unascribe);
            in_full_norm_request = (uu___140_2464.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___140_2464.weakly_reduce_scrutinee);
            nbe_step = (uu___140_2464.nbe_step);
            for_extraction = (uu___140_2464.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___144_2470 = fs  in
          {
            beta = (uu___144_2470.beta);
            iota = (uu___144_2470.iota);
            zeta = (uu___144_2470.zeta);
            weak = (uu___144_2470.weak);
            hnf = (uu___144_2470.hnf);
            primops = (uu___144_2470.primops);
            do_not_unfold_pure_lets = (uu___144_2470.do_not_unfold_pure_lets);
            unfold_until = (uu___144_2470.unfold_until);
            unfold_only = (uu___144_2470.unfold_only);
            unfold_fully = (uu___144_2470.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___144_2470.unfold_tac);
            pure_subterms_within_computations =
              (uu___144_2470.pure_subterms_within_computations);
            simplify = (uu___144_2470.simplify);
            erase_universes = (uu___144_2470.erase_universes);
            allow_unbound_universes = (uu___144_2470.allow_unbound_universes);
            reify_ = (uu___144_2470.reify_);
            compress_uvars = (uu___144_2470.compress_uvars);
            no_full_norm = (uu___144_2470.no_full_norm);
            check_no_uvars = (uu___144_2470.check_no_uvars);
            unmeta = (uu___144_2470.unmeta);
            unascribe = (uu___144_2470.unascribe);
            in_full_norm_request = (uu___144_2470.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___144_2470.weakly_reduce_scrutinee);
            nbe_step = (uu___144_2470.nbe_step);
            for_extraction = (uu___144_2470.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___147_2473 = fs  in
          {
            beta = (uu___147_2473.beta);
            iota = (uu___147_2473.iota);
            zeta = (uu___147_2473.zeta);
            weak = (uu___147_2473.weak);
            hnf = (uu___147_2473.hnf);
            primops = (uu___147_2473.primops);
            do_not_unfold_pure_lets = (uu___147_2473.do_not_unfold_pure_lets);
            unfold_until = (uu___147_2473.unfold_until);
            unfold_only = (uu___147_2473.unfold_only);
            unfold_fully = (uu___147_2473.unfold_fully);
            unfold_attr = (uu___147_2473.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___147_2473.pure_subterms_within_computations);
            simplify = (uu___147_2473.simplify);
            erase_universes = (uu___147_2473.erase_universes);
            allow_unbound_universes = (uu___147_2473.allow_unbound_universes);
            reify_ = (uu___147_2473.reify_);
            compress_uvars = (uu___147_2473.compress_uvars);
            no_full_norm = (uu___147_2473.no_full_norm);
            check_no_uvars = (uu___147_2473.check_no_uvars);
            unmeta = (uu___147_2473.unmeta);
            unascribe = (uu___147_2473.unascribe);
            in_full_norm_request = (uu___147_2473.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___147_2473.weakly_reduce_scrutinee);
            nbe_step = (uu___147_2473.nbe_step);
            for_extraction = (uu___147_2473.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___150_2475 = fs  in
          {
            beta = (uu___150_2475.beta);
            iota = (uu___150_2475.iota);
            zeta = (uu___150_2475.zeta);
            weak = (uu___150_2475.weak);
            hnf = (uu___150_2475.hnf);
            primops = (uu___150_2475.primops);
            do_not_unfold_pure_lets = (uu___150_2475.do_not_unfold_pure_lets);
            unfold_until = (uu___150_2475.unfold_until);
            unfold_only = (uu___150_2475.unfold_only);
            unfold_fully = (uu___150_2475.unfold_fully);
            unfold_attr = (uu___150_2475.unfold_attr);
            unfold_tac = (uu___150_2475.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___150_2475.simplify);
            erase_universes = (uu___150_2475.erase_universes);
            allow_unbound_universes = (uu___150_2475.allow_unbound_universes);
            reify_ = (uu___150_2475.reify_);
            compress_uvars = (uu___150_2475.compress_uvars);
            no_full_norm = (uu___150_2475.no_full_norm);
            check_no_uvars = (uu___150_2475.check_no_uvars);
            unmeta = (uu___150_2475.unmeta);
            unascribe = (uu___150_2475.unascribe);
            in_full_norm_request = (uu___150_2475.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___150_2475.weakly_reduce_scrutinee);
            nbe_step = (uu___150_2475.nbe_step);
            for_extraction = (uu___150_2475.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___153_2477 = fs  in
          {
            beta = (uu___153_2477.beta);
            iota = (uu___153_2477.iota);
            zeta = (uu___153_2477.zeta);
            weak = (uu___153_2477.weak);
            hnf = (uu___153_2477.hnf);
            primops = (uu___153_2477.primops);
            do_not_unfold_pure_lets = (uu___153_2477.do_not_unfold_pure_lets);
            unfold_until = (uu___153_2477.unfold_until);
            unfold_only = (uu___153_2477.unfold_only);
            unfold_fully = (uu___153_2477.unfold_fully);
            unfold_attr = (uu___153_2477.unfold_attr);
            unfold_tac = (uu___153_2477.unfold_tac);
            pure_subterms_within_computations =
              (uu___153_2477.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___153_2477.erase_universes);
            allow_unbound_universes = (uu___153_2477.allow_unbound_universes);
            reify_ = (uu___153_2477.reify_);
            compress_uvars = (uu___153_2477.compress_uvars);
            no_full_norm = (uu___153_2477.no_full_norm);
            check_no_uvars = (uu___153_2477.check_no_uvars);
            unmeta = (uu___153_2477.unmeta);
            unascribe = (uu___153_2477.unascribe);
            in_full_norm_request = (uu___153_2477.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___153_2477.weakly_reduce_scrutinee);
            nbe_step = (uu___153_2477.nbe_step);
            for_extraction = (uu___153_2477.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___156_2479 = fs  in
          {
            beta = (uu___156_2479.beta);
            iota = (uu___156_2479.iota);
            zeta = (uu___156_2479.zeta);
            weak = (uu___156_2479.weak);
            hnf = (uu___156_2479.hnf);
            primops = (uu___156_2479.primops);
            do_not_unfold_pure_lets = (uu___156_2479.do_not_unfold_pure_lets);
            unfold_until = (uu___156_2479.unfold_until);
            unfold_only = (uu___156_2479.unfold_only);
            unfold_fully = (uu___156_2479.unfold_fully);
            unfold_attr = (uu___156_2479.unfold_attr);
            unfold_tac = (uu___156_2479.unfold_tac);
            pure_subterms_within_computations =
              (uu___156_2479.pure_subterms_within_computations);
            simplify = (uu___156_2479.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___156_2479.allow_unbound_universes);
            reify_ = (uu___156_2479.reify_);
            compress_uvars = (uu___156_2479.compress_uvars);
            no_full_norm = (uu___156_2479.no_full_norm);
            check_no_uvars = (uu___156_2479.check_no_uvars);
            unmeta = (uu___156_2479.unmeta);
            unascribe = (uu___156_2479.unascribe);
            in_full_norm_request = (uu___156_2479.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___156_2479.weakly_reduce_scrutinee);
            nbe_step = (uu___156_2479.nbe_step);
            for_extraction = (uu___156_2479.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___159_2481 = fs  in
          {
            beta = (uu___159_2481.beta);
            iota = (uu___159_2481.iota);
            zeta = (uu___159_2481.zeta);
            weak = (uu___159_2481.weak);
            hnf = (uu___159_2481.hnf);
            primops = (uu___159_2481.primops);
            do_not_unfold_pure_lets = (uu___159_2481.do_not_unfold_pure_lets);
            unfold_until = (uu___159_2481.unfold_until);
            unfold_only = (uu___159_2481.unfold_only);
            unfold_fully = (uu___159_2481.unfold_fully);
            unfold_attr = (uu___159_2481.unfold_attr);
            unfold_tac = (uu___159_2481.unfold_tac);
            pure_subterms_within_computations =
              (uu___159_2481.pure_subterms_within_computations);
            simplify = (uu___159_2481.simplify);
            erase_universes = (uu___159_2481.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___159_2481.reify_);
            compress_uvars = (uu___159_2481.compress_uvars);
            no_full_norm = (uu___159_2481.no_full_norm);
            check_no_uvars = (uu___159_2481.check_no_uvars);
            unmeta = (uu___159_2481.unmeta);
            unascribe = (uu___159_2481.unascribe);
            in_full_norm_request = (uu___159_2481.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___159_2481.weakly_reduce_scrutinee);
            nbe_step = (uu___159_2481.nbe_step);
            for_extraction = (uu___159_2481.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___162_2483 = fs  in
          {
            beta = (uu___162_2483.beta);
            iota = (uu___162_2483.iota);
            zeta = (uu___162_2483.zeta);
            weak = (uu___162_2483.weak);
            hnf = (uu___162_2483.hnf);
            primops = (uu___162_2483.primops);
            do_not_unfold_pure_lets = (uu___162_2483.do_not_unfold_pure_lets);
            unfold_until = (uu___162_2483.unfold_until);
            unfold_only = (uu___162_2483.unfold_only);
            unfold_fully = (uu___162_2483.unfold_fully);
            unfold_attr = (uu___162_2483.unfold_attr);
            unfold_tac = (uu___162_2483.unfold_tac);
            pure_subterms_within_computations =
              (uu___162_2483.pure_subterms_within_computations);
            simplify = (uu___162_2483.simplify);
            erase_universes = (uu___162_2483.erase_universes);
            allow_unbound_universes = (uu___162_2483.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___162_2483.compress_uvars);
            no_full_norm = (uu___162_2483.no_full_norm);
            check_no_uvars = (uu___162_2483.check_no_uvars);
            unmeta = (uu___162_2483.unmeta);
            unascribe = (uu___162_2483.unascribe);
            in_full_norm_request = (uu___162_2483.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___162_2483.weakly_reduce_scrutinee);
            nbe_step = (uu___162_2483.nbe_step);
            for_extraction = (uu___162_2483.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___165_2485 = fs  in
          {
            beta = (uu___165_2485.beta);
            iota = (uu___165_2485.iota);
            zeta = (uu___165_2485.zeta);
            weak = (uu___165_2485.weak);
            hnf = (uu___165_2485.hnf);
            primops = (uu___165_2485.primops);
            do_not_unfold_pure_lets = (uu___165_2485.do_not_unfold_pure_lets);
            unfold_until = (uu___165_2485.unfold_until);
            unfold_only = (uu___165_2485.unfold_only);
            unfold_fully = (uu___165_2485.unfold_fully);
            unfold_attr = (uu___165_2485.unfold_attr);
            unfold_tac = (uu___165_2485.unfold_tac);
            pure_subterms_within_computations =
              (uu___165_2485.pure_subterms_within_computations);
            simplify = (uu___165_2485.simplify);
            erase_universes = (uu___165_2485.erase_universes);
            allow_unbound_universes = (uu___165_2485.allow_unbound_universes);
            reify_ = (uu___165_2485.reify_);
            compress_uvars = true;
            no_full_norm = (uu___165_2485.no_full_norm);
            check_no_uvars = (uu___165_2485.check_no_uvars);
            unmeta = (uu___165_2485.unmeta);
            unascribe = (uu___165_2485.unascribe);
            in_full_norm_request = (uu___165_2485.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___165_2485.weakly_reduce_scrutinee);
            nbe_step = (uu___165_2485.nbe_step);
            for_extraction = (uu___165_2485.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___168_2487 = fs  in
          {
            beta = (uu___168_2487.beta);
            iota = (uu___168_2487.iota);
            zeta = (uu___168_2487.zeta);
            weak = (uu___168_2487.weak);
            hnf = (uu___168_2487.hnf);
            primops = (uu___168_2487.primops);
            do_not_unfold_pure_lets = (uu___168_2487.do_not_unfold_pure_lets);
            unfold_until = (uu___168_2487.unfold_until);
            unfold_only = (uu___168_2487.unfold_only);
            unfold_fully = (uu___168_2487.unfold_fully);
            unfold_attr = (uu___168_2487.unfold_attr);
            unfold_tac = (uu___168_2487.unfold_tac);
            pure_subterms_within_computations =
              (uu___168_2487.pure_subterms_within_computations);
            simplify = (uu___168_2487.simplify);
            erase_universes = (uu___168_2487.erase_universes);
            allow_unbound_universes = (uu___168_2487.allow_unbound_universes);
            reify_ = (uu___168_2487.reify_);
            compress_uvars = (uu___168_2487.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___168_2487.check_no_uvars);
            unmeta = (uu___168_2487.unmeta);
            unascribe = (uu___168_2487.unascribe);
            in_full_norm_request = (uu___168_2487.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___168_2487.weakly_reduce_scrutinee);
            nbe_step = (uu___168_2487.nbe_step);
            for_extraction = (uu___168_2487.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___171_2489 = fs  in
          {
            beta = (uu___171_2489.beta);
            iota = (uu___171_2489.iota);
            zeta = (uu___171_2489.zeta);
            weak = (uu___171_2489.weak);
            hnf = (uu___171_2489.hnf);
            primops = (uu___171_2489.primops);
            do_not_unfold_pure_lets = (uu___171_2489.do_not_unfold_pure_lets);
            unfold_until = (uu___171_2489.unfold_until);
            unfold_only = (uu___171_2489.unfold_only);
            unfold_fully = (uu___171_2489.unfold_fully);
            unfold_attr = (uu___171_2489.unfold_attr);
            unfold_tac = (uu___171_2489.unfold_tac);
            pure_subterms_within_computations =
              (uu___171_2489.pure_subterms_within_computations);
            simplify = (uu___171_2489.simplify);
            erase_universes = (uu___171_2489.erase_universes);
            allow_unbound_universes = (uu___171_2489.allow_unbound_universes);
            reify_ = (uu___171_2489.reify_);
            compress_uvars = (uu___171_2489.compress_uvars);
            no_full_norm = (uu___171_2489.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___171_2489.unmeta);
            unascribe = (uu___171_2489.unascribe);
            in_full_norm_request = (uu___171_2489.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___171_2489.weakly_reduce_scrutinee);
            nbe_step = (uu___171_2489.nbe_step);
            for_extraction = (uu___171_2489.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___174_2491 = fs  in
          {
            beta = (uu___174_2491.beta);
            iota = (uu___174_2491.iota);
            zeta = (uu___174_2491.zeta);
            weak = (uu___174_2491.weak);
            hnf = (uu___174_2491.hnf);
            primops = (uu___174_2491.primops);
            do_not_unfold_pure_lets = (uu___174_2491.do_not_unfold_pure_lets);
            unfold_until = (uu___174_2491.unfold_until);
            unfold_only = (uu___174_2491.unfold_only);
            unfold_fully = (uu___174_2491.unfold_fully);
            unfold_attr = (uu___174_2491.unfold_attr);
            unfold_tac = (uu___174_2491.unfold_tac);
            pure_subterms_within_computations =
              (uu___174_2491.pure_subterms_within_computations);
            simplify = (uu___174_2491.simplify);
            erase_universes = (uu___174_2491.erase_universes);
            allow_unbound_universes = (uu___174_2491.allow_unbound_universes);
            reify_ = (uu___174_2491.reify_);
            compress_uvars = (uu___174_2491.compress_uvars);
            no_full_norm = (uu___174_2491.no_full_norm);
            check_no_uvars = (uu___174_2491.check_no_uvars);
            unmeta = true;
            unascribe = (uu___174_2491.unascribe);
            in_full_norm_request = (uu___174_2491.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___174_2491.weakly_reduce_scrutinee);
            nbe_step = (uu___174_2491.nbe_step);
            for_extraction = (uu___174_2491.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___177_2493 = fs  in
          {
            beta = (uu___177_2493.beta);
            iota = (uu___177_2493.iota);
            zeta = (uu___177_2493.zeta);
            weak = (uu___177_2493.weak);
            hnf = (uu___177_2493.hnf);
            primops = (uu___177_2493.primops);
            do_not_unfold_pure_lets = (uu___177_2493.do_not_unfold_pure_lets);
            unfold_until = (uu___177_2493.unfold_until);
            unfold_only = (uu___177_2493.unfold_only);
            unfold_fully = (uu___177_2493.unfold_fully);
            unfold_attr = (uu___177_2493.unfold_attr);
            unfold_tac = (uu___177_2493.unfold_tac);
            pure_subterms_within_computations =
              (uu___177_2493.pure_subterms_within_computations);
            simplify = (uu___177_2493.simplify);
            erase_universes = (uu___177_2493.erase_universes);
            allow_unbound_universes = (uu___177_2493.allow_unbound_universes);
            reify_ = (uu___177_2493.reify_);
            compress_uvars = (uu___177_2493.compress_uvars);
            no_full_norm = (uu___177_2493.no_full_norm);
            check_no_uvars = (uu___177_2493.check_no_uvars);
            unmeta = (uu___177_2493.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___177_2493.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___177_2493.weakly_reduce_scrutinee);
            nbe_step = (uu___177_2493.nbe_step);
            for_extraction = (uu___177_2493.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___180_2495 = fs  in
          {
            beta = (uu___180_2495.beta);
            iota = (uu___180_2495.iota);
            zeta = (uu___180_2495.zeta);
            weak = (uu___180_2495.weak);
            hnf = (uu___180_2495.hnf);
            primops = (uu___180_2495.primops);
            do_not_unfold_pure_lets = (uu___180_2495.do_not_unfold_pure_lets);
            unfold_until = (uu___180_2495.unfold_until);
            unfold_only = (uu___180_2495.unfold_only);
            unfold_fully = (uu___180_2495.unfold_fully);
            unfold_attr = (uu___180_2495.unfold_attr);
            unfold_tac = (uu___180_2495.unfold_tac);
            pure_subterms_within_computations =
              (uu___180_2495.pure_subterms_within_computations);
            simplify = (uu___180_2495.simplify);
            erase_universes = (uu___180_2495.erase_universes);
            allow_unbound_universes = (uu___180_2495.allow_unbound_universes);
            reify_ = (uu___180_2495.reify_);
            compress_uvars = (uu___180_2495.compress_uvars);
            no_full_norm = (uu___180_2495.no_full_norm);
            check_no_uvars = (uu___180_2495.check_no_uvars);
            unmeta = (uu___180_2495.unmeta);
            unascribe = (uu___180_2495.unascribe);
            in_full_norm_request = (uu___180_2495.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___180_2495.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___180_2495.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___183_2497 = fs  in
          {
            beta = (uu___183_2497.beta);
            iota = (uu___183_2497.iota);
            zeta = (uu___183_2497.zeta);
            weak = (uu___183_2497.weak);
            hnf = (uu___183_2497.hnf);
            primops = (uu___183_2497.primops);
            do_not_unfold_pure_lets = (uu___183_2497.do_not_unfold_pure_lets);
            unfold_until = (uu___183_2497.unfold_until);
            unfold_only = (uu___183_2497.unfold_only);
            unfold_fully = (uu___183_2497.unfold_fully);
            unfold_attr = (uu___183_2497.unfold_attr);
            unfold_tac = (uu___183_2497.unfold_tac);
            pure_subterms_within_computations =
              (uu___183_2497.pure_subterms_within_computations);
            simplify = (uu___183_2497.simplify);
            erase_universes = (uu___183_2497.erase_universes);
            allow_unbound_universes = (uu___183_2497.allow_unbound_universes);
            reify_ = (uu___183_2497.reify_);
            compress_uvars = (uu___183_2497.compress_uvars);
            no_full_norm = (uu___183_2497.no_full_norm);
            check_no_uvars = (uu___183_2497.check_no_uvars);
            unmeta = (uu___183_2497.unmeta);
            unascribe = (uu___183_2497.unascribe);
            in_full_norm_request = (uu___183_2497.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___183_2497.weakly_reduce_scrutinee);
            nbe_step = (uu___183_2497.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____2555  -> []) } 
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
    let uu____3604 =
      let uu____3608 =
        let uu____3612 =
          let uu____3614 = steps_to_string cfg.steps  in
          let uu____3616 =
            let uu____3618 =
              FStar_List.map FStar_TypeChecker_Env.string_of_delta_level
                cfg.delta_level
               in
            FStar_All.pipe_right uu____3618 (FStar_String.concat ", ")  in
          FStar_Util.format2 "  steps = %s; delta_level={%s}" uu____3614
            uu____3616
           in
        [uu____3612; "}"]  in
      "{" :: uu____3608  in
    FStar_String.concat "\n" uu____3604
  
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
             let uu____3674 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____3674 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____3690 = FStar_Util.psmap_empty ()  in add_steps uu____3690 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____3706 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____3706
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____3720 =
        let uu____3723 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____3723  in
      FStar_Util.is_some uu____3720
  
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
      let uu____3836 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____3836 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____3872 = FStar_Syntax_Embeddings.embed emb x  in
        uu____3872 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____3905 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____3905 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____3920 .
    'Auu____3920 ->
      FStar_Range.range -> 'Auu____3920 FStar_Syntax_Syntax.syntax
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
    let uu____4041 =
      let uu____4050 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____4050  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4041  in
  let arg_as_bounded_int1 uu____4080 =
    match uu____4080 with
    | (a,uu____4094) ->
        let uu____4105 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____4105 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____4149 =
               let uu____4164 =
                 let uu____4165 = FStar_Syntax_Subst.compress hd1  in
                 uu____4165.FStar_Syntax_Syntax.n  in
               (uu____4164, args)  in
             (match uu____4149 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____4186)::[]) when
                  (let uu____4223 =
                     FStar_Ident.text_of_lid
                       (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   FStar_Util.ends_with uu____4223 "int_to_t") ||
                    (let uu____4227 =
                       FStar_Ident.text_of_lid
                         (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        in
                     FStar_Util.ends_with uu____4227 "Mk")
                  ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____4231 =
                    let uu____4232 = FStar_Syntax_Subst.compress arg1  in
                    uu____4232.FStar_Syntax_Syntax.n  in
                  (match uu____4231 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____4254 =
                         let uu____4259 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____4259)  in
                       FStar_Pervasives_Native.Some uu____4254
                   | uu____4264 -> FStar_Pervasives_Native.None)
              | uu____4269 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4331 = f a  in FStar_Pervasives_Native.Some uu____4331
    | uu____4332 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4388 = f a0 a1  in FStar_Pervasives_Native.Some uu____4388
    | uu____4389 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____4456 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____4456  in
  let binary_op1 as_a f res n1 args =
    let uu____4538 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____4538  in
  let as_primitive_step is_strong uu____4593 =
    match uu____4593 with
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
           let uu____4701 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____4701)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4743 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____4743)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____4784 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____4784)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4837 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____4837)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4890 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____4890)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____5043 =
          let uu____5052 = as_a a  in
          let uu____5055 = as_b b  in (uu____5052, uu____5055)  in
        (match uu____5043 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5070 =
               let uu____5071 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5071  in
             FStar_Pervasives_Native.Some uu____5070
         | uu____5072 -> FStar_Pervasives_Native.None)
    | uu____5081 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____5103 =
        let uu____5104 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5104  in
      mk uu____5103 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5118 =
      let uu____5121 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5121  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5118  in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5169 =
      let uu____5170 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5170  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____5169  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____5256 = arg_as_string1 a1  in
        (match uu____5256 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5265 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____5265 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5283 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____5283
              | uu____5285 -> FStar_Pervasives_Native.None)
         | uu____5291 -> FStar_Pervasives_Native.None)
    | uu____5295 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5376 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____5376 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5392 = arg_as_string1 a2  in
             (match uu____5392 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____5405 =
                    let uu____5406 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____5406 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5405
              | uu____5416 -> FStar_Pervasives_Native.None)
         | uu____5420 -> FStar_Pervasives_Native.None)
    | uu____5426 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____5464 =
          let uu____5478 = arg_as_string1 a1  in
          let uu____5482 = arg_as_int1 a2  in
          let uu____5485 = arg_as_int1 a3  in
          (uu____5478, uu____5482, uu____5485)  in
        (match uu____5464 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___500_5518  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____5523 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5523) ()
              with | uu___499_5526 -> FStar_Pervasives_Native.None)
         | uu____5529 -> FStar_Pervasives_Native.None)
    | uu____5543 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5557 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____5557  in
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
        let uu____5636 =
          let uu____5646 = arg_as_string1 a1  in
          let uu____5650 = arg_as_int1 a2  in (uu____5646, uu____5650)  in
        (match uu____5636 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___534_5674  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____5679 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5679) ()
              with | uu___533_5682 -> FStar_Pervasives_Native.None)
         | uu____5685 -> FStar_Pervasives_Native.None)
    | uu____5695 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5726 =
          let uu____5737 = arg_as_string1 a1  in
          let uu____5741 = arg_as_char1 a2  in (uu____5737, uu____5741)  in
        (match uu____5726 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___555_5770  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____5774 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5774) ()
              with | uu___554_5776 -> FStar_Pervasives_Native.None)
         | uu____5779 -> FStar_Pervasives_Native.None)
    | uu____5790 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5824 =
          let uu____5846 = arg_as_string1 fn  in
          let uu____5850 = arg_as_int1 from_line  in
          let uu____5853 = arg_as_int1 from_col  in
          let uu____5856 = arg_as_int1 to_line  in
          let uu____5859 = arg_as_int1 to_col  in
          (uu____5846, uu____5850, uu____5853, uu____5856, uu____5859)  in
        (match uu____5824 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5894 =
                 let uu____5895 = FStar_BigInt.to_int_fs from_l  in
                 let uu____5897 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____5895 uu____5897  in
               let uu____5899 =
                 let uu____5900 = FStar_BigInt.to_int_fs to_l  in
                 let uu____5902 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____5900 uu____5902  in
               FStar_Range.mk_range fn1 uu____5894 uu____5899  in
             let uu____5904 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____5904
         | uu____5905 -> FStar_Pervasives_Native.None)
    | uu____5927 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____5971)::(a1,uu____5973)::(a2,uu____5975)::[] ->
        let uu____6032 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6032 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6041 -> FStar_Pervasives_Native.None)
    | uu____6042 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____6085)::[] ->
        let uu____6102 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____6102 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6108 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6108
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6109 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____6129  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____6163 =
      let uu____6193 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)), uu____6193)
       in
    let uu____6227 =
      let uu____6259 =
        let uu____6289 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____6289)
         in
      let uu____6329 =
        let uu____6361 =
          let uu____6391 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____6391)
           in
        let uu____6431 =
          let uu____6463 =
            let uu____6493 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____6493)
             in
          let uu____6533 =
            let uu____6565 =
              let uu____6595 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____6595)
               in
            let uu____6635 =
              let uu____6667 =
                let uu____6697 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____6709 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____6709)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____6740 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____6740)), uu____6697)
                 in
              let uu____6743 =
                let uu____6775 =
                  let uu____6805 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____6817 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____6817)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____6848 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____6848)), uu____6805)
                   in
                let uu____6851 =
                  let uu____6883 =
                    let uu____6913 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____6925 = FStar_BigInt.gt_big_int x y  in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____6925)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____6956 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____6956)), uu____6913)
                     in
                  let uu____6959 =
                    let uu____6991 =
                      let uu____7021 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____7033 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____7033)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____7064 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____7064)), uu____7021)
                       in
                    let uu____7067 =
                      let uu____7099 =
                        let uu____7129 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____7129)
                         in
                      let uu____7169 =
                        let uu____7201 =
                          let uu____7231 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____7231)
                           in
                        let uu____7267 =
                          let uu____7299 =
                            let uu____7329 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____7329)
                             in
                          let uu____7373 =
                            let uu____7405 =
                              let uu____7435 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____7435)
                               in
                            let uu____7479 =
                              let uu____7511 =
                                let uu____7541 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____7541)
                                 in
                              let uu____7569 =
                                let uu____7601 =
                                  let uu____7631 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____7631)
                                   in
                                let uu____7661 =
                                  let uu____7693 =
                                    let uu____7723 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____7723)
                                     in
                                  let uu____7753 =
                                    let uu____7785 =
                                      let uu____7815 =
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
                                           string_of_list'1), uu____7815)
                                       in
                                    let uu____7851 =
                                      let uu____7883 =
                                        let uu____7915 =
                                          let uu____7947 =
                                            let uu____7977 =
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
                                              uu____7977)
                                             in
                                          let uu____8021 =
                                            let uu____8053 =
                                              let uu____8085 =
                                                let uu____8115 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____8115)
                                                 in
                                              let uu____8145 =
                                                let uu____8177 =
                                                  let uu____8207 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____8207)
                                                   in
                                                let uu____8237 =
                                                  let uu____8269 =
                                                    let uu____8299 =
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
                                                      uu____8299)
                                                     in
                                                  let uu____8329 =
                                                    let uu____8361 =
                                                      let uu____8393 =
                                                        let uu____8425 =
                                                          let uu____8457 =
                                                            let uu____8489 =
                                                              let uu____8521
                                                                =
                                                                let uu____8551
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____8551,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____8578
                                                                =
                                                                let uu____8610
                                                                  =
                                                                  let uu____8640
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____8640,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____8610]
                                                                 in
                                                              uu____8521 ::
                                                                uu____8578
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____8489
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____8457
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____8425
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____8393
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____8361
                                                     in
                                                  uu____8269 :: uu____8329
                                                   in
                                                uu____8177 :: uu____8237  in
                                              uu____8085 :: uu____8145  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____8053
                                             in
                                          uu____7947 :: uu____8021  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____7915
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
                                                  let uu____9287 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____9287 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____9298 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____9298
                                                  y)))
                                        :: uu____7883
                                       in
                                    uu____7785 :: uu____7851  in
                                  uu____7693 :: uu____7753  in
                                uu____7601 :: uu____7661  in
                              uu____7511 :: uu____7569  in
                            uu____7405 :: uu____7479  in
                          uu____7299 :: uu____7373  in
                        uu____7201 :: uu____7267  in
                      uu____7099 :: uu____7169  in
                    uu____6991 :: uu____7067  in
                  uu____6883 :: uu____6959  in
                uu____6775 :: uu____6851  in
              uu____6667 :: uu____6743  in
            uu____6565 :: uu____6635  in
          uu____6463 :: uu____6533  in
        uu____6361 :: uu____6431  in
      uu____6259 :: uu____6329  in
    uu____6163 :: uu____6227  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = []  in
    let bounded_unsigned_int_types = ["UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9918 =
        let uu____9923 =
          let uu____9924 = FStar_Syntax_Syntax.as_arg c  in [uu____9924]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9923  in
      uu____9918 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____10051 =
                let uu____10081 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____10088 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10106  ->
                       fun uu____10107  ->
                         match (uu____10106, uu____10107) with
                         | ((int_to_t1,x),(uu____10126,y)) ->
                             let uu____10136 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____10136)
                   in
                (uu____10081, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____10171  ->
                          fun uu____10172  ->
                            match (uu____10171, uu____10172) with
                            | ((int_to_t1,x),(uu____10191,y)) ->
                                let uu____10201 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____10201)),
                  uu____10088)
                 in
              let uu____10202 =
                let uu____10234 =
                  let uu____10264 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____10271 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____10289  ->
                         fun uu____10290  ->
                           match (uu____10289, uu____10290) with
                           | ((int_to_t1,x),(uu____10309,y)) ->
                               let uu____10319 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____10319)
                     in
                  (uu____10264, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____10354  ->
                            fun uu____10355  ->
                              match (uu____10354, uu____10355) with
                              | ((int_to_t1,x),(uu____10374,y)) ->
                                  let uu____10384 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____10384)),
                    uu____10271)
                   in
                let uu____10385 =
                  let uu____10417 =
                    let uu____10447 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____10454 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____10472  ->
                           fun uu____10473  ->
                             match (uu____10472, uu____10473) with
                             | ((int_to_t1,x),(uu____10492,y)) ->
                                 let uu____10502 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____10502)
                       in
                    (uu____10447, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____10537  ->
                              fun uu____10538  ->
                                match (uu____10537, uu____10538) with
                                | ((int_to_t1,x),(uu____10557,y)) ->
                                    let uu____10567 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____10567)),
                      uu____10454)
                     in
                  let uu____10568 =
                    let uu____10600 =
                      let uu____10630 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____10637 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____10651  ->
                             match uu____10651 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____10630, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____10688  ->
                                match uu____10688 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____10637)
                       in
                    [uu____10600]  in
                  uu____10417 :: uu____10568  in
                uu____10234 :: uu____10385  in
              uu____10051 :: uu____10202))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____10941 =
                let uu____10971 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____10978 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10996  ->
                       fun uu____10997  ->
                         match (uu____10996, uu____10997) with
                         | ((int_to_t1,x),(uu____11016,y)) ->
                             let uu____11026 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11026)
                   in
                (uu____10971, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11061  ->
                          fun uu____11062  ->
                            match (uu____11061, uu____11062) with
                            | ((int_to_t1,x),(uu____11081,y)) ->
                                let uu____11091 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11091)),
                  uu____10978)
                 in
              let uu____11092 =
                let uu____11124 =
                  let uu____11154 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____11161 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11179  ->
                         fun uu____11180  ->
                           match (uu____11179, uu____11180) with
                           | ((int_to_t1,x),(uu____11199,y)) ->
                               let uu____11209 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11209)
                     in
                  (uu____11154, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11244  ->
                            fun uu____11245  ->
                              match (uu____11244, uu____11245) with
                              | ((int_to_t1,x),(uu____11264,y)) ->
                                  let uu____11274 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11274)),
                    uu____11161)
                   in
                [uu____11124]  in
              uu____10941 :: uu____11092))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____11380 ->
          let uu____11382 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____11382
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____11486 =
                let uu____11516 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____11523 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11541  ->
                       fun uu____11542  ->
                         match (uu____11541, uu____11542) with
                         | ((int_to_t1,x),(uu____11561,y)) ->
                             let uu____11571 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11571)
                   in
                (uu____11516, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11606  ->
                          fun uu____11607  ->
                            match (uu____11606, uu____11607) with
                            | ((int_to_t1,x),(uu____11626,y)) ->
                                let uu____11636 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11636)),
                  uu____11523)
                 in
              let uu____11637 =
                let uu____11669 =
                  let uu____11699 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____11706 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11724  ->
                         fun uu____11725  ->
                           match (uu____11724, uu____11725) with
                           | ((int_to_t1,x),(uu____11744,y)) ->
                               let uu____11754 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11754)
                     in
                  (uu____11699, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11789  ->
                            fun uu____11790  ->
                              match (uu____11789, uu____11790) with
                              | ((int_to_t1,x),(uu____11809,y)) ->
                                  let uu____11819 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11819)),
                    uu____11706)
                   in
                let uu____11820 =
                  let uu____11852 =
                    let uu____11882 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____11889 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____11907  ->
                           fun uu____11908  ->
                             match (uu____11907, uu____11908) with
                             | ((int_to_t1,x),(uu____11927,y)) ->
                                 let uu____11937 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____11937)
                       in
                    (uu____11882, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____11972  ->
                              fun uu____11973  ->
                                match (uu____11972, uu____11973) with
                                | ((int_to_t1,x),(uu____11992,y)) ->
                                    let uu____12002 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____12002)),
                      uu____11889)
                     in
                  let uu____12003 =
                    let uu____12035 =
                      let uu____12065 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____12072 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____12087  ->
                             match uu____12087 with
                             | (int_to_t1,x) ->
                                 let uu____12094 =
                                   let uu____12095 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____12096 = mask m  in
                                   FStar_BigInt.logand_big_int uu____12095
                                     uu____12096
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____12094)
                         in
                      (uu____12065, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____12128  ->
                                match uu____12128 with
                                | (int_to_t1,x) ->
                                    let uu____12135 =
                                      let uu____12136 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____12137 = mask m  in
                                      FStar_BigInt.logand_big_int uu____12136
                                        uu____12137
                                       in
                                    int_as_bounded1 r int_to_t1 uu____12135)),
                        uu____12072)
                       in
                    let uu____12138 =
                      let uu____12170 =
                        let uu____12200 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____12207 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____12225  ->
                               fun uu____12226  ->
                                 match (uu____12225, uu____12226) with
                                 | ((int_to_t1,x),(uu____12245,y)) ->
                                     let uu____12255 =
                                       let uu____12256 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____12257 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____12256 uu____12257
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____12255)
                           in
                        (uu____12200, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____12292  ->
                                  fun uu____12293  ->
                                    match (uu____12292, uu____12293) with
                                    | ((int_to_t1,x),(uu____12312,y)) ->
                                        let uu____12322 =
                                          let uu____12323 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____12324 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____12323 uu____12324
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____12322)), uu____12207)
                         in
                      let uu____12325 =
                        let uu____12357 =
                          let uu____12387 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____12394 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____12412  ->
                                 fun uu____12413  ->
                                   match (uu____12412, uu____12413) with
                                   | ((int_to_t1,x),(uu____12432,y)) ->
                                       let uu____12442 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____12442)
                             in
                          (uu____12387, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____12477  ->
                                    fun uu____12478  ->
                                      match (uu____12477, uu____12478) with
                                      | ((int_to_t1,x),(uu____12497,y)) ->
                                          let uu____12507 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____12507)), uu____12394)
                           in
                        [uu____12357]  in
                      uu____12170 :: uu____12325  in
                    uu____12035 :: uu____12138  in
                  uu____11852 :: uu____12003  in
                uu____11669 :: uu____11820  in
              uu____11486 :: uu____11637))
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
    | (_typ,uu____12899)::(a1,uu____12901)::(a2,uu____12903)::[] ->
        let uu____12960 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____12960 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___875_12964 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___875_12964.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___875_12964.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___878_12966 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___878_12966.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___878_12966.FStar_Syntax_Syntax.vars)
                })
         | uu____12967 -> FStar_Pervasives_Native.None)
    | uu____12968 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____12998)::(t2,uu____13000)::(a1,uu____13002)::(a2,uu____13004)::[]
        ->
        let uu____13077 =
          let uu____13078 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____13079 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____13078 uu____13079  in
        (match uu____13077 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___901_13083 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___901_13083.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___901_13083.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___904_13085 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___904_13085.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___904_13085.FStar_Syntax_Syntax.vars)
                })
         | uu____13086 -> FStar_Pervasives_Native.None)
    | uu____13087 -> failwith "Unexpected number of arguments"  in
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
  fun uu____13118  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____13135 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____13135 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____13164 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____13164 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____13175  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____13246  ->
           fun uu____13247  ->
             match (uu____13246, uu____13247) with
             | ((uu____13273,t1),(uu____13275,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____13309  ->
         fun rest  ->
           match uu____13309 with
           | (nm,ms) ->
               let uu____13325 =
                 let uu____13327 =
                   let uu____13329 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____13329  in
                 FStar_Util.format2 "%sms --- %s\n" uu____13327 nm  in
               FStar_String.op_Hat uu____13325 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____13360 =
      let uu____13363 = FStar_ST.op_Bang plugins  in p :: uu____13363  in
    FStar_ST.op_Colon_Equals plugins uu____13360  in
  let retrieve uu____13419 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____13472  ->
    let uu____13473 = FStar_Options.no_plugins ()  in
    if uu____13473 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____13494 = FStar_Options.use_nbe ()  in
    if uu____13494
    then
      let uu___947_13497 = s  in
      {
        beta = (uu___947_13497.beta);
        iota = (uu___947_13497.iota);
        zeta = (uu___947_13497.zeta);
        weak = (uu___947_13497.weak);
        hnf = (uu___947_13497.hnf);
        primops = (uu___947_13497.primops);
        do_not_unfold_pure_lets = (uu___947_13497.do_not_unfold_pure_lets);
        unfold_until = (uu___947_13497.unfold_until);
        unfold_only = (uu___947_13497.unfold_only);
        unfold_fully = (uu___947_13497.unfold_fully);
        unfold_attr = (uu___947_13497.unfold_attr);
        unfold_tac = (uu___947_13497.unfold_tac);
        pure_subterms_within_computations =
          (uu___947_13497.pure_subterms_within_computations);
        simplify = (uu___947_13497.simplify);
        erase_universes = (uu___947_13497.erase_universes);
        allow_unbound_universes = (uu___947_13497.allow_unbound_universes);
        reify_ = (uu___947_13497.reify_);
        compress_uvars = (uu___947_13497.compress_uvars);
        no_full_norm = (uu___947_13497.no_full_norm);
        check_no_uvars = (uu___947_13497.check_no_uvars);
        unmeta = (uu___947_13497.unmeta);
        unascribe = (uu___947_13497.unascribe);
        in_full_norm_request = (uu___947_13497.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___947_13497.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___947_13497.for_extraction)
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
               (fun uu___0_13534  ->
                  match uu___0_13534 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____13538 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____13544 -> d  in
        let uu____13547 =
          let uu____13548 = to_fsteps s  in
          FStar_All.pipe_right uu____13548 add_nbe  in
        let uu____13549 =
          let uu____13550 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____13553 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____13556 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____13559 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____13562 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____13565 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____13568 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____13571 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____13574 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____13550;
            top = uu____13553;
            cfg = uu____13556;
            primop = uu____13559;
            unfolding = uu____13562;
            b380 = uu____13565;
            wpe = uu____13568;
            norm_delayed = uu____13571;
            print_normalized = uu____13574
          }  in
        let uu____13577 =
          let uu____13580 =
            let uu____13583 = retrieve_plugins ()  in
            FStar_List.append uu____13583 psteps  in
          add_steps built_in_primitive_steps uu____13580  in
        let uu____13586 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____13589 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____13589)
           in
        {
          steps = uu____13547;
          tcenv = e;
          debug = uu____13549;
          delta_level = d1;
          primitive_steps = uu____13577;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____13586;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 