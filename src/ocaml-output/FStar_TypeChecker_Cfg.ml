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
    let uu____3606 =
      let uu____3610 =
        let uu____3614 =
          let uu____3616 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____3616  in
        [uu____3614; "}"]  in
      "{" :: uu____3610  in
    FStar_String.concat "\n" uu____3606
  
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
             let uu____3664 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____3664 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____3680 = FStar_Util.psmap_empty ()  in add_steps uu____3680 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____3696 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____3696
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____3710 =
        let uu____3713 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____3713  in
      FStar_Util.is_some uu____3710
  
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
      let uu____3826 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____3826 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____3862 = FStar_Syntax_Embeddings.embed emb x  in
        uu____3862 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____3895 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____3895 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____3910 .
    'Auu____3910 ->
      FStar_Range.range -> 'Auu____3910 FStar_Syntax_Syntax.syntax
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
    let uu____4031 =
      let uu____4040 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____4040  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4031  in
  let arg_as_bounded_int1 uu____4070 =
    match uu____4070 with
    | (a,uu____4084) ->
        let uu____4095 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____4095 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____4139 =
               let uu____4154 =
                 let uu____4155 = FStar_Syntax_Subst.compress hd1  in
                 uu____4155.FStar_Syntax_Syntax.n  in
               (uu____4154, args)  in
             (match uu____4139 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____4176)::[]) when
                  (let uu____4213 =
                     FStar_Ident.text_of_lid
                       (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   FStar_Util.ends_with uu____4213 "int_to_t") ||
                    (let uu____4217 =
                       FStar_Ident.text_of_lid
                         (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        in
                     FStar_Util.ends_with uu____4217 "Mk")
                  ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____4221 =
                    let uu____4222 = FStar_Syntax_Subst.compress arg1  in
                    uu____4222.FStar_Syntax_Syntax.n  in
                  (match uu____4221 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____4244 =
                         let uu____4249 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____4249)  in
                       FStar_Pervasives_Native.Some uu____4244
                   | uu____4254 -> FStar_Pervasives_Native.None)
              | uu____4259 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4321 = f a  in FStar_Pervasives_Native.Some uu____4321
    | uu____4322 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4378 = f a0 a1  in FStar_Pervasives_Native.Some uu____4378
    | uu____4379 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____4446 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____4446  in
  let binary_op1 as_a f res n1 args =
    let uu____4528 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____4528  in
  let as_primitive_step is_strong uu____4583 =
    match uu____4583 with
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
           let uu____4691 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____4691)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4733 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____4733)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____4774 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____4774)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4827 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____4827)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4880 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____4880)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____5033 =
          let uu____5042 = as_a a  in
          let uu____5045 = as_b b  in (uu____5042, uu____5045)  in
        (match uu____5033 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5060 =
               let uu____5061 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5061  in
             FStar_Pervasives_Native.Some uu____5060
         | uu____5062 -> FStar_Pervasives_Native.None)
    | uu____5071 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____5093 =
        let uu____5094 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5094  in
      mk uu____5093 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5108 =
      let uu____5111 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5111  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5108  in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5159 =
      let uu____5160 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5160  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____5159  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____5246 = arg_as_string1 a1  in
        (match uu____5246 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5255 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____5255 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5273 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____5273
              | uu____5275 -> FStar_Pervasives_Native.None)
         | uu____5281 -> FStar_Pervasives_Native.None)
    | uu____5285 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5366 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____5366 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5382 = arg_as_string1 a2  in
             (match uu____5382 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____5395 =
                    let uu____5396 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____5396 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5395
              | uu____5406 -> FStar_Pervasives_Native.None)
         | uu____5410 -> FStar_Pervasives_Native.None)
    | uu____5416 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____5454 =
          let uu____5468 = arg_as_string1 a1  in
          let uu____5472 = arg_as_int1 a2  in
          let uu____5475 = arg_as_int1 a3  in
          (uu____5468, uu____5472, uu____5475)  in
        (match uu____5454 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___501_5508  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____5513 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5513) ()
              with | uu___500_5516 -> FStar_Pervasives_Native.None)
         | uu____5519 -> FStar_Pervasives_Native.None)
    | uu____5533 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5547 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____5547  in
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
        let uu____5626 =
          let uu____5636 = arg_as_string1 a1  in
          let uu____5640 = arg_as_int1 a2  in (uu____5636, uu____5640)  in
        (match uu____5626 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___535_5664  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____5669 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5669) ()
              with | uu___534_5672 -> FStar_Pervasives_Native.None)
         | uu____5675 -> FStar_Pervasives_Native.None)
    | uu____5685 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5716 =
          let uu____5727 = arg_as_string1 a1  in
          let uu____5731 = arg_as_char1 a2  in (uu____5727, uu____5731)  in
        (match uu____5716 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___556_5760  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____5764 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5764) ()
              with | uu___555_5766 -> FStar_Pervasives_Native.None)
         | uu____5769 -> FStar_Pervasives_Native.None)
    | uu____5780 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5814 =
          let uu____5836 = arg_as_string1 fn  in
          let uu____5840 = arg_as_int1 from_line  in
          let uu____5843 = arg_as_int1 from_col  in
          let uu____5846 = arg_as_int1 to_line  in
          let uu____5849 = arg_as_int1 to_col  in
          (uu____5836, uu____5840, uu____5843, uu____5846, uu____5849)  in
        (match uu____5814 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5884 =
                 let uu____5885 = FStar_BigInt.to_int_fs from_l  in
                 let uu____5887 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____5885 uu____5887  in
               let uu____5889 =
                 let uu____5890 = FStar_BigInt.to_int_fs to_l  in
                 let uu____5892 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____5890 uu____5892  in
               FStar_Range.mk_range fn1 uu____5884 uu____5889  in
             let uu____5894 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____5894
         | uu____5895 -> FStar_Pervasives_Native.None)
    | uu____5917 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____5961)::(a1,uu____5963)::(a2,uu____5965)::[] ->
        let uu____6022 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6022 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6031 -> FStar_Pervasives_Native.None)
    | uu____6032 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____6075)::[] ->
        let uu____6092 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____6092 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6098 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6098
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6099 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____6119  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____6153 =
      let uu____6183 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)), uu____6183)
       in
    let uu____6217 =
      let uu____6249 =
        let uu____6279 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____6279)
         in
      let uu____6319 =
        let uu____6351 =
          let uu____6381 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____6381)
           in
        let uu____6421 =
          let uu____6453 =
            let uu____6483 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____6483)
             in
          let uu____6523 =
            let uu____6555 =
              let uu____6585 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____6585)
               in
            let uu____6625 =
              let uu____6657 =
                let uu____6687 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____6699 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____6699)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____6730 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____6730)), uu____6687)
                 in
              let uu____6733 =
                let uu____6765 =
                  let uu____6795 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____6807 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____6807)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____6838 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____6838)), uu____6795)
                   in
                let uu____6841 =
                  let uu____6873 =
                    let uu____6903 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____6915 = FStar_BigInt.gt_big_int x y  in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____6915)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____6946 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____6946)), uu____6903)
                     in
                  let uu____6949 =
                    let uu____6981 =
                      let uu____7011 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____7023 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____7023)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____7054 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____7054)), uu____7011)
                       in
                    let uu____7057 =
                      let uu____7089 =
                        let uu____7119 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____7119)
                         in
                      let uu____7159 =
                        let uu____7191 =
                          let uu____7221 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____7221)
                           in
                        let uu____7257 =
                          let uu____7289 =
                            let uu____7319 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____7319)
                             in
                          let uu____7363 =
                            let uu____7395 =
                              let uu____7425 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____7425)
                               in
                            let uu____7469 =
                              let uu____7501 =
                                let uu____7531 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____7531)
                                 in
                              let uu____7559 =
                                let uu____7591 =
                                  let uu____7621 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____7621)
                                   in
                                let uu____7651 =
                                  let uu____7683 =
                                    let uu____7713 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____7713)
                                     in
                                  let uu____7743 =
                                    let uu____7775 =
                                      let uu____7805 =
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
                                           string_of_list'1), uu____7805)
                                       in
                                    let uu____7841 =
                                      let uu____7873 =
                                        let uu____7905 =
                                          let uu____7937 =
                                            let uu____7967 =
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
                                              uu____7967)
                                             in
                                          let uu____8011 =
                                            let uu____8043 =
                                              let uu____8075 =
                                                let uu____8105 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____8105)
                                                 in
                                              let uu____8135 =
                                                let uu____8167 =
                                                  let uu____8197 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____8197)
                                                   in
                                                let uu____8227 =
                                                  let uu____8259 =
                                                    let uu____8289 =
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
                                                      uu____8289)
                                                     in
                                                  let uu____8319 =
                                                    let uu____8351 =
                                                      let uu____8383 =
                                                        let uu____8415 =
                                                          let uu____8447 =
                                                            let uu____8479 =
                                                              let uu____8511
                                                                =
                                                                let uu____8541
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____8541,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____8568
                                                                =
                                                                let uu____8600
                                                                  =
                                                                  let uu____8630
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____8630,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____8600]
                                                                 in
                                                              uu____8511 ::
                                                                uu____8568
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____8479
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____8447
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____8415
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____8383
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____8351
                                                     in
                                                  uu____8259 :: uu____8319
                                                   in
                                                uu____8167 :: uu____8227  in
                                              uu____8075 :: uu____8135  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____8043
                                             in
                                          uu____7937 :: uu____8011  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____7905
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
                                                  let uu____9277 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____9277 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____9288 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____9288
                                                  y)))
                                        :: uu____7873
                                       in
                                    uu____7775 :: uu____7841  in
                                  uu____7683 :: uu____7743  in
                                uu____7591 :: uu____7651  in
                              uu____7501 :: uu____7559  in
                            uu____7395 :: uu____7469  in
                          uu____7289 :: uu____7363  in
                        uu____7191 :: uu____7257  in
                      uu____7089 :: uu____7159  in
                    uu____6981 :: uu____7057  in
                  uu____6873 :: uu____6949  in
                uu____6765 :: uu____6841  in
              uu____6657 :: uu____6733  in
            uu____6555 :: uu____6625  in
          uu____6453 :: uu____6523  in
        uu____6351 :: uu____6421  in
      uu____6249 :: uu____6319  in
    uu____6153 :: uu____6217  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = []  in
    let bounded_unsigned_int_types = ["UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9908 =
        let uu____9913 =
          let uu____9914 = FStar_Syntax_Syntax.as_arg c  in [uu____9914]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9913  in
      uu____9908 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____10041 =
                let uu____10071 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____10078 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10096  ->
                       fun uu____10097  ->
                         match (uu____10096, uu____10097) with
                         | ((int_to_t1,x),(uu____10116,y)) ->
                             let uu____10126 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____10126)
                   in
                (uu____10071, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____10161  ->
                          fun uu____10162  ->
                            match (uu____10161, uu____10162) with
                            | ((int_to_t1,x),(uu____10181,y)) ->
                                let uu____10191 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____10191)),
                  uu____10078)
                 in
              let uu____10192 =
                let uu____10224 =
                  let uu____10254 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____10261 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____10279  ->
                         fun uu____10280  ->
                           match (uu____10279, uu____10280) with
                           | ((int_to_t1,x),(uu____10299,y)) ->
                               let uu____10309 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____10309)
                     in
                  (uu____10254, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____10344  ->
                            fun uu____10345  ->
                              match (uu____10344, uu____10345) with
                              | ((int_to_t1,x),(uu____10364,y)) ->
                                  let uu____10374 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____10374)),
                    uu____10261)
                   in
                let uu____10375 =
                  let uu____10407 =
                    let uu____10437 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____10444 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____10462  ->
                           fun uu____10463  ->
                             match (uu____10462, uu____10463) with
                             | ((int_to_t1,x),(uu____10482,y)) ->
                                 let uu____10492 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____10492)
                       in
                    (uu____10437, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____10527  ->
                              fun uu____10528  ->
                                match (uu____10527, uu____10528) with
                                | ((int_to_t1,x),(uu____10547,y)) ->
                                    let uu____10557 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____10557)),
                      uu____10444)
                     in
                  let uu____10558 =
                    let uu____10590 =
                      let uu____10620 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____10627 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____10641  ->
                             match uu____10641 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____10620, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____10678  ->
                                match uu____10678 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____10627)
                       in
                    [uu____10590]  in
                  uu____10407 :: uu____10558  in
                uu____10224 :: uu____10375  in
              uu____10041 :: uu____10192))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____10931 =
                let uu____10961 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____10968 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10986  ->
                       fun uu____10987  ->
                         match (uu____10986, uu____10987) with
                         | ((int_to_t1,x),(uu____11006,y)) ->
                             let uu____11016 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11016)
                   in
                (uu____10961, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11051  ->
                          fun uu____11052  ->
                            match (uu____11051, uu____11052) with
                            | ((int_to_t1,x),(uu____11071,y)) ->
                                let uu____11081 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11081)),
                  uu____10968)
                 in
              let uu____11082 =
                let uu____11114 =
                  let uu____11144 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____11151 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11169  ->
                         fun uu____11170  ->
                           match (uu____11169, uu____11170) with
                           | ((int_to_t1,x),(uu____11189,y)) ->
                               let uu____11199 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11199)
                     in
                  (uu____11144, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11234  ->
                            fun uu____11235  ->
                              match (uu____11234, uu____11235) with
                              | ((int_to_t1,x),(uu____11254,y)) ->
                                  let uu____11264 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11264)),
                    uu____11151)
                   in
                [uu____11114]  in
              uu____10931 :: uu____11082))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____11370 ->
          let uu____11372 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____11372
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____11476 =
                let uu____11506 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____11513 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11531  ->
                       fun uu____11532  ->
                         match (uu____11531, uu____11532) with
                         | ((int_to_t1,x),(uu____11551,y)) ->
                             let uu____11561 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11561)
                   in
                (uu____11506, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11596  ->
                          fun uu____11597  ->
                            match (uu____11596, uu____11597) with
                            | ((int_to_t1,x),(uu____11616,y)) ->
                                let uu____11626 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11626)),
                  uu____11513)
                 in
              let uu____11627 =
                let uu____11659 =
                  let uu____11689 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____11696 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11714  ->
                         fun uu____11715  ->
                           match (uu____11714, uu____11715) with
                           | ((int_to_t1,x),(uu____11734,y)) ->
                               let uu____11744 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11744)
                     in
                  (uu____11689, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11779  ->
                            fun uu____11780  ->
                              match (uu____11779, uu____11780) with
                              | ((int_to_t1,x),(uu____11799,y)) ->
                                  let uu____11809 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11809)),
                    uu____11696)
                   in
                let uu____11810 =
                  let uu____11842 =
                    let uu____11872 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____11879 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____11897  ->
                           fun uu____11898  ->
                             match (uu____11897, uu____11898) with
                             | ((int_to_t1,x),(uu____11917,y)) ->
                                 let uu____11927 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____11927)
                       in
                    (uu____11872, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____11962  ->
                              fun uu____11963  ->
                                match (uu____11962, uu____11963) with
                                | ((int_to_t1,x),(uu____11982,y)) ->
                                    let uu____11992 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____11992)),
                      uu____11879)
                     in
                  let uu____11993 =
                    let uu____12025 =
                      let uu____12055 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____12062 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____12077  ->
                             match uu____12077 with
                             | (int_to_t1,x) ->
                                 let uu____12084 =
                                   let uu____12085 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____12086 = mask m  in
                                   FStar_BigInt.logand_big_int uu____12085
                                     uu____12086
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____12084)
                         in
                      (uu____12055, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____12118  ->
                                match uu____12118 with
                                | (int_to_t1,x) ->
                                    let uu____12125 =
                                      let uu____12126 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____12127 = mask m  in
                                      FStar_BigInt.logand_big_int uu____12126
                                        uu____12127
                                       in
                                    int_as_bounded1 r int_to_t1 uu____12125)),
                        uu____12062)
                       in
                    let uu____12128 =
                      let uu____12160 =
                        let uu____12190 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____12197 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____12215  ->
                               fun uu____12216  ->
                                 match (uu____12215, uu____12216) with
                                 | ((int_to_t1,x),(uu____12235,y)) ->
                                     let uu____12245 =
                                       let uu____12246 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____12247 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____12246 uu____12247
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____12245)
                           in
                        (uu____12190, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____12282  ->
                                  fun uu____12283  ->
                                    match (uu____12282, uu____12283) with
                                    | ((int_to_t1,x),(uu____12302,y)) ->
                                        let uu____12312 =
                                          let uu____12313 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____12314 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____12313 uu____12314
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____12312)), uu____12197)
                         in
                      let uu____12315 =
                        let uu____12347 =
                          let uu____12377 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____12384 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____12402  ->
                                 fun uu____12403  ->
                                   match (uu____12402, uu____12403) with
                                   | ((int_to_t1,x),(uu____12422,y)) ->
                                       let uu____12432 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____12432)
                             in
                          (uu____12377, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____12467  ->
                                    fun uu____12468  ->
                                      match (uu____12467, uu____12468) with
                                      | ((int_to_t1,x),(uu____12487,y)) ->
                                          let uu____12497 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____12497)), uu____12384)
                           in
                        [uu____12347]  in
                      uu____12160 :: uu____12315  in
                    uu____12025 :: uu____12128  in
                  uu____11842 :: uu____11993  in
                uu____11659 :: uu____11810  in
              uu____11476 :: uu____11627))
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
    | (_typ,uu____12889)::(a1,uu____12891)::(a2,uu____12893)::[] ->
        let uu____12950 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____12950 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___876_12954 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___876_12954.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___876_12954.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___879_12956 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___879_12956.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___879_12956.FStar_Syntax_Syntax.vars)
                })
         | uu____12957 -> FStar_Pervasives_Native.None)
    | uu____12958 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____12988)::(t2,uu____12990)::(a1,uu____12992)::(a2,uu____12994)::[]
        ->
        let uu____13067 =
          let uu____13068 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____13069 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____13068 uu____13069  in
        (match uu____13067 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___902_13073 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___902_13073.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___902_13073.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___905_13075 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___905_13075.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___905_13075.FStar_Syntax_Syntax.vars)
                })
         | uu____13076 -> FStar_Pervasives_Native.None)
    | uu____13077 -> failwith "Unexpected number of arguments"  in
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
  fun uu____13108  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____13125 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____13125 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____13154 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____13154 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____13165  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____13236  ->
           fun uu____13237  ->
             match (uu____13236, uu____13237) with
             | ((uu____13263,t1),(uu____13265,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____13299  ->
         fun rest  ->
           match uu____13299 with
           | (nm,ms) ->
               let uu____13315 =
                 let uu____13317 =
                   let uu____13319 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____13319  in
                 FStar_Util.format2 "%sms --- %s\n" uu____13317 nm  in
               FStar_String.op_Hat uu____13315 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____13350 =
      let uu____13353 = FStar_ST.op_Bang plugins  in p :: uu____13353  in
    FStar_ST.op_Colon_Equals plugins uu____13350  in
  let retrieve uu____13409 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____13462  ->
    let uu____13463 = FStar_Options.no_plugins ()  in
    if uu____13463 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____13484 = FStar_Options.use_nbe ()  in
    if uu____13484
    then
      let uu___948_13487 = s  in
      {
        beta = (uu___948_13487.beta);
        iota = (uu___948_13487.iota);
        zeta = (uu___948_13487.zeta);
        weak = (uu___948_13487.weak);
        hnf = (uu___948_13487.hnf);
        primops = (uu___948_13487.primops);
        do_not_unfold_pure_lets = (uu___948_13487.do_not_unfold_pure_lets);
        unfold_until = (uu___948_13487.unfold_until);
        unfold_only = (uu___948_13487.unfold_only);
        unfold_fully = (uu___948_13487.unfold_fully);
        unfold_attr = (uu___948_13487.unfold_attr);
        unfold_tac = (uu___948_13487.unfold_tac);
        pure_subterms_within_computations =
          (uu___948_13487.pure_subterms_within_computations);
        simplify = (uu___948_13487.simplify);
        erase_universes = (uu___948_13487.erase_universes);
        allow_unbound_universes = (uu___948_13487.allow_unbound_universes);
        reify_ = (uu___948_13487.reify_);
        compress_uvars = (uu___948_13487.compress_uvars);
        no_full_norm = (uu___948_13487.no_full_norm);
        check_no_uvars = (uu___948_13487.check_no_uvars);
        unmeta = (uu___948_13487.unmeta);
        unascribe = (uu___948_13487.unascribe);
        in_full_norm_request = (uu___948_13487.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___948_13487.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___948_13487.for_extraction)
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
               (fun uu___0_13524  ->
                  match uu___0_13524 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding b ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only b]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____13530 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____13536 -> d  in
        let uu____13539 =
          let uu____13540 = to_fsteps s  in
          FStar_All.pipe_right uu____13540 add_nbe  in
        let uu____13541 =
          let uu____13542 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____13545 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____13548 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____13551 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____13554 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____13557 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____13560 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____13563 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____13566 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____13542;
            top = uu____13545;
            cfg = uu____13548;
            primop = uu____13551;
            unfolding = uu____13554;
            b380 = uu____13557;
            wpe = uu____13560;
            norm_delayed = uu____13563;
            print_normalized = uu____13566
          }  in
        let uu____13569 =
          let uu____13572 =
            let uu____13575 = retrieve_plugins ()  in
            FStar_List.append uu____13575 psteps  in
          add_steps built_in_primitive_steps uu____13572  in
        let uu____13578 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____13581 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____13581)
           in
        {
          steps = uu____13539;
          tcenv = e;
          debug = uu____13541;
          delta_level = d1;
          primitive_steps = uu____13569;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____13578;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 