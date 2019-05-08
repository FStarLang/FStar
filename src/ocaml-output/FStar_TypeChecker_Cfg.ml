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
                  let uu____4221 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____4221 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____4225 =
                    let uu____4226 = FStar_Syntax_Subst.compress arg1  in
                    uu____4226.FStar_Syntax_Syntax.n  in
                  (match uu____4225 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____4248 =
                         let uu____4253 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____4253)  in
                       FStar_Pervasives_Native.Some uu____4248
                   | uu____4258 -> FStar_Pervasives_Native.None)
              | uu____4263 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4325 = f a  in FStar_Pervasives_Native.Some uu____4325
    | uu____4326 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4382 = f a0 a1  in FStar_Pervasives_Native.Some uu____4382
    | uu____4383 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____4450 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____4450  in
  let binary_op1 as_a f res n1 args =
    let uu____4532 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____4532  in
  let as_primitive_step is_strong uu____4587 =
    match uu____4587 with
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
           let uu____4695 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____4695)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4737 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____4737)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____4778 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____4778)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4831 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____4831)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4884 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____4884)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____5037 =
          let uu____5046 = as_a a  in
          let uu____5049 = as_b b  in (uu____5046, uu____5049)  in
        (match uu____5037 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5064 =
               let uu____5065 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5065  in
             FStar_Pervasives_Native.Some uu____5064
         | uu____5066 -> FStar_Pervasives_Native.None)
    | uu____5075 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____5097 =
        let uu____5098 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5098  in
      mk uu____5097 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5112 =
      let uu____5115 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5115  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5112  in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5163 =
      let uu____5164 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5164  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____5163  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____5250 = arg_as_string1 a1  in
        (match uu____5250 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5259 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____5259 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5277 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____5277
              | uu____5279 -> FStar_Pervasives_Native.None)
         | uu____5285 -> FStar_Pervasives_Native.None)
    | uu____5289 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5370 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____5370 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5386 = arg_as_string1 a2  in
             (match uu____5386 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____5399 =
                    let uu____5400 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____5400 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5399
              | uu____5410 -> FStar_Pervasives_Native.None)
         | uu____5414 -> FStar_Pervasives_Native.None)
    | uu____5420 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____5458 =
          let uu____5472 = arg_as_string1 a1  in
          let uu____5476 = arg_as_int1 a2  in
          let uu____5479 = arg_as_int1 a3  in
          (uu____5472, uu____5476, uu____5479)  in
        (match uu____5458 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___500_5512  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____5517 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5517) ()
              with | uu___499_5520 -> FStar_Pervasives_Native.None)
         | uu____5523 -> FStar_Pervasives_Native.None)
    | uu____5537 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5551 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____5551  in
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
        let uu____5630 =
          let uu____5640 = arg_as_string1 a1  in
          let uu____5644 = arg_as_int1 a2  in (uu____5640, uu____5644)  in
        (match uu____5630 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___534_5668  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____5673 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5673) ()
              with | uu___533_5676 -> FStar_Pervasives_Native.None)
         | uu____5679 -> FStar_Pervasives_Native.None)
    | uu____5689 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5720 =
          let uu____5731 = arg_as_string1 a1  in
          let uu____5735 = arg_as_char1 a2  in (uu____5731, uu____5735)  in
        (match uu____5720 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___555_5764  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____5768 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5768) ()
              with | uu___554_5770 -> FStar_Pervasives_Native.None)
         | uu____5773 -> FStar_Pervasives_Native.None)
    | uu____5784 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5818 =
          let uu____5840 = arg_as_string1 fn  in
          let uu____5844 = arg_as_int1 from_line  in
          let uu____5847 = arg_as_int1 from_col  in
          let uu____5850 = arg_as_int1 to_line  in
          let uu____5853 = arg_as_int1 to_col  in
          (uu____5840, uu____5844, uu____5847, uu____5850, uu____5853)  in
        (match uu____5818 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5888 =
                 let uu____5889 = FStar_BigInt.to_int_fs from_l  in
                 let uu____5891 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____5889 uu____5891  in
               let uu____5893 =
                 let uu____5894 = FStar_BigInt.to_int_fs to_l  in
                 let uu____5896 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____5894 uu____5896  in
               FStar_Range.mk_range fn1 uu____5888 uu____5893  in
             let uu____5898 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____5898
         | uu____5899 -> FStar_Pervasives_Native.None)
    | uu____5921 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____5965)::(a1,uu____5967)::(a2,uu____5969)::[] ->
        let uu____6026 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6026 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6035 -> FStar_Pervasives_Native.None)
    | uu____6036 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____6079)::[] ->
        let uu____6096 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____6096 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6102 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6102
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6103 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____6123  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____6157 =
      let uu____6187 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)), uu____6187)
       in
    let uu____6221 =
      let uu____6253 =
        let uu____6283 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____6283)
         in
      let uu____6323 =
        let uu____6355 =
          let uu____6385 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____6385)
           in
        let uu____6425 =
          let uu____6457 =
            let uu____6487 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____6487)
             in
          let uu____6527 =
            let uu____6559 =
              let uu____6589 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____6589)
               in
            let uu____6629 =
              let uu____6661 =
                let uu____6691 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____6703 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____6703)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____6734 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____6734)), uu____6691)
                 in
              let uu____6737 =
                let uu____6769 =
                  let uu____6799 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____6811 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____6811)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____6842 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____6842)), uu____6799)
                   in
                let uu____6845 =
                  let uu____6877 =
                    let uu____6907 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____6919 = FStar_BigInt.gt_big_int x y  in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____6919)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____6950 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____6950)), uu____6907)
                     in
                  let uu____6953 =
                    let uu____6985 =
                      let uu____7015 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____7027 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____7027)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____7058 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____7058)), uu____7015)
                       in
                    let uu____7061 =
                      let uu____7093 =
                        let uu____7123 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____7123)
                         in
                      let uu____7163 =
                        let uu____7195 =
                          let uu____7225 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____7225)
                           in
                        let uu____7261 =
                          let uu____7293 =
                            let uu____7323 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____7323)
                             in
                          let uu____7367 =
                            let uu____7399 =
                              let uu____7429 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____7429)
                               in
                            let uu____7473 =
                              let uu____7505 =
                                let uu____7535 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____7535)
                                 in
                              let uu____7563 =
                                let uu____7595 =
                                  let uu____7625 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____7625)
                                   in
                                let uu____7655 =
                                  let uu____7687 =
                                    let uu____7717 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____7717)
                                     in
                                  let uu____7747 =
                                    let uu____7779 =
                                      let uu____7809 =
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
                                           string_of_list'1), uu____7809)
                                       in
                                    let uu____7845 =
                                      let uu____7877 =
                                        let uu____7909 =
                                          let uu____7941 =
                                            let uu____7971 =
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
                                              uu____7971)
                                             in
                                          let uu____8015 =
                                            let uu____8047 =
                                              let uu____8079 =
                                                let uu____8109 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____8109)
                                                 in
                                              let uu____8139 =
                                                let uu____8171 =
                                                  let uu____8201 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____8201)
                                                   in
                                                let uu____8231 =
                                                  let uu____8263 =
                                                    let uu____8293 =
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
                                                      uu____8293)
                                                     in
                                                  let uu____8323 =
                                                    let uu____8355 =
                                                      let uu____8387 =
                                                        let uu____8419 =
                                                          let uu____8451 =
                                                            let uu____8483 =
                                                              let uu____8515
                                                                =
                                                                let uu____8545
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____8545,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____8572
                                                                =
                                                                let uu____8604
                                                                  =
                                                                  let uu____8634
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____8634,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____8604]
                                                                 in
                                                              uu____8515 ::
                                                                uu____8572
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____8483
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____8451
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____8419
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____8387
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____8355
                                                     in
                                                  uu____8263 :: uu____8323
                                                   in
                                                uu____8171 :: uu____8231  in
                                              uu____8079 :: uu____8139  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____8047
                                             in
                                          uu____7941 :: uu____8015  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____7909
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
                                                  let uu____9281 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____9281 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____9292 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____9292
                                                  y)))
                                        :: uu____7877
                                       in
                                    uu____7779 :: uu____7845  in
                                  uu____7687 :: uu____7747  in
                                uu____7595 :: uu____7655  in
                              uu____7505 :: uu____7563  in
                            uu____7399 :: uu____7473  in
                          uu____7293 :: uu____7367  in
                        uu____7195 :: uu____7261  in
                      uu____7093 :: uu____7163  in
                    uu____6985 :: uu____7061  in
                  uu____6877 :: uu____6953  in
                uu____6769 :: uu____6845  in
              uu____6661 :: uu____6737  in
            uu____6559 :: uu____6629  in
          uu____6457 :: uu____6527  in
        uu____6355 :: uu____6425  in
      uu____6253 :: uu____6323  in
    uu____6157 :: uu____6221  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9928 =
        let uu____9933 =
          let uu____9934 = FStar_Syntax_Syntax.as_arg c  in [uu____9934]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9933  in
      uu____9928 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____10061 =
                let uu____10091 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____10098 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10116  ->
                       fun uu____10117  ->
                         match (uu____10116, uu____10117) with
                         | ((int_to_t1,x),(uu____10136,y)) ->
                             let uu____10146 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____10146)
                   in
                (uu____10091, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____10181  ->
                          fun uu____10182  ->
                            match (uu____10181, uu____10182) with
                            | ((int_to_t1,x),(uu____10201,y)) ->
                                let uu____10211 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____10211)),
                  uu____10098)
                 in
              let uu____10212 =
                let uu____10244 =
                  let uu____10274 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____10281 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____10299  ->
                         fun uu____10300  ->
                           match (uu____10299, uu____10300) with
                           | ((int_to_t1,x),(uu____10319,y)) ->
                               let uu____10329 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____10329)
                     in
                  (uu____10274, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____10364  ->
                            fun uu____10365  ->
                              match (uu____10364, uu____10365) with
                              | ((int_to_t1,x),(uu____10384,y)) ->
                                  let uu____10394 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____10394)),
                    uu____10281)
                   in
                let uu____10395 =
                  let uu____10427 =
                    let uu____10457 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____10464 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____10482  ->
                           fun uu____10483  ->
                             match (uu____10482, uu____10483) with
                             | ((int_to_t1,x),(uu____10502,y)) ->
                                 let uu____10512 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____10512)
                       in
                    (uu____10457, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____10547  ->
                              fun uu____10548  ->
                                match (uu____10547, uu____10548) with
                                | ((int_to_t1,x),(uu____10567,y)) ->
                                    let uu____10577 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____10577)),
                      uu____10464)
                     in
                  let uu____10578 =
                    let uu____10610 =
                      let uu____10640 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____10647 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____10661  ->
                             match uu____10661 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____10640, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____10698  ->
                                match uu____10698 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____10647)
                       in
                    [uu____10610]  in
                  uu____10427 :: uu____10578  in
                uu____10244 :: uu____10395  in
              uu____10061 :: uu____10212))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____10951 =
                let uu____10981 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____10988 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11006  ->
                       fun uu____11007  ->
                         match (uu____11006, uu____11007) with
                         | ((int_to_t1,x),(uu____11026,y)) ->
                             let uu____11036 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11036)
                   in
                (uu____10981, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11071  ->
                          fun uu____11072  ->
                            match (uu____11071, uu____11072) with
                            | ((int_to_t1,x),(uu____11091,y)) ->
                                let uu____11101 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11101)),
                  uu____10988)
                 in
              let uu____11102 =
                let uu____11134 =
                  let uu____11164 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____11171 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11189  ->
                         fun uu____11190  ->
                           match (uu____11189, uu____11190) with
                           | ((int_to_t1,x),(uu____11209,y)) ->
                               let uu____11219 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11219)
                     in
                  (uu____11164, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11254  ->
                            fun uu____11255  ->
                              match (uu____11254, uu____11255) with
                              | ((int_to_t1,x),(uu____11274,y)) ->
                                  let uu____11284 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11284)),
                    uu____11171)
                   in
                [uu____11134]  in
              uu____10951 :: uu____11102))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____11390 ->
          let uu____11392 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____11392
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____11496 =
                let uu____11526 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____11533 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11551  ->
                       fun uu____11552  ->
                         match (uu____11551, uu____11552) with
                         | ((int_to_t1,x),(uu____11571,y)) ->
                             let uu____11581 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11581)
                   in
                (uu____11526, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11616  ->
                          fun uu____11617  ->
                            match (uu____11616, uu____11617) with
                            | ((int_to_t1,x),(uu____11636,y)) ->
                                let uu____11646 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11646)),
                  uu____11533)
                 in
              let uu____11647 =
                let uu____11679 =
                  let uu____11709 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____11716 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11734  ->
                         fun uu____11735  ->
                           match (uu____11734, uu____11735) with
                           | ((int_to_t1,x),(uu____11754,y)) ->
                               let uu____11764 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11764)
                     in
                  (uu____11709, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11799  ->
                            fun uu____11800  ->
                              match (uu____11799, uu____11800) with
                              | ((int_to_t1,x),(uu____11819,y)) ->
                                  let uu____11829 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11829)),
                    uu____11716)
                   in
                let uu____11830 =
                  let uu____11862 =
                    let uu____11892 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____11899 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____11917  ->
                           fun uu____11918  ->
                             match (uu____11917, uu____11918) with
                             | ((int_to_t1,x),(uu____11937,y)) ->
                                 let uu____11947 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____11947)
                       in
                    (uu____11892, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____11982  ->
                              fun uu____11983  ->
                                match (uu____11982, uu____11983) with
                                | ((int_to_t1,x),(uu____12002,y)) ->
                                    let uu____12012 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____12012)),
                      uu____11899)
                     in
                  let uu____12013 =
                    let uu____12045 =
                      let uu____12075 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____12082 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____12097  ->
                             match uu____12097 with
                             | (int_to_t1,x) ->
                                 let uu____12104 =
                                   let uu____12105 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____12106 = mask m  in
                                   FStar_BigInt.logand_big_int uu____12105
                                     uu____12106
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____12104)
                         in
                      (uu____12075, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____12138  ->
                                match uu____12138 with
                                | (int_to_t1,x) ->
                                    let uu____12145 =
                                      let uu____12146 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____12147 = mask m  in
                                      FStar_BigInt.logand_big_int uu____12146
                                        uu____12147
                                       in
                                    int_as_bounded1 r int_to_t1 uu____12145)),
                        uu____12082)
                       in
                    let uu____12148 =
                      let uu____12180 =
                        let uu____12210 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____12217 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____12235  ->
                               fun uu____12236  ->
                                 match (uu____12235, uu____12236) with
                                 | ((int_to_t1,x),(uu____12255,y)) ->
                                     let uu____12265 =
                                       let uu____12266 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____12267 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____12266 uu____12267
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____12265)
                           in
                        (uu____12210, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____12302  ->
                                  fun uu____12303  ->
                                    match (uu____12302, uu____12303) with
                                    | ((int_to_t1,x),(uu____12322,y)) ->
                                        let uu____12332 =
                                          let uu____12333 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____12334 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____12333 uu____12334
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____12332)), uu____12217)
                         in
                      let uu____12335 =
                        let uu____12367 =
                          let uu____12397 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____12404 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____12422  ->
                                 fun uu____12423  ->
                                   match (uu____12422, uu____12423) with
                                   | ((int_to_t1,x),(uu____12442,y)) ->
                                       let uu____12452 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____12452)
                             in
                          (uu____12397, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____12487  ->
                                    fun uu____12488  ->
                                      match (uu____12487, uu____12488) with
                                      | ((int_to_t1,x),(uu____12507,y)) ->
                                          let uu____12517 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____12517)), uu____12404)
                           in
                        [uu____12367]  in
                      uu____12180 :: uu____12335  in
                    uu____12045 :: uu____12148  in
                  uu____11862 :: uu____12013  in
                uu____11679 :: uu____11830  in
              uu____11496 :: uu____11647))
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
    | (_typ,uu____12909)::(a1,uu____12911)::(a2,uu____12913)::[] ->
        let uu____12970 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____12970 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___875_12974 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___875_12974.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___875_12974.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___878_12976 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___878_12976.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___878_12976.FStar_Syntax_Syntax.vars)
                })
         | uu____12977 -> FStar_Pervasives_Native.None)
    | uu____12978 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____13008)::(t2,uu____13010)::(a1,uu____13012)::(a2,uu____13014)::[]
        ->
        let uu____13087 =
          let uu____13088 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____13089 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____13088 uu____13089  in
        (match uu____13087 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___901_13093 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___901_13093.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___901_13093.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___904_13095 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___904_13095.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___904_13095.FStar_Syntax_Syntax.vars)
                })
         | uu____13096 -> FStar_Pervasives_Native.None)
    | uu____13097 -> failwith "Unexpected number of arguments"  in
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
  fun uu____13128  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____13145 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____13145 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____13174 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____13174 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____13185  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____13256  ->
           fun uu____13257  ->
             match (uu____13256, uu____13257) with
             | ((uu____13283,t1),(uu____13285,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____13319  ->
         fun rest  ->
           match uu____13319 with
           | (nm,ms) ->
               let uu____13335 =
                 let uu____13337 =
                   let uu____13339 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____13339  in
                 FStar_Util.format2 "%sms --- %s\n" uu____13337 nm  in
               FStar_String.op_Hat uu____13335 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____13370 =
      let uu____13373 = FStar_ST.op_Bang plugins  in p :: uu____13373  in
    FStar_ST.op_Colon_Equals plugins uu____13370  in
  let retrieve uu____13429 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____13482  ->
    let uu____13483 = FStar_Options.no_plugins ()  in
    if uu____13483 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____13504 = FStar_Options.use_nbe ()  in
    if uu____13504
    then
      let uu___947_13507 = s  in
      {
        beta = (uu___947_13507.beta);
        iota = (uu___947_13507.iota);
        zeta = (uu___947_13507.zeta);
        weak = (uu___947_13507.weak);
        hnf = (uu___947_13507.hnf);
        primops = (uu___947_13507.primops);
        do_not_unfold_pure_lets = (uu___947_13507.do_not_unfold_pure_lets);
        unfold_until = (uu___947_13507.unfold_until);
        unfold_only = (uu___947_13507.unfold_only);
        unfold_fully = (uu___947_13507.unfold_fully);
        unfold_attr = (uu___947_13507.unfold_attr);
        unfold_tac = (uu___947_13507.unfold_tac);
        pure_subterms_within_computations =
          (uu___947_13507.pure_subterms_within_computations);
        simplify = (uu___947_13507.simplify);
        erase_universes = (uu___947_13507.erase_universes);
        allow_unbound_universes = (uu___947_13507.allow_unbound_universes);
        reify_ = (uu___947_13507.reify_);
        compress_uvars = (uu___947_13507.compress_uvars);
        no_full_norm = (uu___947_13507.no_full_norm);
        check_no_uvars = (uu___947_13507.check_no_uvars);
        unmeta = (uu___947_13507.unmeta);
        unascribe = (uu___947_13507.unascribe);
        in_full_norm_request = (uu___947_13507.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___947_13507.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___947_13507.for_extraction)
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
               (fun uu___0_13544  ->
                  match uu___0_13544 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____13548 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____13554 -> d  in
        let uu____13557 =
          let uu____13558 = to_fsteps s  in
          FStar_All.pipe_right uu____13558 add_nbe  in
        let uu____13559 =
          let uu____13560 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____13563 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____13566 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____13569 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____13572 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____13575 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____13578 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____13581 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____13584 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____13560;
            top = uu____13563;
            cfg = uu____13566;
            primop = uu____13569;
            unfolding = uu____13572;
            b380 = uu____13575;
            wpe = uu____13578;
            norm_delayed = uu____13581;
            print_normalized = uu____13584
          }  in
        let uu____13587 =
          let uu____13590 =
            let uu____13593 = retrieve_plugins ()  in
            FStar_List.append uu____13593 psteps  in
          add_steps built_in_primitive_steps uu____13590  in
        let uu____13596 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____13599 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____13599)
           in
        {
          steps = uu____13557;
          tcenv = e;
          debug = uu____13559;
          delta_level = d1;
          primitive_steps = uu____13587;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____13596;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 