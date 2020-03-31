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
          let uu____2100 =
            let uu____2102 = f1 x  in FStar_String.op_Hat uu____2102 ")"  in
          FStar_String.op_Hat "Some (" uu____2100
       in
    let b = FStar_Util.string_of_bool  in
    let uu____2113 =
      let uu____2117 = FStar_All.pipe_right f.beta b  in
      let uu____2121 =
        let uu____2125 = FStar_All.pipe_right f.iota b  in
        let uu____2129 =
          let uu____2133 = FStar_All.pipe_right f.zeta b  in
          let uu____2137 =
            let uu____2141 = FStar_All.pipe_right f.weak b  in
            let uu____2145 =
              let uu____2149 = FStar_All.pipe_right f.hnf b  in
              let uu____2153 =
                let uu____2157 = FStar_All.pipe_right f.primops b  in
                let uu____2161 =
                  let uu____2165 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____2169 =
                    let uu____2173 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____2178 =
                      let uu____2182 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____2196 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____2196
                                  (FStar_String.concat ", ")))
                         in
                      let uu____2206 =
                        let uu____2210 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____2224 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____2224
                                    (FStar_String.concat ", ")))
                           in
                        let uu____2234 =
                          let uu____2238 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____2252 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____2252
                                      (FStar_String.concat ", ")))
                             in
                          let uu____2262 =
                            let uu____2266 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____2270 =
                              let uu____2274 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____2278 =
                                let uu____2282 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____2286 =
                                  let uu____2290 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____2294 =
                                    let uu____2298 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____2302 =
                                      let uu____2306 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____2310 =
                                        let uu____2314 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____2318 =
                                          let uu____2322 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____2326 =
                                            let uu____2330 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____2334 =
                                              let uu____2338 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____2342 =
                                                let uu____2346 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____2350 =
                                                  let uu____2354 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____2358 =
                                                    let uu____2362 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____2362]  in
                                                  uu____2354 :: uu____2358
                                                   in
                                                uu____2346 :: uu____2350  in
                                              uu____2338 :: uu____2342  in
                                            uu____2330 :: uu____2334  in
                                          uu____2322 :: uu____2326  in
                                        uu____2314 :: uu____2318  in
                                      uu____2306 :: uu____2310  in
                                    uu____2298 :: uu____2302  in
                                  uu____2290 :: uu____2294  in
                                uu____2282 :: uu____2286  in
                              uu____2274 :: uu____2278  in
                            uu____2266 :: uu____2270  in
                          uu____2238 :: uu____2262  in
                        uu____2210 :: uu____2234  in
                      uu____2182 :: uu____2206  in
                    uu____2173 :: uu____2178  in
                  uu____2165 :: uu____2169  in
                uu____2157 :: uu____2161  in
              uu____2149 :: uu____2153  in
            uu____2141 :: uu____2145  in
          uu____2133 :: uu____2137  in
        uu____2125 :: uu____2129  in
      uu____2117 :: uu____2121  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____2113
  
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
          let uu___94_2432 = fs  in
          {
            beta = true;
            iota = (uu___94_2432.iota);
            zeta = (uu___94_2432.zeta);
            weak = (uu___94_2432.weak);
            hnf = (uu___94_2432.hnf);
            primops = (uu___94_2432.primops);
            do_not_unfold_pure_lets = (uu___94_2432.do_not_unfold_pure_lets);
            unfold_until = (uu___94_2432.unfold_until);
            unfold_only = (uu___94_2432.unfold_only);
            unfold_fully = (uu___94_2432.unfold_fully);
            unfold_attr = (uu___94_2432.unfold_attr);
            unfold_tac = (uu___94_2432.unfold_tac);
            pure_subterms_within_computations =
              (uu___94_2432.pure_subterms_within_computations);
            simplify = (uu___94_2432.simplify);
            erase_universes = (uu___94_2432.erase_universes);
            allow_unbound_universes = (uu___94_2432.allow_unbound_universes);
            reify_ = (uu___94_2432.reify_);
            compress_uvars = (uu___94_2432.compress_uvars);
            no_full_norm = (uu___94_2432.no_full_norm);
            check_no_uvars = (uu___94_2432.check_no_uvars);
            unmeta = (uu___94_2432.unmeta);
            unascribe = (uu___94_2432.unascribe);
            in_full_norm_request = (uu___94_2432.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___94_2432.weakly_reduce_scrutinee);
            nbe_step = (uu___94_2432.nbe_step);
            for_extraction = (uu___94_2432.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___97_2434 = fs  in
          {
            beta = (uu___97_2434.beta);
            iota = true;
            zeta = (uu___97_2434.zeta);
            weak = (uu___97_2434.weak);
            hnf = (uu___97_2434.hnf);
            primops = (uu___97_2434.primops);
            do_not_unfold_pure_lets = (uu___97_2434.do_not_unfold_pure_lets);
            unfold_until = (uu___97_2434.unfold_until);
            unfold_only = (uu___97_2434.unfold_only);
            unfold_fully = (uu___97_2434.unfold_fully);
            unfold_attr = (uu___97_2434.unfold_attr);
            unfold_tac = (uu___97_2434.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_2434.pure_subterms_within_computations);
            simplify = (uu___97_2434.simplify);
            erase_universes = (uu___97_2434.erase_universes);
            allow_unbound_universes = (uu___97_2434.allow_unbound_universes);
            reify_ = (uu___97_2434.reify_);
            compress_uvars = (uu___97_2434.compress_uvars);
            no_full_norm = (uu___97_2434.no_full_norm);
            check_no_uvars = (uu___97_2434.check_no_uvars);
            unmeta = (uu___97_2434.unmeta);
            unascribe = (uu___97_2434.unascribe);
            in_full_norm_request = (uu___97_2434.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___97_2434.weakly_reduce_scrutinee);
            nbe_step = (uu___97_2434.nbe_step);
            for_extraction = (uu___97_2434.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___100_2436 = fs  in
          {
            beta = (uu___100_2436.beta);
            iota = (uu___100_2436.iota);
            zeta = true;
            weak = (uu___100_2436.weak);
            hnf = (uu___100_2436.hnf);
            primops = (uu___100_2436.primops);
            do_not_unfold_pure_lets = (uu___100_2436.do_not_unfold_pure_lets);
            unfold_until = (uu___100_2436.unfold_until);
            unfold_only = (uu___100_2436.unfold_only);
            unfold_fully = (uu___100_2436.unfold_fully);
            unfold_attr = (uu___100_2436.unfold_attr);
            unfold_tac = (uu___100_2436.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_2436.pure_subterms_within_computations);
            simplify = (uu___100_2436.simplify);
            erase_universes = (uu___100_2436.erase_universes);
            allow_unbound_universes = (uu___100_2436.allow_unbound_universes);
            reify_ = (uu___100_2436.reify_);
            compress_uvars = (uu___100_2436.compress_uvars);
            no_full_norm = (uu___100_2436.no_full_norm);
            check_no_uvars = (uu___100_2436.check_no_uvars);
            unmeta = (uu___100_2436.unmeta);
            unascribe = (uu___100_2436.unascribe);
            in_full_norm_request = (uu___100_2436.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_2436.weakly_reduce_scrutinee);
            nbe_step = (uu___100_2436.nbe_step);
            for_extraction = (uu___100_2436.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___104_2438 = fs  in
          {
            beta = false;
            iota = (uu___104_2438.iota);
            zeta = (uu___104_2438.zeta);
            weak = (uu___104_2438.weak);
            hnf = (uu___104_2438.hnf);
            primops = (uu___104_2438.primops);
            do_not_unfold_pure_lets = (uu___104_2438.do_not_unfold_pure_lets);
            unfold_until = (uu___104_2438.unfold_until);
            unfold_only = (uu___104_2438.unfold_only);
            unfold_fully = (uu___104_2438.unfold_fully);
            unfold_attr = (uu___104_2438.unfold_attr);
            unfold_tac = (uu___104_2438.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_2438.pure_subterms_within_computations);
            simplify = (uu___104_2438.simplify);
            erase_universes = (uu___104_2438.erase_universes);
            allow_unbound_universes = (uu___104_2438.allow_unbound_universes);
            reify_ = (uu___104_2438.reify_);
            compress_uvars = (uu___104_2438.compress_uvars);
            no_full_norm = (uu___104_2438.no_full_norm);
            check_no_uvars = (uu___104_2438.check_no_uvars);
            unmeta = (uu___104_2438.unmeta);
            unascribe = (uu___104_2438.unascribe);
            in_full_norm_request = (uu___104_2438.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___104_2438.weakly_reduce_scrutinee);
            nbe_step = (uu___104_2438.nbe_step);
            for_extraction = (uu___104_2438.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___108_2440 = fs  in
          {
            beta = (uu___108_2440.beta);
            iota = false;
            zeta = (uu___108_2440.zeta);
            weak = (uu___108_2440.weak);
            hnf = (uu___108_2440.hnf);
            primops = (uu___108_2440.primops);
            do_not_unfold_pure_lets = (uu___108_2440.do_not_unfold_pure_lets);
            unfold_until = (uu___108_2440.unfold_until);
            unfold_only = (uu___108_2440.unfold_only);
            unfold_fully = (uu___108_2440.unfold_fully);
            unfold_attr = (uu___108_2440.unfold_attr);
            unfold_tac = (uu___108_2440.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_2440.pure_subterms_within_computations);
            simplify = (uu___108_2440.simplify);
            erase_universes = (uu___108_2440.erase_universes);
            allow_unbound_universes = (uu___108_2440.allow_unbound_universes);
            reify_ = (uu___108_2440.reify_);
            compress_uvars = (uu___108_2440.compress_uvars);
            no_full_norm = (uu___108_2440.no_full_norm);
            check_no_uvars = (uu___108_2440.check_no_uvars);
            unmeta = (uu___108_2440.unmeta);
            unascribe = (uu___108_2440.unascribe);
            in_full_norm_request = (uu___108_2440.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___108_2440.weakly_reduce_scrutinee);
            nbe_step = (uu___108_2440.nbe_step);
            for_extraction = (uu___108_2440.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___112_2442 = fs  in
          {
            beta = (uu___112_2442.beta);
            iota = (uu___112_2442.iota);
            zeta = false;
            weak = (uu___112_2442.weak);
            hnf = (uu___112_2442.hnf);
            primops = (uu___112_2442.primops);
            do_not_unfold_pure_lets = (uu___112_2442.do_not_unfold_pure_lets);
            unfold_until = (uu___112_2442.unfold_until);
            unfold_only = (uu___112_2442.unfold_only);
            unfold_fully = (uu___112_2442.unfold_fully);
            unfold_attr = (uu___112_2442.unfold_attr);
            unfold_tac = (uu___112_2442.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_2442.pure_subterms_within_computations);
            simplify = (uu___112_2442.simplify);
            erase_universes = (uu___112_2442.erase_universes);
            allow_unbound_universes = (uu___112_2442.allow_unbound_universes);
            reify_ = (uu___112_2442.reify_);
            compress_uvars = (uu___112_2442.compress_uvars);
            no_full_norm = (uu___112_2442.no_full_norm);
            check_no_uvars = (uu___112_2442.check_no_uvars);
            unmeta = (uu___112_2442.unmeta);
            unascribe = (uu___112_2442.unascribe);
            in_full_norm_request = (uu___112_2442.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___112_2442.weakly_reduce_scrutinee);
            nbe_step = (uu___112_2442.nbe_step);
            for_extraction = (uu___112_2442.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____2444 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___117_2446 = fs  in
          {
            beta = (uu___117_2446.beta);
            iota = (uu___117_2446.iota);
            zeta = (uu___117_2446.zeta);
            weak = true;
            hnf = (uu___117_2446.hnf);
            primops = (uu___117_2446.primops);
            do_not_unfold_pure_lets = (uu___117_2446.do_not_unfold_pure_lets);
            unfold_until = (uu___117_2446.unfold_until);
            unfold_only = (uu___117_2446.unfold_only);
            unfold_fully = (uu___117_2446.unfold_fully);
            unfold_attr = (uu___117_2446.unfold_attr);
            unfold_tac = (uu___117_2446.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_2446.pure_subterms_within_computations);
            simplify = (uu___117_2446.simplify);
            erase_universes = (uu___117_2446.erase_universes);
            allow_unbound_universes = (uu___117_2446.allow_unbound_universes);
            reify_ = (uu___117_2446.reify_);
            compress_uvars = (uu___117_2446.compress_uvars);
            no_full_norm = (uu___117_2446.no_full_norm);
            check_no_uvars = (uu___117_2446.check_no_uvars);
            unmeta = (uu___117_2446.unmeta);
            unascribe = (uu___117_2446.unascribe);
            in_full_norm_request = (uu___117_2446.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___117_2446.weakly_reduce_scrutinee);
            nbe_step = (uu___117_2446.nbe_step);
            for_extraction = (uu___117_2446.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___120_2448 = fs  in
          {
            beta = (uu___120_2448.beta);
            iota = (uu___120_2448.iota);
            zeta = (uu___120_2448.zeta);
            weak = (uu___120_2448.weak);
            hnf = true;
            primops = (uu___120_2448.primops);
            do_not_unfold_pure_lets = (uu___120_2448.do_not_unfold_pure_lets);
            unfold_until = (uu___120_2448.unfold_until);
            unfold_only = (uu___120_2448.unfold_only);
            unfold_fully = (uu___120_2448.unfold_fully);
            unfold_attr = (uu___120_2448.unfold_attr);
            unfold_tac = (uu___120_2448.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_2448.pure_subterms_within_computations);
            simplify = (uu___120_2448.simplify);
            erase_universes = (uu___120_2448.erase_universes);
            allow_unbound_universes = (uu___120_2448.allow_unbound_universes);
            reify_ = (uu___120_2448.reify_);
            compress_uvars = (uu___120_2448.compress_uvars);
            no_full_norm = (uu___120_2448.no_full_norm);
            check_no_uvars = (uu___120_2448.check_no_uvars);
            unmeta = (uu___120_2448.unmeta);
            unascribe = (uu___120_2448.unascribe);
            in_full_norm_request = (uu___120_2448.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___120_2448.weakly_reduce_scrutinee);
            nbe_step = (uu___120_2448.nbe_step);
            for_extraction = (uu___120_2448.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___123_2450 = fs  in
          {
            beta = (uu___123_2450.beta);
            iota = (uu___123_2450.iota);
            zeta = (uu___123_2450.zeta);
            weak = (uu___123_2450.weak);
            hnf = (uu___123_2450.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___123_2450.do_not_unfold_pure_lets);
            unfold_until = (uu___123_2450.unfold_until);
            unfold_only = (uu___123_2450.unfold_only);
            unfold_fully = (uu___123_2450.unfold_fully);
            unfold_attr = (uu___123_2450.unfold_attr);
            unfold_tac = (uu___123_2450.unfold_tac);
            pure_subterms_within_computations =
              (uu___123_2450.pure_subterms_within_computations);
            simplify = (uu___123_2450.simplify);
            erase_universes = (uu___123_2450.erase_universes);
            allow_unbound_universes = (uu___123_2450.allow_unbound_universes);
            reify_ = (uu___123_2450.reify_);
            compress_uvars = (uu___123_2450.compress_uvars);
            no_full_norm = (uu___123_2450.no_full_norm);
            check_no_uvars = (uu___123_2450.check_no_uvars);
            unmeta = (uu___123_2450.unmeta);
            unascribe = (uu___123_2450.unascribe);
            in_full_norm_request = (uu___123_2450.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___123_2450.weakly_reduce_scrutinee);
            nbe_step = (uu___123_2450.nbe_step);
            for_extraction = (uu___123_2450.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___128_2452 = fs  in
          {
            beta = (uu___128_2452.beta);
            iota = (uu___128_2452.iota);
            zeta = (uu___128_2452.zeta);
            weak = (uu___128_2452.weak);
            hnf = (uu___128_2452.hnf);
            primops = (uu___128_2452.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___128_2452.unfold_until);
            unfold_only = (uu___128_2452.unfold_only);
            unfold_fully = (uu___128_2452.unfold_fully);
            unfold_attr = (uu___128_2452.unfold_attr);
            unfold_tac = (uu___128_2452.unfold_tac);
            pure_subterms_within_computations =
              (uu___128_2452.pure_subterms_within_computations);
            simplify = (uu___128_2452.simplify);
            erase_universes = (uu___128_2452.erase_universes);
            allow_unbound_universes = (uu___128_2452.allow_unbound_universes);
            reify_ = (uu___128_2452.reify_);
            compress_uvars = (uu___128_2452.compress_uvars);
            no_full_norm = (uu___128_2452.no_full_norm);
            check_no_uvars = (uu___128_2452.check_no_uvars);
            unmeta = (uu___128_2452.unmeta);
            unascribe = (uu___128_2452.unascribe);
            in_full_norm_request = (uu___128_2452.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___128_2452.weakly_reduce_scrutinee);
            nbe_step = (uu___128_2452.nbe_step);
            for_extraction = (uu___128_2452.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___132_2455 = fs  in
          {
            beta = (uu___132_2455.beta);
            iota = (uu___132_2455.iota);
            zeta = (uu___132_2455.zeta);
            weak = (uu___132_2455.weak);
            hnf = (uu___132_2455.hnf);
            primops = (uu___132_2455.primops);
            do_not_unfold_pure_lets = (uu___132_2455.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___132_2455.unfold_only);
            unfold_fully = (uu___132_2455.unfold_fully);
            unfold_attr = (uu___132_2455.unfold_attr);
            unfold_tac = (uu___132_2455.unfold_tac);
            pure_subterms_within_computations =
              (uu___132_2455.pure_subterms_within_computations);
            simplify = (uu___132_2455.simplify);
            erase_universes = (uu___132_2455.erase_universes);
            allow_unbound_universes = (uu___132_2455.allow_unbound_universes);
            reify_ = (uu___132_2455.reify_);
            compress_uvars = (uu___132_2455.compress_uvars);
            no_full_norm = (uu___132_2455.no_full_norm);
            check_no_uvars = (uu___132_2455.check_no_uvars);
            unmeta = (uu___132_2455.unmeta);
            unascribe = (uu___132_2455.unascribe);
            in_full_norm_request = (uu___132_2455.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___132_2455.weakly_reduce_scrutinee);
            nbe_step = (uu___132_2455.nbe_step);
            for_extraction = (uu___132_2455.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___136_2459 = fs  in
          {
            beta = (uu___136_2459.beta);
            iota = (uu___136_2459.iota);
            zeta = (uu___136_2459.zeta);
            weak = (uu___136_2459.weak);
            hnf = (uu___136_2459.hnf);
            primops = (uu___136_2459.primops);
            do_not_unfold_pure_lets = (uu___136_2459.do_not_unfold_pure_lets);
            unfold_until = (uu___136_2459.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___136_2459.unfold_fully);
            unfold_attr = (uu___136_2459.unfold_attr);
            unfold_tac = (uu___136_2459.unfold_tac);
            pure_subterms_within_computations =
              (uu___136_2459.pure_subterms_within_computations);
            simplify = (uu___136_2459.simplify);
            erase_universes = (uu___136_2459.erase_universes);
            allow_unbound_universes = (uu___136_2459.allow_unbound_universes);
            reify_ = (uu___136_2459.reify_);
            compress_uvars = (uu___136_2459.compress_uvars);
            no_full_norm = (uu___136_2459.no_full_norm);
            check_no_uvars = (uu___136_2459.check_no_uvars);
            unmeta = (uu___136_2459.unmeta);
            unascribe = (uu___136_2459.unascribe);
            in_full_norm_request = (uu___136_2459.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___136_2459.weakly_reduce_scrutinee);
            nbe_step = (uu___136_2459.nbe_step);
            for_extraction = (uu___136_2459.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___140_2465 = fs  in
          {
            beta = (uu___140_2465.beta);
            iota = (uu___140_2465.iota);
            zeta = (uu___140_2465.zeta);
            weak = (uu___140_2465.weak);
            hnf = (uu___140_2465.hnf);
            primops = (uu___140_2465.primops);
            do_not_unfold_pure_lets = (uu___140_2465.do_not_unfold_pure_lets);
            unfold_until = (uu___140_2465.unfold_until);
            unfold_only = (uu___140_2465.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___140_2465.unfold_attr);
            unfold_tac = (uu___140_2465.unfold_tac);
            pure_subterms_within_computations =
              (uu___140_2465.pure_subterms_within_computations);
            simplify = (uu___140_2465.simplify);
            erase_universes = (uu___140_2465.erase_universes);
            allow_unbound_universes = (uu___140_2465.allow_unbound_universes);
            reify_ = (uu___140_2465.reify_);
            compress_uvars = (uu___140_2465.compress_uvars);
            no_full_norm = (uu___140_2465.no_full_norm);
            check_no_uvars = (uu___140_2465.check_no_uvars);
            unmeta = (uu___140_2465.unmeta);
            unascribe = (uu___140_2465.unascribe);
            in_full_norm_request = (uu___140_2465.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___140_2465.weakly_reduce_scrutinee);
            nbe_step = (uu___140_2465.nbe_step);
            for_extraction = (uu___140_2465.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___144_2471 = fs  in
          {
            beta = (uu___144_2471.beta);
            iota = (uu___144_2471.iota);
            zeta = (uu___144_2471.zeta);
            weak = (uu___144_2471.weak);
            hnf = (uu___144_2471.hnf);
            primops = (uu___144_2471.primops);
            do_not_unfold_pure_lets = (uu___144_2471.do_not_unfold_pure_lets);
            unfold_until = (uu___144_2471.unfold_until);
            unfold_only = (uu___144_2471.unfold_only);
            unfold_fully = (uu___144_2471.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___144_2471.unfold_tac);
            pure_subterms_within_computations =
              (uu___144_2471.pure_subterms_within_computations);
            simplify = (uu___144_2471.simplify);
            erase_universes = (uu___144_2471.erase_universes);
            allow_unbound_universes = (uu___144_2471.allow_unbound_universes);
            reify_ = (uu___144_2471.reify_);
            compress_uvars = (uu___144_2471.compress_uvars);
            no_full_norm = (uu___144_2471.no_full_norm);
            check_no_uvars = (uu___144_2471.check_no_uvars);
            unmeta = (uu___144_2471.unmeta);
            unascribe = (uu___144_2471.unascribe);
            in_full_norm_request = (uu___144_2471.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___144_2471.weakly_reduce_scrutinee);
            nbe_step = (uu___144_2471.nbe_step);
            for_extraction = (uu___144_2471.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___147_2474 = fs  in
          {
            beta = (uu___147_2474.beta);
            iota = (uu___147_2474.iota);
            zeta = (uu___147_2474.zeta);
            weak = (uu___147_2474.weak);
            hnf = (uu___147_2474.hnf);
            primops = (uu___147_2474.primops);
            do_not_unfold_pure_lets = (uu___147_2474.do_not_unfold_pure_lets);
            unfold_until = (uu___147_2474.unfold_until);
            unfold_only = (uu___147_2474.unfold_only);
            unfold_fully = (uu___147_2474.unfold_fully);
            unfold_attr = (uu___147_2474.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___147_2474.pure_subterms_within_computations);
            simplify = (uu___147_2474.simplify);
            erase_universes = (uu___147_2474.erase_universes);
            allow_unbound_universes = (uu___147_2474.allow_unbound_universes);
            reify_ = (uu___147_2474.reify_);
            compress_uvars = (uu___147_2474.compress_uvars);
            no_full_norm = (uu___147_2474.no_full_norm);
            check_no_uvars = (uu___147_2474.check_no_uvars);
            unmeta = (uu___147_2474.unmeta);
            unascribe = (uu___147_2474.unascribe);
            in_full_norm_request = (uu___147_2474.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___147_2474.weakly_reduce_scrutinee);
            nbe_step = (uu___147_2474.nbe_step);
            for_extraction = (uu___147_2474.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___150_2476 = fs  in
          {
            beta = (uu___150_2476.beta);
            iota = (uu___150_2476.iota);
            zeta = (uu___150_2476.zeta);
            weak = (uu___150_2476.weak);
            hnf = (uu___150_2476.hnf);
            primops = (uu___150_2476.primops);
            do_not_unfold_pure_lets = (uu___150_2476.do_not_unfold_pure_lets);
            unfold_until = (uu___150_2476.unfold_until);
            unfold_only = (uu___150_2476.unfold_only);
            unfold_fully = (uu___150_2476.unfold_fully);
            unfold_attr = (uu___150_2476.unfold_attr);
            unfold_tac = (uu___150_2476.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___150_2476.simplify);
            erase_universes = (uu___150_2476.erase_universes);
            allow_unbound_universes = (uu___150_2476.allow_unbound_universes);
            reify_ = (uu___150_2476.reify_);
            compress_uvars = (uu___150_2476.compress_uvars);
            no_full_norm = (uu___150_2476.no_full_norm);
            check_no_uvars = (uu___150_2476.check_no_uvars);
            unmeta = (uu___150_2476.unmeta);
            unascribe = (uu___150_2476.unascribe);
            in_full_norm_request = (uu___150_2476.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___150_2476.weakly_reduce_scrutinee);
            nbe_step = (uu___150_2476.nbe_step);
            for_extraction = (uu___150_2476.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___153_2478 = fs  in
          {
            beta = (uu___153_2478.beta);
            iota = (uu___153_2478.iota);
            zeta = (uu___153_2478.zeta);
            weak = (uu___153_2478.weak);
            hnf = (uu___153_2478.hnf);
            primops = (uu___153_2478.primops);
            do_not_unfold_pure_lets = (uu___153_2478.do_not_unfold_pure_lets);
            unfold_until = (uu___153_2478.unfold_until);
            unfold_only = (uu___153_2478.unfold_only);
            unfold_fully = (uu___153_2478.unfold_fully);
            unfold_attr = (uu___153_2478.unfold_attr);
            unfold_tac = (uu___153_2478.unfold_tac);
            pure_subterms_within_computations =
              (uu___153_2478.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___153_2478.erase_universes);
            allow_unbound_universes = (uu___153_2478.allow_unbound_universes);
            reify_ = (uu___153_2478.reify_);
            compress_uvars = (uu___153_2478.compress_uvars);
            no_full_norm = (uu___153_2478.no_full_norm);
            check_no_uvars = (uu___153_2478.check_no_uvars);
            unmeta = (uu___153_2478.unmeta);
            unascribe = (uu___153_2478.unascribe);
            in_full_norm_request = (uu___153_2478.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___153_2478.weakly_reduce_scrutinee);
            nbe_step = (uu___153_2478.nbe_step);
            for_extraction = (uu___153_2478.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___156_2480 = fs  in
          {
            beta = (uu___156_2480.beta);
            iota = (uu___156_2480.iota);
            zeta = (uu___156_2480.zeta);
            weak = (uu___156_2480.weak);
            hnf = (uu___156_2480.hnf);
            primops = (uu___156_2480.primops);
            do_not_unfold_pure_lets = (uu___156_2480.do_not_unfold_pure_lets);
            unfold_until = (uu___156_2480.unfold_until);
            unfold_only = (uu___156_2480.unfold_only);
            unfold_fully = (uu___156_2480.unfold_fully);
            unfold_attr = (uu___156_2480.unfold_attr);
            unfold_tac = (uu___156_2480.unfold_tac);
            pure_subterms_within_computations =
              (uu___156_2480.pure_subterms_within_computations);
            simplify = (uu___156_2480.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___156_2480.allow_unbound_universes);
            reify_ = (uu___156_2480.reify_);
            compress_uvars = (uu___156_2480.compress_uvars);
            no_full_norm = (uu___156_2480.no_full_norm);
            check_no_uvars = (uu___156_2480.check_no_uvars);
            unmeta = (uu___156_2480.unmeta);
            unascribe = (uu___156_2480.unascribe);
            in_full_norm_request = (uu___156_2480.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___156_2480.weakly_reduce_scrutinee);
            nbe_step = (uu___156_2480.nbe_step);
            for_extraction = (uu___156_2480.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___159_2482 = fs  in
          {
            beta = (uu___159_2482.beta);
            iota = (uu___159_2482.iota);
            zeta = (uu___159_2482.zeta);
            weak = (uu___159_2482.weak);
            hnf = (uu___159_2482.hnf);
            primops = (uu___159_2482.primops);
            do_not_unfold_pure_lets = (uu___159_2482.do_not_unfold_pure_lets);
            unfold_until = (uu___159_2482.unfold_until);
            unfold_only = (uu___159_2482.unfold_only);
            unfold_fully = (uu___159_2482.unfold_fully);
            unfold_attr = (uu___159_2482.unfold_attr);
            unfold_tac = (uu___159_2482.unfold_tac);
            pure_subterms_within_computations =
              (uu___159_2482.pure_subterms_within_computations);
            simplify = (uu___159_2482.simplify);
            erase_universes = (uu___159_2482.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___159_2482.reify_);
            compress_uvars = (uu___159_2482.compress_uvars);
            no_full_norm = (uu___159_2482.no_full_norm);
            check_no_uvars = (uu___159_2482.check_no_uvars);
            unmeta = (uu___159_2482.unmeta);
            unascribe = (uu___159_2482.unascribe);
            in_full_norm_request = (uu___159_2482.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___159_2482.weakly_reduce_scrutinee);
            nbe_step = (uu___159_2482.nbe_step);
            for_extraction = (uu___159_2482.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___162_2484 = fs  in
          {
            beta = (uu___162_2484.beta);
            iota = (uu___162_2484.iota);
            zeta = (uu___162_2484.zeta);
            weak = (uu___162_2484.weak);
            hnf = (uu___162_2484.hnf);
            primops = (uu___162_2484.primops);
            do_not_unfold_pure_lets = (uu___162_2484.do_not_unfold_pure_lets);
            unfold_until = (uu___162_2484.unfold_until);
            unfold_only = (uu___162_2484.unfold_only);
            unfold_fully = (uu___162_2484.unfold_fully);
            unfold_attr = (uu___162_2484.unfold_attr);
            unfold_tac = (uu___162_2484.unfold_tac);
            pure_subterms_within_computations =
              (uu___162_2484.pure_subterms_within_computations);
            simplify = (uu___162_2484.simplify);
            erase_universes = (uu___162_2484.erase_universes);
            allow_unbound_universes = (uu___162_2484.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___162_2484.compress_uvars);
            no_full_norm = (uu___162_2484.no_full_norm);
            check_no_uvars = (uu___162_2484.check_no_uvars);
            unmeta = (uu___162_2484.unmeta);
            unascribe = (uu___162_2484.unascribe);
            in_full_norm_request = (uu___162_2484.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___162_2484.weakly_reduce_scrutinee);
            nbe_step = (uu___162_2484.nbe_step);
            for_extraction = (uu___162_2484.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___165_2486 = fs  in
          {
            beta = (uu___165_2486.beta);
            iota = (uu___165_2486.iota);
            zeta = (uu___165_2486.zeta);
            weak = (uu___165_2486.weak);
            hnf = (uu___165_2486.hnf);
            primops = (uu___165_2486.primops);
            do_not_unfold_pure_lets = (uu___165_2486.do_not_unfold_pure_lets);
            unfold_until = (uu___165_2486.unfold_until);
            unfold_only = (uu___165_2486.unfold_only);
            unfold_fully = (uu___165_2486.unfold_fully);
            unfold_attr = (uu___165_2486.unfold_attr);
            unfold_tac = (uu___165_2486.unfold_tac);
            pure_subterms_within_computations =
              (uu___165_2486.pure_subterms_within_computations);
            simplify = (uu___165_2486.simplify);
            erase_universes = (uu___165_2486.erase_universes);
            allow_unbound_universes = (uu___165_2486.allow_unbound_universes);
            reify_ = (uu___165_2486.reify_);
            compress_uvars = true;
            no_full_norm = (uu___165_2486.no_full_norm);
            check_no_uvars = (uu___165_2486.check_no_uvars);
            unmeta = (uu___165_2486.unmeta);
            unascribe = (uu___165_2486.unascribe);
            in_full_norm_request = (uu___165_2486.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___165_2486.weakly_reduce_scrutinee);
            nbe_step = (uu___165_2486.nbe_step);
            for_extraction = (uu___165_2486.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___168_2488 = fs  in
          {
            beta = (uu___168_2488.beta);
            iota = (uu___168_2488.iota);
            zeta = (uu___168_2488.zeta);
            weak = (uu___168_2488.weak);
            hnf = (uu___168_2488.hnf);
            primops = (uu___168_2488.primops);
            do_not_unfold_pure_lets = (uu___168_2488.do_not_unfold_pure_lets);
            unfold_until = (uu___168_2488.unfold_until);
            unfold_only = (uu___168_2488.unfold_only);
            unfold_fully = (uu___168_2488.unfold_fully);
            unfold_attr = (uu___168_2488.unfold_attr);
            unfold_tac = (uu___168_2488.unfold_tac);
            pure_subterms_within_computations =
              (uu___168_2488.pure_subterms_within_computations);
            simplify = (uu___168_2488.simplify);
            erase_universes = (uu___168_2488.erase_universes);
            allow_unbound_universes = (uu___168_2488.allow_unbound_universes);
            reify_ = (uu___168_2488.reify_);
            compress_uvars = (uu___168_2488.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___168_2488.check_no_uvars);
            unmeta = (uu___168_2488.unmeta);
            unascribe = (uu___168_2488.unascribe);
            in_full_norm_request = (uu___168_2488.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___168_2488.weakly_reduce_scrutinee);
            nbe_step = (uu___168_2488.nbe_step);
            for_extraction = (uu___168_2488.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___171_2490 = fs  in
          {
            beta = (uu___171_2490.beta);
            iota = (uu___171_2490.iota);
            zeta = (uu___171_2490.zeta);
            weak = (uu___171_2490.weak);
            hnf = (uu___171_2490.hnf);
            primops = (uu___171_2490.primops);
            do_not_unfold_pure_lets = (uu___171_2490.do_not_unfold_pure_lets);
            unfold_until = (uu___171_2490.unfold_until);
            unfold_only = (uu___171_2490.unfold_only);
            unfold_fully = (uu___171_2490.unfold_fully);
            unfold_attr = (uu___171_2490.unfold_attr);
            unfold_tac = (uu___171_2490.unfold_tac);
            pure_subterms_within_computations =
              (uu___171_2490.pure_subterms_within_computations);
            simplify = (uu___171_2490.simplify);
            erase_universes = (uu___171_2490.erase_universes);
            allow_unbound_universes = (uu___171_2490.allow_unbound_universes);
            reify_ = (uu___171_2490.reify_);
            compress_uvars = (uu___171_2490.compress_uvars);
            no_full_norm = (uu___171_2490.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___171_2490.unmeta);
            unascribe = (uu___171_2490.unascribe);
            in_full_norm_request = (uu___171_2490.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___171_2490.weakly_reduce_scrutinee);
            nbe_step = (uu___171_2490.nbe_step);
            for_extraction = (uu___171_2490.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___174_2492 = fs  in
          {
            beta = (uu___174_2492.beta);
            iota = (uu___174_2492.iota);
            zeta = (uu___174_2492.zeta);
            weak = (uu___174_2492.weak);
            hnf = (uu___174_2492.hnf);
            primops = (uu___174_2492.primops);
            do_not_unfold_pure_lets = (uu___174_2492.do_not_unfold_pure_lets);
            unfold_until = (uu___174_2492.unfold_until);
            unfold_only = (uu___174_2492.unfold_only);
            unfold_fully = (uu___174_2492.unfold_fully);
            unfold_attr = (uu___174_2492.unfold_attr);
            unfold_tac = (uu___174_2492.unfold_tac);
            pure_subterms_within_computations =
              (uu___174_2492.pure_subterms_within_computations);
            simplify = (uu___174_2492.simplify);
            erase_universes = (uu___174_2492.erase_universes);
            allow_unbound_universes = (uu___174_2492.allow_unbound_universes);
            reify_ = (uu___174_2492.reify_);
            compress_uvars = (uu___174_2492.compress_uvars);
            no_full_norm = (uu___174_2492.no_full_norm);
            check_no_uvars = (uu___174_2492.check_no_uvars);
            unmeta = true;
            unascribe = (uu___174_2492.unascribe);
            in_full_norm_request = (uu___174_2492.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___174_2492.weakly_reduce_scrutinee);
            nbe_step = (uu___174_2492.nbe_step);
            for_extraction = (uu___174_2492.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___177_2494 = fs  in
          {
            beta = (uu___177_2494.beta);
            iota = (uu___177_2494.iota);
            zeta = (uu___177_2494.zeta);
            weak = (uu___177_2494.weak);
            hnf = (uu___177_2494.hnf);
            primops = (uu___177_2494.primops);
            do_not_unfold_pure_lets = (uu___177_2494.do_not_unfold_pure_lets);
            unfold_until = (uu___177_2494.unfold_until);
            unfold_only = (uu___177_2494.unfold_only);
            unfold_fully = (uu___177_2494.unfold_fully);
            unfold_attr = (uu___177_2494.unfold_attr);
            unfold_tac = (uu___177_2494.unfold_tac);
            pure_subterms_within_computations =
              (uu___177_2494.pure_subterms_within_computations);
            simplify = (uu___177_2494.simplify);
            erase_universes = (uu___177_2494.erase_universes);
            allow_unbound_universes = (uu___177_2494.allow_unbound_universes);
            reify_ = (uu___177_2494.reify_);
            compress_uvars = (uu___177_2494.compress_uvars);
            no_full_norm = (uu___177_2494.no_full_norm);
            check_no_uvars = (uu___177_2494.check_no_uvars);
            unmeta = (uu___177_2494.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___177_2494.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___177_2494.weakly_reduce_scrutinee);
            nbe_step = (uu___177_2494.nbe_step);
            for_extraction = (uu___177_2494.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___180_2496 = fs  in
          {
            beta = (uu___180_2496.beta);
            iota = (uu___180_2496.iota);
            zeta = (uu___180_2496.zeta);
            weak = (uu___180_2496.weak);
            hnf = (uu___180_2496.hnf);
            primops = (uu___180_2496.primops);
            do_not_unfold_pure_lets = (uu___180_2496.do_not_unfold_pure_lets);
            unfold_until = (uu___180_2496.unfold_until);
            unfold_only = (uu___180_2496.unfold_only);
            unfold_fully = (uu___180_2496.unfold_fully);
            unfold_attr = (uu___180_2496.unfold_attr);
            unfold_tac = (uu___180_2496.unfold_tac);
            pure_subterms_within_computations =
              (uu___180_2496.pure_subterms_within_computations);
            simplify = (uu___180_2496.simplify);
            erase_universes = (uu___180_2496.erase_universes);
            allow_unbound_universes = (uu___180_2496.allow_unbound_universes);
            reify_ = (uu___180_2496.reify_);
            compress_uvars = (uu___180_2496.compress_uvars);
            no_full_norm = (uu___180_2496.no_full_norm);
            check_no_uvars = (uu___180_2496.check_no_uvars);
            unmeta = (uu___180_2496.unmeta);
            unascribe = (uu___180_2496.unascribe);
            in_full_norm_request = (uu___180_2496.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___180_2496.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___180_2496.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___183_2498 = fs  in
          {
            beta = (uu___183_2498.beta);
            iota = (uu___183_2498.iota);
            zeta = (uu___183_2498.zeta);
            weak = (uu___183_2498.weak);
            hnf = (uu___183_2498.hnf);
            primops = (uu___183_2498.primops);
            do_not_unfold_pure_lets = (uu___183_2498.do_not_unfold_pure_lets);
            unfold_until = (uu___183_2498.unfold_until);
            unfold_only = (uu___183_2498.unfold_only);
            unfold_fully = (uu___183_2498.unfold_fully);
            unfold_attr = (uu___183_2498.unfold_attr);
            unfold_tac = (uu___183_2498.unfold_tac);
            pure_subterms_within_computations =
              (uu___183_2498.pure_subterms_within_computations);
            simplify = (uu___183_2498.simplify);
            erase_universes = (uu___183_2498.erase_universes);
            allow_unbound_universes = (uu___183_2498.allow_unbound_universes);
            reify_ = (uu___183_2498.reify_);
            compress_uvars = (uu___183_2498.compress_uvars);
            no_full_norm = (uu___183_2498.no_full_norm);
            check_no_uvars = (uu___183_2498.check_no_uvars);
            unmeta = (uu___183_2498.unmeta);
            unascribe = (uu___183_2498.unascribe);
            in_full_norm_request = (uu___183_2498.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___183_2498.weakly_reduce_scrutinee);
            nbe_step = (uu___183_2498.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____2556  -> []) } 
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
  fun uu____3392  -> FStar_Util.psmap_empty () 
let (add_step :
  primitive_step -> prim_step_set -> primitive_step FStar_Util.psmap) =
  fun s  ->
    fun ss  ->
      let uu____3406 = FStar_Ident.text_of_lid s.name  in
      FStar_Util.psmap_add ss uu____3406 s
  
let (merge_steps : prim_step_set -> prim_step_set -> prim_step_set) =
  fun s1  -> fun s2  -> FStar_Util.psmap_merge s1 s2 
let (add_steps : prim_step_set -> primitive_step Prims.list -> prim_step_set)
  = fun m  -> fun l  -> FStar_List.fold_right add_step l m 
let (prim_from_list : primitive_step Prims.list -> prim_step_set) =
  fun l  -> let uu____3444 = empty_prim_steps ()  in add_steps uu____3444 l 
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
    let uu____3704 =
      let uu____3708 =
        let uu____3712 =
          let uu____3714 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____3714  in
        [uu____3712; "}"]  in
      "{" :: uu____3708  in
    FStar_String.concat "\n" uu____3704
  
let (cfg_env : cfg -> FStar_TypeChecker_Env.env) = fun cfg  -> cfg.tcenv 
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____3743 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____3743
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____3757 =
        let uu____3760 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____3760  in
      FStar_Util.is_some uu____3757
  
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
        let uu____3905 = FStar_Syntax_Embeddings.embed emb x  in
        uu____3905 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____3938 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____3938 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____3953 .
    'Auu____3953 ->
      FStar_Range.range -> 'Auu____3953 FStar_Syntax_Syntax.syntax
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
    let uu____4072 =
      let uu____4081 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____4081  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4072  in
  let arg_as_bounded_int1 uu____4111 =
    match uu____4111 with
    | (a,uu____4125) ->
        let uu____4136 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____4136 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____4180 =
               let uu____4195 =
                 let uu____4196 = FStar_Syntax_Subst.compress hd1  in
                 uu____4196.FStar_Syntax_Syntax.n  in
               (uu____4195, args)  in
             (match uu____4180 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____4217)::[]) when
                  let uu____4252 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____4252 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____4256 =
                    let uu____4257 = FStar_Syntax_Subst.compress arg1  in
                    uu____4257.FStar_Syntax_Syntax.n  in
                  (match uu____4256 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____4279 =
                         let uu____4284 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____4284)  in
                       FStar_Pervasives_Native.Some uu____4279
                   | uu____4289 -> FStar_Pervasives_Native.None)
              | uu____4294 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4356 = f a  in FStar_Pervasives_Native.Some uu____4356
    | uu____4357 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4413 = f a0 a1  in FStar_Pervasives_Native.Some uu____4413
    | uu____4414 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____4481 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____4481  in
  let binary_op1 as_a f res n1 args =
    let uu____4563 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____4563  in
  let as_primitive_step is_strong uu____4618 =
    match uu____4618 with
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
           let uu____4726 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____4726)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4768 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____4768)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____4809 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____4809)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4862 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____4862)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4915 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____4915)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____5068 =
          let uu____5077 = as_a a  in
          let uu____5080 = as_b b  in (uu____5077, uu____5080)  in
        (match uu____5068 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5095 =
               let uu____5096 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5096  in
             FStar_Pervasives_Native.Some uu____5095
         | uu____5097 -> FStar_Pervasives_Native.None)
    | uu____5106 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____5128 =
        let uu____5129 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5129  in
      mk uu____5128 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5143 =
      let uu____5146 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5146  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5143  in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5194 =
      let uu____5195 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5195  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____5194  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____5281 = arg_as_string1 a1  in
        (match uu____5281 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5290 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____5290 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5308 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____5308
              | uu____5310 -> FStar_Pervasives_Native.None)
         | uu____5316 -> FStar_Pervasives_Native.None)
    | uu____5320 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5401 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____5401 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5417 = arg_as_string1 a2  in
             (match uu____5417 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____5430 =
                    let uu____5431 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____5431 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5430
              | uu____5441 -> FStar_Pervasives_Native.None)
         | uu____5445 -> FStar_Pervasives_Native.None)
    | uu____5451 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____5489 =
          let uu____5503 = arg_as_string1 a1  in
          let uu____5507 = arg_as_int1 a2  in
          let uu____5510 = arg_as_int1 a3  in
          (uu____5503, uu____5507, uu____5510)  in
        (match uu____5489 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___506_5543  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____5548 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5548) ()
              with | uu___505_5551 -> FStar_Pervasives_Native.None)
         | uu____5554 -> FStar_Pervasives_Native.None)
    | uu____5568 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5582 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____5582  in
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
        let uu____5661 =
          let uu____5671 = arg_as_string1 a1  in
          let uu____5675 = arg_as_int1 a2  in (uu____5671, uu____5675)  in
        (match uu____5661 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___540_5699  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____5704 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5704) ()
              with | uu___539_5707 -> FStar_Pervasives_Native.None)
         | uu____5710 -> FStar_Pervasives_Native.None)
    | uu____5720 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5751 =
          let uu____5762 = arg_as_string1 a1  in
          let uu____5766 = arg_as_char1 a2  in (uu____5762, uu____5766)  in
        (match uu____5751 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___561_5795  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____5799 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5799) ()
              with | uu___560_5801 -> FStar_Pervasives_Native.None)
         | uu____5804 -> FStar_Pervasives_Native.None)
    | uu____5815 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5849 =
          let uu____5871 = arg_as_string1 fn  in
          let uu____5875 = arg_as_int1 from_line  in
          let uu____5878 = arg_as_int1 from_col  in
          let uu____5881 = arg_as_int1 to_line  in
          let uu____5884 = arg_as_int1 to_col  in
          (uu____5871, uu____5875, uu____5878, uu____5881, uu____5884)  in
        (match uu____5849 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5919 =
                 let uu____5920 = FStar_BigInt.to_int_fs from_l  in
                 let uu____5922 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____5920 uu____5922  in
               let uu____5924 =
                 let uu____5925 = FStar_BigInt.to_int_fs to_l  in
                 let uu____5927 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____5925 uu____5927  in
               FStar_Range.mk_range fn1 uu____5919 uu____5924  in
             let uu____5929 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____5929
         | uu____5930 -> FStar_Pervasives_Native.None)
    | uu____5952 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____5996)::(a1,uu____5998)::(a2,uu____6000)::[] ->
        let uu____6057 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6057 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6066 -> FStar_Pervasives_Native.None)
    | uu____6067 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____6110)::[] ->
        let uu____6127 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____6127 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6133 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6133
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6134 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____6154  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____6188 =
      let uu____6218 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, Prims.int_one, Prims.int_zero,
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)), uu____6218)
       in
    let uu____6252 =
      let uu____6284 =
        let uu____6314 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.of_int (2)), Prims.int_zero,
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____6314)
         in
      let uu____6354 =
        let uu____6386 =
          let uu____6416 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.of_int (2)),
            Prims.int_zero,
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____6416)
           in
        let uu____6456 =
          let uu____6488 =
            let uu____6518 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.of_int (2)),
              Prims.int_zero,
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____6518)
             in
          let uu____6558 =
            let uu____6590 =
              let uu____6620 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.of_int (2)),
                Prims.int_zero,
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____6620)
               in
            let uu____6660 =
              let uu____6692 =
                let uu____6722 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____6734 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____6734)
                   in
                (FStar_Parser_Const.op_LT, (Prims.of_int (2)),
                  Prims.int_zero,
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____6765 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____6765)), uu____6722)
                 in
              let uu____6768 =
                let uu____6800 =
                  let uu____6830 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____6842 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____6842)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.of_int (2)),
                    Prims.int_zero,
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____6873 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____6873)), uu____6830)
                   in
                let uu____6876 =
                  let uu____6908 =
                    let uu____6938 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____6950 = FStar_BigInt.gt_big_int x y  in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____6950)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.of_int (2)),
                      Prims.int_zero,
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____6981 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____6981)), uu____6938)
                     in
                  let uu____6984 =
                    let uu____7016 =
                      let uu____7046 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____7058 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____7058)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.of_int (2)),
                        Prims.int_zero,
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____7089 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____7089)), uu____7046)
                       in
                    let uu____7092 =
                      let uu____7124 =
                        let uu____7154 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus, (Prims.of_int (2)),
                          Prims.int_zero,
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____7154)
                         in
                      let uu____7194 =
                        let uu____7226 =
                          let uu____7256 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation, Prims.int_one,
                            Prims.int_zero,
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____7256)
                           in
                        let uu____7292 =
                          let uu____7324 =
                            let uu____7354 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And, (Prims.of_int (2)),
                              Prims.int_zero,
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____7354)
                             in
                          let uu____7398 =
                            let uu____7430 =
                              let uu____7460 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or, (Prims.of_int (2)),
                                Prims.int_zero,
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____7460)
                               in
                            let uu____7504 =
                              let uu____7536 =
                                let uu____7566 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  Prims.int_one, Prims.int_zero,
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____7566)
                                 in
                              let uu____7594 =
                                let uu____7626 =
                                  let uu____7656 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    Prims.int_one, Prims.int_zero,
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____7656)
                                   in
                                let uu____7686 =
                                  let uu____7718 =
                                    let uu____7748 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      Prims.int_one, Prims.int_zero,
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____7748)
                                     in
                                  let uu____7778 =
                                    let uu____7810 =
                                      let uu____7840 =
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
                                           string_of_list'1), uu____7840)
                                       in
                                    let uu____7876 =
                                      let uu____7908 =
                                        let uu____7940 =
                                          let uu____7972 =
                                            let uu____8002 =
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
                                              uu____8002)
                                             in
                                          let uu____8046 =
                                            let uu____8078 =
                                              let uu____8110 =
                                                let uu____8140 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.of_int (2)),
                                                  Prims.int_zero,
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____8140)
                                                 in
                                              let uu____8170 =
                                                let uu____8202 =
                                                  let uu____8232 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    Prims.int_one,
                                                    Prims.int_zero,
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____8232)
                                                   in
                                                let uu____8262 =
                                                  let uu____8294 =
                                                    let uu____8324 =
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
                                                      uu____8324)
                                                     in
                                                  let uu____8354 =
                                                    let uu____8386 =
                                                      let uu____8418 =
                                                        let uu____8450 =
                                                          let uu____8482 =
                                                            let uu____8514 =
                                                              let uu____8546
                                                                =
                                                                let uu____8576
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____8576,
                                                                  (Prims.of_int (5)),
                                                                  Prims.int_zero,
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____8603
                                                                =
                                                                let uu____8635
                                                                  =
                                                                  let uu____8665
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____8665,
                                                                    Prims.int_one,
                                                                    Prims.int_zero,
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____8635]
                                                                 in
                                                              uu____8546 ::
                                                                uu____8603
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.of_int (3)),
                                                              Prims.int_zero,
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____8514
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.of_int (3)),
                                                            Prims.int_zero,
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____8482
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.of_int (3)),
                                                          Prims.int_zero,
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____8450
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.of_int (2)),
                                                        Prims.int_zero,
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____8418
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.of_int (2)),
                                                      Prims.int_zero,
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____8386
                                                     in
                                                  uu____8294 :: uu____8354
                                                   in
                                                uu____8202 :: uu____8262  in
                                              uu____8110 :: uu____8170  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.of_int (2)),
                                              Prims.int_zero,
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____8078
                                             in
                                          uu____7972 :: uu____8046  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.of_int (2)), Prims.int_zero,
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____7940
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
                                                  let uu____9312 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____9312 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____9323 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____9323
                                                  y)))
                                        :: uu____7908
                                       in
                                    uu____7810 :: uu____7876  in
                                  uu____7718 :: uu____7778  in
                                uu____7626 :: uu____7686  in
                              uu____7536 :: uu____7594  in
                            uu____7430 :: uu____7504  in
                          uu____7324 :: uu____7398  in
                        uu____7226 :: uu____7292  in
                      uu____7124 :: uu____7194  in
                    uu____7016 :: uu____7092  in
                  uu____6908 :: uu____6984  in
                uu____6800 :: uu____6876  in
              uu____6692 :: uu____6768  in
            uu____6590 :: uu____6660  in
          uu____6488 :: uu____6558  in
        uu____6386 :: uu____6456  in
      uu____6284 :: uu____6354  in
    uu____6188 :: uu____6252  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9959 =
        let uu____9964 =
          let uu____9965 = FStar_Syntax_Syntax.as_arg c  in [uu____9965]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9964  in
      uu____9959 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____10092 =
                let uu____10122 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____10129 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10147  ->
                       fun uu____10148  ->
                         match (uu____10147, uu____10148) with
                         | ((int_to_t1,x),(uu____10167,y)) ->
                             let uu____10177 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____10177)
                   in
                (uu____10122, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____10212  ->
                          fun uu____10213  ->
                            match (uu____10212, uu____10213) with
                            | ((int_to_t1,x),(uu____10232,y)) ->
                                let uu____10242 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____10242)),
                  uu____10129)
                 in
              let uu____10243 =
                let uu____10275 =
                  let uu____10305 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____10312 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____10330  ->
                         fun uu____10331  ->
                           match (uu____10330, uu____10331) with
                           | ((int_to_t1,x),(uu____10350,y)) ->
                               let uu____10360 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____10360)
                     in
                  (uu____10305, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____10395  ->
                            fun uu____10396  ->
                              match (uu____10395, uu____10396) with
                              | ((int_to_t1,x),(uu____10415,y)) ->
                                  let uu____10425 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____10425)),
                    uu____10312)
                   in
                let uu____10426 =
                  let uu____10458 =
                    let uu____10488 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____10495 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____10513  ->
                           fun uu____10514  ->
                             match (uu____10513, uu____10514) with
                             | ((int_to_t1,x),(uu____10533,y)) ->
                                 let uu____10543 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____10543)
                       in
                    (uu____10488, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____10578  ->
                              fun uu____10579  ->
                                match (uu____10578, uu____10579) with
                                | ((int_to_t1,x),(uu____10598,y)) ->
                                    let uu____10608 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____10608)),
                      uu____10495)
                     in
                  let uu____10609 =
                    let uu____10641 =
                      let uu____10671 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____10678 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____10692  ->
                             match uu____10692 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____10671, Prims.int_one, Prims.int_zero,
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____10729  ->
                                match uu____10729 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____10678)
                       in
                    [uu____10641]  in
                  uu____10458 :: uu____10609  in
                uu____10275 :: uu____10426  in
              uu____10092 :: uu____10243))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____10982 =
                let uu____11012 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____11019 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11037  ->
                       fun uu____11038  ->
                         match (uu____11037, uu____11038) with
                         | ((int_to_t1,x),(uu____11057,y)) ->
                             let uu____11067 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11067)
                   in
                (uu____11012, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11102  ->
                          fun uu____11103  ->
                            match (uu____11102, uu____11103) with
                            | ((int_to_t1,x),(uu____11122,y)) ->
                                let uu____11132 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11132)),
                  uu____11019)
                 in
              let uu____11133 =
                let uu____11165 =
                  let uu____11195 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____11202 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11220  ->
                         fun uu____11221  ->
                           match (uu____11220, uu____11221) with
                           | ((int_to_t1,x),(uu____11240,y)) ->
                               let uu____11250 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11250)
                     in
                  (uu____11195, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11285  ->
                            fun uu____11286  ->
                              match (uu____11285, uu____11286) with
                              | ((int_to_t1,x),(uu____11305,y)) ->
                                  let uu____11315 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11315)),
                    uu____11202)
                   in
                [uu____11165]  in
              uu____10982 :: uu____11133))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____11421 ->
          let uu____11423 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____11423
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____11527 =
                let uu____11557 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____11564 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11582  ->
                       fun uu____11583  ->
                         match (uu____11582, uu____11583) with
                         | ((int_to_t1,x),(uu____11602,y)) ->
                             let uu____11612 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11612)
                   in
                (uu____11557, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11647  ->
                          fun uu____11648  ->
                            match (uu____11647, uu____11648) with
                            | ((int_to_t1,x),(uu____11667,y)) ->
                                let uu____11677 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11677)),
                  uu____11564)
                 in
              let uu____11678 =
                let uu____11710 =
                  let uu____11740 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____11747 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11765  ->
                         fun uu____11766  ->
                           match (uu____11765, uu____11766) with
                           | ((int_to_t1,x),(uu____11785,y)) ->
                               let uu____11795 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11795)
                     in
                  (uu____11740, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11830  ->
                            fun uu____11831  ->
                              match (uu____11830, uu____11831) with
                              | ((int_to_t1,x),(uu____11850,y)) ->
                                  let uu____11860 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11860)),
                    uu____11747)
                   in
                let uu____11861 =
                  let uu____11893 =
                    let uu____11923 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____11930 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____11948  ->
                           fun uu____11949  ->
                             match (uu____11948, uu____11949) with
                             | ((int_to_t1,x),(uu____11968,y)) ->
                                 let uu____11978 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____11978)
                       in
                    (uu____11923, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____12013  ->
                              fun uu____12014  ->
                                match (uu____12013, uu____12014) with
                                | ((int_to_t1,x),(uu____12033,y)) ->
                                    let uu____12043 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____12043)),
                      uu____11930)
                     in
                  let uu____12044 =
                    let uu____12076 =
                      let uu____12106 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____12113 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____12128  ->
                             match uu____12128 with
                             | (int_to_t1,x) ->
                                 let uu____12135 =
                                   let uu____12136 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____12137 = mask m  in
                                   FStar_BigInt.logand_big_int uu____12136
                                     uu____12137
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____12135)
                         in
                      (uu____12106, Prims.int_one, Prims.int_zero,
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____12169  ->
                                match uu____12169 with
                                | (int_to_t1,x) ->
                                    let uu____12176 =
                                      let uu____12177 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____12178 = mask m  in
                                      FStar_BigInt.logand_big_int uu____12177
                                        uu____12178
                                       in
                                    int_as_bounded1 r int_to_t1 uu____12176)),
                        uu____12113)
                       in
                    let uu____12179 =
                      let uu____12211 =
                        let uu____12241 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____12248 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____12266  ->
                               fun uu____12267  ->
                                 match (uu____12266, uu____12267) with
                                 | ((int_to_t1,x),(uu____12286,y)) ->
                                     let uu____12296 =
                                       let uu____12297 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____12298 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____12297 uu____12298
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____12296)
                           in
                        (uu____12241, (Prims.of_int (2)), Prims.int_zero,
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____12333  ->
                                  fun uu____12334  ->
                                    match (uu____12333, uu____12334) with
                                    | ((int_to_t1,x),(uu____12353,y)) ->
                                        let uu____12363 =
                                          let uu____12364 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____12365 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____12364 uu____12365
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____12363)), uu____12248)
                         in
                      let uu____12366 =
                        let uu____12398 =
                          let uu____12428 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____12435 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____12453  ->
                                 fun uu____12454  ->
                                   match (uu____12453, uu____12454) with
                                   | ((int_to_t1,x),(uu____12473,y)) ->
                                       let uu____12483 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____12483)
                             in
                          (uu____12428, (Prims.of_int (2)), Prims.int_zero,
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____12518  ->
                                    fun uu____12519  ->
                                      match (uu____12518, uu____12519) with
                                      | ((int_to_t1,x),(uu____12538,y)) ->
                                          let uu____12548 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____12548)), uu____12435)
                           in
                        [uu____12398]  in
                      uu____12211 :: uu____12366  in
                    uu____12076 :: uu____12179  in
                  uu____11893 :: uu____12044  in
                uu____11710 :: uu____11861  in
              uu____11527 :: uu____11678))
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
    | (_typ,uu____12936)::(a1,uu____12938)::(a2,uu____12940)::[] ->
        let uu____12997 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____12997 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___881_13001 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___881_13001.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___881_13001.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___884_13003 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___884_13003.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___884_13003.FStar_Syntax_Syntax.vars)
                })
         | uu____13004 -> FStar_Pervasives_Native.None)
    | uu____13005 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____13035)::(t2,uu____13037)::(a1,uu____13039)::(a2,uu____13041)::[]
        ->
        let uu____13114 =
          let uu____13115 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____13116 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____13115 uu____13116  in
        (match uu____13114 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___907_13120 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___907_13120.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___907_13120.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___910_13122 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___910_13122.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___910_13122.FStar_Syntax_Syntax.vars)
                })
         | uu____13123 -> FStar_Pervasives_Native.None)
    | uu____13124 -> failwith "Unexpected number of arguments"  in
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
  fun uu____13155  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____13172 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____13172 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____13201 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____13201 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____13212  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____13283  ->
           fun uu____13284  ->
             match (uu____13283, uu____13284) with
             | ((uu____13310,t1),(uu____13312,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____13346  ->
         fun rest  ->
           match uu____13346 with
           | (nm,ms) ->
               let uu____13362 =
                 let uu____13364 =
                   let uu____13366 = FStar_Util.string_of_int ms  in
                   fixto (Prims.of_int (10)) uu____13366  in
                 FStar_Util.format2 "%sms --- %s\n" uu____13364 nm  in
               FStar_String.op_Hat uu____13362 rest) pairs1 ""
  
let (extendable_primops_dirty : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref true 
type register_prim_step_t = primitive_step -> unit
type retrieve_prim_step_t = unit -> prim_step_set
let (mk_extendable_primop_set :
  unit -> (register_prim_step_t * retrieve_prim_step_t)) =
  fun uu____13394  ->
    let steps =
      let uu____13404 = empty_prim_steps ()  in FStar_Util.mk_ref uu____13404
       in
    let register p =
      FStar_ST.op_Colon_Equals extendable_primops_dirty true;
      (let uu____13434 =
         let uu____13435 = FStar_ST.op_Bang steps  in add_step p uu____13435
          in
       FStar_ST.op_Colon_Equals steps uu____13434)
       in
    let retrieve uu____13479 = FStar_ST.op_Bang steps  in
    (register, retrieve)
  
let (plugins : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set () 
let (extra_steps : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set () 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> prim_step_set) =
  fun uu____13528  ->
    let uu____13529 = FStar_Options.no_plugins ()  in
    if uu____13529
    then empty_prim_steps ()
    else FStar_Pervasives_Native.snd plugins ()
  
let (register_extra_step : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst extra_steps p 
let (retrieve_extra_steps : unit -> prim_step_set) =
  fun uu____13549  -> FStar_Pervasives_Native.snd extra_steps () 
let (cached_steps : unit -> prim_step_set) =
  let memo =
    let uu____13560 = empty_prim_steps ()  in FStar_Util.mk_ref uu____13560
     in
  fun uu____13561  ->
    let uu____13562 = FStar_ST.op_Bang extendable_primops_dirty  in
    if uu____13562
    then
      let steps =
        let uu____13587 =
          let uu____13588 = retrieve_plugins ()  in
          let uu____13589 = retrieve_extra_steps ()  in
          merge_steps uu____13588 uu____13589  in
        merge_steps built_in_primitive_steps uu____13587  in
      (FStar_ST.op_Colon_Equals memo steps;
       FStar_ST.op_Colon_Equals extendable_primops_dirty false;
       steps)
    else FStar_ST.op_Bang memo
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____13660 = FStar_Options.use_nbe ()  in
    if uu____13660
    then
      let uu___963_13663 = s  in
      {
        beta = (uu___963_13663.beta);
        iota = (uu___963_13663.iota);
        zeta = (uu___963_13663.zeta);
        weak = (uu___963_13663.weak);
        hnf = (uu___963_13663.hnf);
        primops = (uu___963_13663.primops);
        do_not_unfold_pure_lets = (uu___963_13663.do_not_unfold_pure_lets);
        unfold_until = (uu___963_13663.unfold_until);
        unfold_only = (uu___963_13663.unfold_only);
        unfold_fully = (uu___963_13663.unfold_fully);
        unfold_attr = (uu___963_13663.unfold_attr);
        unfold_tac = (uu___963_13663.unfold_tac);
        pure_subterms_within_computations =
          (uu___963_13663.pure_subterms_within_computations);
        simplify = (uu___963_13663.simplify);
        erase_universes = (uu___963_13663.erase_universes);
        allow_unbound_universes = (uu___963_13663.allow_unbound_universes);
        reify_ = (uu___963_13663.reify_);
        compress_uvars = (uu___963_13663.compress_uvars);
        no_full_norm = (uu___963_13663.no_full_norm);
        check_no_uvars = (uu___963_13663.check_no_uvars);
        unmeta = (uu___963_13663.unmeta);
        unascribe = (uu___963_13663.unascribe);
        in_full_norm_request = (uu___963_13663.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___963_13663.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___963_13663.for_extraction)
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
               (fun uu___0_13700  ->
                  match uu___0_13700 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____13704 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____13710 -> d  in
        let steps =
          let uu____13714 = to_fsteps s  in
          FStar_All.pipe_right uu____13714 add_nbe  in
        let psteps1 =
          let uu____13716 = cached_steps ()  in add_steps uu____13716 psteps
           in
        let uu____13717 =
          let uu____13718 = FStar_Options.debug_any ()  in
          if uu____13718
          then
            let uu____13721 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
            let uu____13724 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")
               in
            let uu____13727 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")
               in
            let uu____13730 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")
               in
            let uu____13733 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
               in
            let uu____13736 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
            let uu____13739 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
            let uu____13742 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "NormDelayed")
               in
            let uu____13745 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "print_normalized_terms")
               in
            let uu____13748 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NBE")  in
            {
              gen = uu____13721;
              top = uu____13724;
              cfg = uu____13727;
              primop = uu____13730;
              unfolding = uu____13733;
              b380 = uu____13736;
              wpe = uu____13739;
              norm_delayed = uu____13742;
              print_normalized = uu____13745;
              debug_nbe = uu____13748
            }
          else no_debug_switches  in
        let uu____13753 =
          (Prims.op_Negation steps.pure_subterms_within_computations) ||
            (FStar_Options.normalize_pure_terms_for_extraction ())
           in
        {
          steps;
          tcenv = e;
          debug = uu____13717;
          delta_level = d1;
          primitive_steps = psteps1;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____13753;
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
        (let uu____13790 =
           (cfg.steps).pure_subterms_within_computations &&
             (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs
                FStar_Parser_Const.inline_let_attr)
            in
         if uu____13790
         then true
         else
           (let n1 =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                lb.FStar_Syntax_Syntax.lbeff
               in
            let uu____13798 =
              (FStar_Syntax_Util.is_pure_effect n1) &&
                (cfg.normalize_pure_lets ||
                   (FStar_Syntax_Util.has_attribute
                      lb.FStar_Syntax_Syntax.lbattrs
                      FStar_Parser_Const.inline_let_attr))
               in
            if uu____13798
            then true
            else
              (FStar_Syntax_Util.is_ghost_effect n1) &&
                (Prims.op_Negation
                   (cfg.steps).pure_subterms_within_computations)))
  