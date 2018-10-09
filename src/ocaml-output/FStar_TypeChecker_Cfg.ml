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
          let uu____2046 =
            let uu____2048 = f1 x  in Prims.strcat uu____2048 ")"  in
          Prims.strcat "Some (" uu____2046
       in
    let b = FStar_Util.string_of_bool  in
    let uu____2059 =
      let uu____2063 = FStar_All.pipe_right f.beta b  in
      let uu____2067 =
        let uu____2071 = FStar_All.pipe_right f.iota b  in
        let uu____2075 =
          let uu____2079 = FStar_All.pipe_right f.zeta b  in
          let uu____2083 =
            let uu____2087 = FStar_All.pipe_right f.weak b  in
            let uu____2091 =
              let uu____2095 = FStar_All.pipe_right f.hnf b  in
              let uu____2099 =
                let uu____2103 = FStar_All.pipe_right f.primops b  in
                let uu____2107 =
                  let uu____2111 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____2115 =
                    let uu____2119 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____2124 =
                      let uu____2128 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____2142 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____2142
                                  (FStar_String.concat ", ")))
                         in
                      let uu____2152 =
                        let uu____2156 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____2170 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____2170
                                    (FStar_String.concat ", ")))
                           in
                        let uu____2180 =
                          let uu____2184 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____2198 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____2198
                                      (FStar_String.concat ", ")))
                             in
                          let uu____2208 =
                            let uu____2212 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____2216 =
                              let uu____2220 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____2224 =
                                let uu____2228 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____2232 =
                                  let uu____2236 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____2240 =
                                    let uu____2244 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____2248 =
                                      let uu____2252 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____2256 =
                                        let uu____2260 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____2264 =
                                          let uu____2268 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____2272 =
                                            let uu____2276 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____2280 =
                                              let uu____2284 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____2288 =
                                                let uu____2292 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____2296 =
                                                  let uu____2300 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____2304 =
                                                    let uu____2308 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____2308]  in
                                                  uu____2300 :: uu____2304
                                                   in
                                                uu____2292 :: uu____2296  in
                                              uu____2284 :: uu____2288  in
                                            uu____2276 :: uu____2280  in
                                          uu____2268 :: uu____2272  in
                                        uu____2260 :: uu____2264  in
                                      uu____2252 :: uu____2256  in
                                    uu____2244 :: uu____2248  in
                                  uu____2236 :: uu____2240  in
                                uu____2228 :: uu____2232  in
                              uu____2220 :: uu____2224  in
                            uu____2212 :: uu____2216  in
                          uu____2184 :: uu____2208  in
                        uu____2156 :: uu____2180  in
                      uu____2128 :: uu____2152  in
                    uu____2119 :: uu____2124  in
                  uu____2111 :: uu____2115  in
                uu____2103 :: uu____2107  in
              uu____2095 :: uu____2099  in
            uu____2087 :: uu____2091  in
          uu____2079 :: uu____2083  in
        uu____2071 :: uu____2075  in
      uu____2063 :: uu____2067  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____2059
  
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
          let uu___239_2378 = fs  in
          {
            beta = true;
            iota = (uu___239_2378.iota);
            zeta = (uu___239_2378.zeta);
            weak = (uu___239_2378.weak);
            hnf = (uu___239_2378.hnf);
            primops = (uu___239_2378.primops);
            do_not_unfold_pure_lets = (uu___239_2378.do_not_unfold_pure_lets);
            unfold_until = (uu___239_2378.unfold_until);
            unfold_only = (uu___239_2378.unfold_only);
            unfold_fully = (uu___239_2378.unfold_fully);
            unfold_attr = (uu___239_2378.unfold_attr);
            unfold_tac = (uu___239_2378.unfold_tac);
            pure_subterms_within_computations =
              (uu___239_2378.pure_subterms_within_computations);
            simplify = (uu___239_2378.simplify);
            erase_universes = (uu___239_2378.erase_universes);
            allow_unbound_universes = (uu___239_2378.allow_unbound_universes);
            reify_ = (uu___239_2378.reify_);
            compress_uvars = (uu___239_2378.compress_uvars);
            no_full_norm = (uu___239_2378.no_full_norm);
            check_no_uvars = (uu___239_2378.check_no_uvars);
            unmeta = (uu___239_2378.unmeta);
            unascribe = (uu___239_2378.unascribe);
            in_full_norm_request = (uu___239_2378.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___239_2378.weakly_reduce_scrutinee);
            nbe_step = (uu___239_2378.nbe_step);
            for_extraction = (uu___239_2378.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___240_2380 = fs  in
          {
            beta = (uu___240_2380.beta);
            iota = true;
            zeta = (uu___240_2380.zeta);
            weak = (uu___240_2380.weak);
            hnf = (uu___240_2380.hnf);
            primops = (uu___240_2380.primops);
            do_not_unfold_pure_lets = (uu___240_2380.do_not_unfold_pure_lets);
            unfold_until = (uu___240_2380.unfold_until);
            unfold_only = (uu___240_2380.unfold_only);
            unfold_fully = (uu___240_2380.unfold_fully);
            unfold_attr = (uu___240_2380.unfold_attr);
            unfold_tac = (uu___240_2380.unfold_tac);
            pure_subterms_within_computations =
              (uu___240_2380.pure_subterms_within_computations);
            simplify = (uu___240_2380.simplify);
            erase_universes = (uu___240_2380.erase_universes);
            allow_unbound_universes = (uu___240_2380.allow_unbound_universes);
            reify_ = (uu___240_2380.reify_);
            compress_uvars = (uu___240_2380.compress_uvars);
            no_full_norm = (uu___240_2380.no_full_norm);
            check_no_uvars = (uu___240_2380.check_no_uvars);
            unmeta = (uu___240_2380.unmeta);
            unascribe = (uu___240_2380.unascribe);
            in_full_norm_request = (uu___240_2380.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___240_2380.weakly_reduce_scrutinee);
            nbe_step = (uu___240_2380.nbe_step);
            for_extraction = (uu___240_2380.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___241_2382 = fs  in
          {
            beta = (uu___241_2382.beta);
            iota = (uu___241_2382.iota);
            zeta = true;
            weak = (uu___241_2382.weak);
            hnf = (uu___241_2382.hnf);
            primops = (uu___241_2382.primops);
            do_not_unfold_pure_lets = (uu___241_2382.do_not_unfold_pure_lets);
            unfold_until = (uu___241_2382.unfold_until);
            unfold_only = (uu___241_2382.unfold_only);
            unfold_fully = (uu___241_2382.unfold_fully);
            unfold_attr = (uu___241_2382.unfold_attr);
            unfold_tac = (uu___241_2382.unfold_tac);
            pure_subterms_within_computations =
              (uu___241_2382.pure_subterms_within_computations);
            simplify = (uu___241_2382.simplify);
            erase_universes = (uu___241_2382.erase_universes);
            allow_unbound_universes = (uu___241_2382.allow_unbound_universes);
            reify_ = (uu___241_2382.reify_);
            compress_uvars = (uu___241_2382.compress_uvars);
            no_full_norm = (uu___241_2382.no_full_norm);
            check_no_uvars = (uu___241_2382.check_no_uvars);
            unmeta = (uu___241_2382.unmeta);
            unascribe = (uu___241_2382.unascribe);
            in_full_norm_request = (uu___241_2382.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___241_2382.weakly_reduce_scrutinee);
            nbe_step = (uu___241_2382.nbe_step);
            for_extraction = (uu___241_2382.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___242_2384 = fs  in
          {
            beta = false;
            iota = (uu___242_2384.iota);
            zeta = (uu___242_2384.zeta);
            weak = (uu___242_2384.weak);
            hnf = (uu___242_2384.hnf);
            primops = (uu___242_2384.primops);
            do_not_unfold_pure_lets = (uu___242_2384.do_not_unfold_pure_lets);
            unfold_until = (uu___242_2384.unfold_until);
            unfold_only = (uu___242_2384.unfold_only);
            unfold_fully = (uu___242_2384.unfold_fully);
            unfold_attr = (uu___242_2384.unfold_attr);
            unfold_tac = (uu___242_2384.unfold_tac);
            pure_subterms_within_computations =
              (uu___242_2384.pure_subterms_within_computations);
            simplify = (uu___242_2384.simplify);
            erase_universes = (uu___242_2384.erase_universes);
            allow_unbound_universes = (uu___242_2384.allow_unbound_universes);
            reify_ = (uu___242_2384.reify_);
            compress_uvars = (uu___242_2384.compress_uvars);
            no_full_norm = (uu___242_2384.no_full_norm);
            check_no_uvars = (uu___242_2384.check_no_uvars);
            unmeta = (uu___242_2384.unmeta);
            unascribe = (uu___242_2384.unascribe);
            in_full_norm_request = (uu___242_2384.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___242_2384.weakly_reduce_scrutinee);
            nbe_step = (uu___242_2384.nbe_step);
            for_extraction = (uu___242_2384.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___243_2386 = fs  in
          {
            beta = (uu___243_2386.beta);
            iota = false;
            zeta = (uu___243_2386.zeta);
            weak = (uu___243_2386.weak);
            hnf = (uu___243_2386.hnf);
            primops = (uu___243_2386.primops);
            do_not_unfold_pure_lets = (uu___243_2386.do_not_unfold_pure_lets);
            unfold_until = (uu___243_2386.unfold_until);
            unfold_only = (uu___243_2386.unfold_only);
            unfold_fully = (uu___243_2386.unfold_fully);
            unfold_attr = (uu___243_2386.unfold_attr);
            unfold_tac = (uu___243_2386.unfold_tac);
            pure_subterms_within_computations =
              (uu___243_2386.pure_subterms_within_computations);
            simplify = (uu___243_2386.simplify);
            erase_universes = (uu___243_2386.erase_universes);
            allow_unbound_universes = (uu___243_2386.allow_unbound_universes);
            reify_ = (uu___243_2386.reify_);
            compress_uvars = (uu___243_2386.compress_uvars);
            no_full_norm = (uu___243_2386.no_full_norm);
            check_no_uvars = (uu___243_2386.check_no_uvars);
            unmeta = (uu___243_2386.unmeta);
            unascribe = (uu___243_2386.unascribe);
            in_full_norm_request = (uu___243_2386.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___243_2386.weakly_reduce_scrutinee);
            nbe_step = (uu___243_2386.nbe_step);
            for_extraction = (uu___243_2386.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___244_2388 = fs  in
          {
            beta = (uu___244_2388.beta);
            iota = (uu___244_2388.iota);
            zeta = false;
            weak = (uu___244_2388.weak);
            hnf = (uu___244_2388.hnf);
            primops = (uu___244_2388.primops);
            do_not_unfold_pure_lets = (uu___244_2388.do_not_unfold_pure_lets);
            unfold_until = (uu___244_2388.unfold_until);
            unfold_only = (uu___244_2388.unfold_only);
            unfold_fully = (uu___244_2388.unfold_fully);
            unfold_attr = (uu___244_2388.unfold_attr);
            unfold_tac = (uu___244_2388.unfold_tac);
            pure_subterms_within_computations =
              (uu___244_2388.pure_subterms_within_computations);
            simplify = (uu___244_2388.simplify);
            erase_universes = (uu___244_2388.erase_universes);
            allow_unbound_universes = (uu___244_2388.allow_unbound_universes);
            reify_ = (uu___244_2388.reify_);
            compress_uvars = (uu___244_2388.compress_uvars);
            no_full_norm = (uu___244_2388.no_full_norm);
            check_no_uvars = (uu___244_2388.check_no_uvars);
            unmeta = (uu___244_2388.unmeta);
            unascribe = (uu___244_2388.unascribe);
            in_full_norm_request = (uu___244_2388.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___244_2388.weakly_reduce_scrutinee);
            nbe_step = (uu___244_2388.nbe_step);
            for_extraction = (uu___244_2388.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____2390 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___245_2392 = fs  in
          {
            beta = (uu___245_2392.beta);
            iota = (uu___245_2392.iota);
            zeta = (uu___245_2392.zeta);
            weak = true;
            hnf = (uu___245_2392.hnf);
            primops = (uu___245_2392.primops);
            do_not_unfold_pure_lets = (uu___245_2392.do_not_unfold_pure_lets);
            unfold_until = (uu___245_2392.unfold_until);
            unfold_only = (uu___245_2392.unfold_only);
            unfold_fully = (uu___245_2392.unfold_fully);
            unfold_attr = (uu___245_2392.unfold_attr);
            unfold_tac = (uu___245_2392.unfold_tac);
            pure_subterms_within_computations =
              (uu___245_2392.pure_subterms_within_computations);
            simplify = (uu___245_2392.simplify);
            erase_universes = (uu___245_2392.erase_universes);
            allow_unbound_universes = (uu___245_2392.allow_unbound_universes);
            reify_ = (uu___245_2392.reify_);
            compress_uvars = (uu___245_2392.compress_uvars);
            no_full_norm = (uu___245_2392.no_full_norm);
            check_no_uvars = (uu___245_2392.check_no_uvars);
            unmeta = (uu___245_2392.unmeta);
            unascribe = (uu___245_2392.unascribe);
            in_full_norm_request = (uu___245_2392.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___245_2392.weakly_reduce_scrutinee);
            nbe_step = (uu___245_2392.nbe_step);
            for_extraction = (uu___245_2392.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___246_2394 = fs  in
          {
            beta = (uu___246_2394.beta);
            iota = (uu___246_2394.iota);
            zeta = (uu___246_2394.zeta);
            weak = (uu___246_2394.weak);
            hnf = true;
            primops = (uu___246_2394.primops);
            do_not_unfold_pure_lets = (uu___246_2394.do_not_unfold_pure_lets);
            unfold_until = (uu___246_2394.unfold_until);
            unfold_only = (uu___246_2394.unfold_only);
            unfold_fully = (uu___246_2394.unfold_fully);
            unfold_attr = (uu___246_2394.unfold_attr);
            unfold_tac = (uu___246_2394.unfold_tac);
            pure_subterms_within_computations =
              (uu___246_2394.pure_subterms_within_computations);
            simplify = (uu___246_2394.simplify);
            erase_universes = (uu___246_2394.erase_universes);
            allow_unbound_universes = (uu___246_2394.allow_unbound_universes);
            reify_ = (uu___246_2394.reify_);
            compress_uvars = (uu___246_2394.compress_uvars);
            no_full_norm = (uu___246_2394.no_full_norm);
            check_no_uvars = (uu___246_2394.check_no_uvars);
            unmeta = (uu___246_2394.unmeta);
            unascribe = (uu___246_2394.unascribe);
            in_full_norm_request = (uu___246_2394.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___246_2394.weakly_reduce_scrutinee);
            nbe_step = (uu___246_2394.nbe_step);
            for_extraction = (uu___246_2394.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___247_2396 = fs  in
          {
            beta = (uu___247_2396.beta);
            iota = (uu___247_2396.iota);
            zeta = (uu___247_2396.zeta);
            weak = (uu___247_2396.weak);
            hnf = (uu___247_2396.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___247_2396.do_not_unfold_pure_lets);
            unfold_until = (uu___247_2396.unfold_until);
            unfold_only = (uu___247_2396.unfold_only);
            unfold_fully = (uu___247_2396.unfold_fully);
            unfold_attr = (uu___247_2396.unfold_attr);
            unfold_tac = (uu___247_2396.unfold_tac);
            pure_subterms_within_computations =
              (uu___247_2396.pure_subterms_within_computations);
            simplify = (uu___247_2396.simplify);
            erase_universes = (uu___247_2396.erase_universes);
            allow_unbound_universes = (uu___247_2396.allow_unbound_universes);
            reify_ = (uu___247_2396.reify_);
            compress_uvars = (uu___247_2396.compress_uvars);
            no_full_norm = (uu___247_2396.no_full_norm);
            check_no_uvars = (uu___247_2396.check_no_uvars);
            unmeta = (uu___247_2396.unmeta);
            unascribe = (uu___247_2396.unascribe);
            in_full_norm_request = (uu___247_2396.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___247_2396.weakly_reduce_scrutinee);
            nbe_step = (uu___247_2396.nbe_step);
            for_extraction = (uu___247_2396.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___248_2398 = fs  in
          {
            beta = (uu___248_2398.beta);
            iota = (uu___248_2398.iota);
            zeta = (uu___248_2398.zeta);
            weak = (uu___248_2398.weak);
            hnf = (uu___248_2398.hnf);
            primops = (uu___248_2398.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___248_2398.unfold_until);
            unfold_only = (uu___248_2398.unfold_only);
            unfold_fully = (uu___248_2398.unfold_fully);
            unfold_attr = (uu___248_2398.unfold_attr);
            unfold_tac = (uu___248_2398.unfold_tac);
            pure_subterms_within_computations =
              (uu___248_2398.pure_subterms_within_computations);
            simplify = (uu___248_2398.simplify);
            erase_universes = (uu___248_2398.erase_universes);
            allow_unbound_universes = (uu___248_2398.allow_unbound_universes);
            reify_ = (uu___248_2398.reify_);
            compress_uvars = (uu___248_2398.compress_uvars);
            no_full_norm = (uu___248_2398.no_full_norm);
            check_no_uvars = (uu___248_2398.check_no_uvars);
            unmeta = (uu___248_2398.unmeta);
            unascribe = (uu___248_2398.unascribe);
            in_full_norm_request = (uu___248_2398.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___248_2398.weakly_reduce_scrutinee);
            nbe_step = (uu___248_2398.nbe_step);
            for_extraction = (uu___248_2398.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___249_2401 = fs  in
          {
            beta = (uu___249_2401.beta);
            iota = (uu___249_2401.iota);
            zeta = (uu___249_2401.zeta);
            weak = (uu___249_2401.weak);
            hnf = (uu___249_2401.hnf);
            primops = (uu___249_2401.primops);
            do_not_unfold_pure_lets = (uu___249_2401.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___249_2401.unfold_only);
            unfold_fully = (uu___249_2401.unfold_fully);
            unfold_attr = (uu___249_2401.unfold_attr);
            unfold_tac = (uu___249_2401.unfold_tac);
            pure_subterms_within_computations =
              (uu___249_2401.pure_subterms_within_computations);
            simplify = (uu___249_2401.simplify);
            erase_universes = (uu___249_2401.erase_universes);
            allow_unbound_universes = (uu___249_2401.allow_unbound_universes);
            reify_ = (uu___249_2401.reify_);
            compress_uvars = (uu___249_2401.compress_uvars);
            no_full_norm = (uu___249_2401.no_full_norm);
            check_no_uvars = (uu___249_2401.check_no_uvars);
            unmeta = (uu___249_2401.unmeta);
            unascribe = (uu___249_2401.unascribe);
            in_full_norm_request = (uu___249_2401.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___249_2401.weakly_reduce_scrutinee);
            nbe_step = (uu___249_2401.nbe_step);
            for_extraction = (uu___249_2401.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___250_2405 = fs  in
          {
            beta = (uu___250_2405.beta);
            iota = (uu___250_2405.iota);
            zeta = (uu___250_2405.zeta);
            weak = (uu___250_2405.weak);
            hnf = (uu___250_2405.hnf);
            primops = (uu___250_2405.primops);
            do_not_unfold_pure_lets = (uu___250_2405.do_not_unfold_pure_lets);
            unfold_until = (uu___250_2405.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___250_2405.unfold_fully);
            unfold_attr = (uu___250_2405.unfold_attr);
            unfold_tac = (uu___250_2405.unfold_tac);
            pure_subterms_within_computations =
              (uu___250_2405.pure_subterms_within_computations);
            simplify = (uu___250_2405.simplify);
            erase_universes = (uu___250_2405.erase_universes);
            allow_unbound_universes = (uu___250_2405.allow_unbound_universes);
            reify_ = (uu___250_2405.reify_);
            compress_uvars = (uu___250_2405.compress_uvars);
            no_full_norm = (uu___250_2405.no_full_norm);
            check_no_uvars = (uu___250_2405.check_no_uvars);
            unmeta = (uu___250_2405.unmeta);
            unascribe = (uu___250_2405.unascribe);
            in_full_norm_request = (uu___250_2405.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___250_2405.weakly_reduce_scrutinee);
            nbe_step = (uu___250_2405.nbe_step);
            for_extraction = (uu___250_2405.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___251_2411 = fs  in
          {
            beta = (uu___251_2411.beta);
            iota = (uu___251_2411.iota);
            zeta = (uu___251_2411.zeta);
            weak = (uu___251_2411.weak);
            hnf = (uu___251_2411.hnf);
            primops = (uu___251_2411.primops);
            do_not_unfold_pure_lets = (uu___251_2411.do_not_unfold_pure_lets);
            unfold_until = (uu___251_2411.unfold_until);
            unfold_only = (uu___251_2411.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___251_2411.unfold_attr);
            unfold_tac = (uu___251_2411.unfold_tac);
            pure_subterms_within_computations =
              (uu___251_2411.pure_subterms_within_computations);
            simplify = (uu___251_2411.simplify);
            erase_universes = (uu___251_2411.erase_universes);
            allow_unbound_universes = (uu___251_2411.allow_unbound_universes);
            reify_ = (uu___251_2411.reify_);
            compress_uvars = (uu___251_2411.compress_uvars);
            no_full_norm = (uu___251_2411.no_full_norm);
            check_no_uvars = (uu___251_2411.check_no_uvars);
            unmeta = (uu___251_2411.unmeta);
            unascribe = (uu___251_2411.unascribe);
            in_full_norm_request = (uu___251_2411.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___251_2411.weakly_reduce_scrutinee);
            nbe_step = (uu___251_2411.nbe_step);
            for_extraction = (uu___251_2411.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___252_2417 = fs  in
          {
            beta = (uu___252_2417.beta);
            iota = (uu___252_2417.iota);
            zeta = (uu___252_2417.zeta);
            weak = (uu___252_2417.weak);
            hnf = (uu___252_2417.hnf);
            primops = (uu___252_2417.primops);
            do_not_unfold_pure_lets = (uu___252_2417.do_not_unfold_pure_lets);
            unfold_until = (uu___252_2417.unfold_until);
            unfold_only = (uu___252_2417.unfold_only);
            unfold_fully = (uu___252_2417.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___252_2417.unfold_tac);
            pure_subterms_within_computations =
              (uu___252_2417.pure_subterms_within_computations);
            simplify = (uu___252_2417.simplify);
            erase_universes = (uu___252_2417.erase_universes);
            allow_unbound_universes = (uu___252_2417.allow_unbound_universes);
            reify_ = (uu___252_2417.reify_);
            compress_uvars = (uu___252_2417.compress_uvars);
            no_full_norm = (uu___252_2417.no_full_norm);
            check_no_uvars = (uu___252_2417.check_no_uvars);
            unmeta = (uu___252_2417.unmeta);
            unascribe = (uu___252_2417.unascribe);
            in_full_norm_request = (uu___252_2417.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___252_2417.weakly_reduce_scrutinee);
            nbe_step = (uu___252_2417.nbe_step);
            for_extraction = (uu___252_2417.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___253_2420 = fs  in
          {
            beta = (uu___253_2420.beta);
            iota = (uu___253_2420.iota);
            zeta = (uu___253_2420.zeta);
            weak = (uu___253_2420.weak);
            hnf = (uu___253_2420.hnf);
            primops = (uu___253_2420.primops);
            do_not_unfold_pure_lets = (uu___253_2420.do_not_unfold_pure_lets);
            unfold_until = (uu___253_2420.unfold_until);
            unfold_only = (uu___253_2420.unfold_only);
            unfold_fully = (uu___253_2420.unfold_fully);
            unfold_attr = (uu___253_2420.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___253_2420.pure_subterms_within_computations);
            simplify = (uu___253_2420.simplify);
            erase_universes = (uu___253_2420.erase_universes);
            allow_unbound_universes = (uu___253_2420.allow_unbound_universes);
            reify_ = (uu___253_2420.reify_);
            compress_uvars = (uu___253_2420.compress_uvars);
            no_full_norm = (uu___253_2420.no_full_norm);
            check_no_uvars = (uu___253_2420.check_no_uvars);
            unmeta = (uu___253_2420.unmeta);
            unascribe = (uu___253_2420.unascribe);
            in_full_norm_request = (uu___253_2420.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___253_2420.weakly_reduce_scrutinee);
            nbe_step = (uu___253_2420.nbe_step);
            for_extraction = (uu___253_2420.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___254_2422 = fs  in
          {
            beta = (uu___254_2422.beta);
            iota = (uu___254_2422.iota);
            zeta = (uu___254_2422.zeta);
            weak = (uu___254_2422.weak);
            hnf = (uu___254_2422.hnf);
            primops = (uu___254_2422.primops);
            do_not_unfold_pure_lets = (uu___254_2422.do_not_unfold_pure_lets);
            unfold_until = (uu___254_2422.unfold_until);
            unfold_only = (uu___254_2422.unfold_only);
            unfold_fully = (uu___254_2422.unfold_fully);
            unfold_attr = (uu___254_2422.unfold_attr);
            unfold_tac = (uu___254_2422.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___254_2422.simplify);
            erase_universes = (uu___254_2422.erase_universes);
            allow_unbound_universes = (uu___254_2422.allow_unbound_universes);
            reify_ = (uu___254_2422.reify_);
            compress_uvars = (uu___254_2422.compress_uvars);
            no_full_norm = (uu___254_2422.no_full_norm);
            check_no_uvars = (uu___254_2422.check_no_uvars);
            unmeta = (uu___254_2422.unmeta);
            unascribe = (uu___254_2422.unascribe);
            in_full_norm_request = (uu___254_2422.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___254_2422.weakly_reduce_scrutinee);
            nbe_step = (uu___254_2422.nbe_step);
            for_extraction = (uu___254_2422.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___255_2424 = fs  in
          {
            beta = (uu___255_2424.beta);
            iota = (uu___255_2424.iota);
            zeta = (uu___255_2424.zeta);
            weak = (uu___255_2424.weak);
            hnf = (uu___255_2424.hnf);
            primops = (uu___255_2424.primops);
            do_not_unfold_pure_lets = (uu___255_2424.do_not_unfold_pure_lets);
            unfold_until = (uu___255_2424.unfold_until);
            unfold_only = (uu___255_2424.unfold_only);
            unfold_fully = (uu___255_2424.unfold_fully);
            unfold_attr = (uu___255_2424.unfold_attr);
            unfold_tac = (uu___255_2424.unfold_tac);
            pure_subterms_within_computations =
              (uu___255_2424.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___255_2424.erase_universes);
            allow_unbound_universes = (uu___255_2424.allow_unbound_universes);
            reify_ = (uu___255_2424.reify_);
            compress_uvars = (uu___255_2424.compress_uvars);
            no_full_norm = (uu___255_2424.no_full_norm);
            check_no_uvars = (uu___255_2424.check_no_uvars);
            unmeta = (uu___255_2424.unmeta);
            unascribe = (uu___255_2424.unascribe);
            in_full_norm_request = (uu___255_2424.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___255_2424.weakly_reduce_scrutinee);
            nbe_step = (uu___255_2424.nbe_step);
            for_extraction = (uu___255_2424.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___256_2426 = fs  in
          {
            beta = (uu___256_2426.beta);
            iota = (uu___256_2426.iota);
            zeta = (uu___256_2426.zeta);
            weak = (uu___256_2426.weak);
            hnf = (uu___256_2426.hnf);
            primops = (uu___256_2426.primops);
            do_not_unfold_pure_lets = (uu___256_2426.do_not_unfold_pure_lets);
            unfold_until = (uu___256_2426.unfold_until);
            unfold_only = (uu___256_2426.unfold_only);
            unfold_fully = (uu___256_2426.unfold_fully);
            unfold_attr = (uu___256_2426.unfold_attr);
            unfold_tac = (uu___256_2426.unfold_tac);
            pure_subterms_within_computations =
              (uu___256_2426.pure_subterms_within_computations);
            simplify = (uu___256_2426.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___256_2426.allow_unbound_universes);
            reify_ = (uu___256_2426.reify_);
            compress_uvars = (uu___256_2426.compress_uvars);
            no_full_norm = (uu___256_2426.no_full_norm);
            check_no_uvars = (uu___256_2426.check_no_uvars);
            unmeta = (uu___256_2426.unmeta);
            unascribe = (uu___256_2426.unascribe);
            in_full_norm_request = (uu___256_2426.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___256_2426.weakly_reduce_scrutinee);
            nbe_step = (uu___256_2426.nbe_step);
            for_extraction = (uu___256_2426.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___257_2428 = fs  in
          {
            beta = (uu___257_2428.beta);
            iota = (uu___257_2428.iota);
            zeta = (uu___257_2428.zeta);
            weak = (uu___257_2428.weak);
            hnf = (uu___257_2428.hnf);
            primops = (uu___257_2428.primops);
            do_not_unfold_pure_lets = (uu___257_2428.do_not_unfold_pure_lets);
            unfold_until = (uu___257_2428.unfold_until);
            unfold_only = (uu___257_2428.unfold_only);
            unfold_fully = (uu___257_2428.unfold_fully);
            unfold_attr = (uu___257_2428.unfold_attr);
            unfold_tac = (uu___257_2428.unfold_tac);
            pure_subterms_within_computations =
              (uu___257_2428.pure_subterms_within_computations);
            simplify = (uu___257_2428.simplify);
            erase_universes = (uu___257_2428.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___257_2428.reify_);
            compress_uvars = (uu___257_2428.compress_uvars);
            no_full_norm = (uu___257_2428.no_full_norm);
            check_no_uvars = (uu___257_2428.check_no_uvars);
            unmeta = (uu___257_2428.unmeta);
            unascribe = (uu___257_2428.unascribe);
            in_full_norm_request = (uu___257_2428.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___257_2428.weakly_reduce_scrutinee);
            nbe_step = (uu___257_2428.nbe_step);
            for_extraction = (uu___257_2428.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___258_2430 = fs  in
          {
            beta = (uu___258_2430.beta);
            iota = (uu___258_2430.iota);
            zeta = (uu___258_2430.zeta);
            weak = (uu___258_2430.weak);
            hnf = (uu___258_2430.hnf);
            primops = (uu___258_2430.primops);
            do_not_unfold_pure_lets = (uu___258_2430.do_not_unfold_pure_lets);
            unfold_until = (uu___258_2430.unfold_until);
            unfold_only = (uu___258_2430.unfold_only);
            unfold_fully = (uu___258_2430.unfold_fully);
            unfold_attr = (uu___258_2430.unfold_attr);
            unfold_tac = (uu___258_2430.unfold_tac);
            pure_subterms_within_computations =
              (uu___258_2430.pure_subterms_within_computations);
            simplify = (uu___258_2430.simplify);
            erase_universes = (uu___258_2430.erase_universes);
            allow_unbound_universes = (uu___258_2430.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___258_2430.compress_uvars);
            no_full_norm = (uu___258_2430.no_full_norm);
            check_no_uvars = (uu___258_2430.check_no_uvars);
            unmeta = (uu___258_2430.unmeta);
            unascribe = (uu___258_2430.unascribe);
            in_full_norm_request = (uu___258_2430.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___258_2430.weakly_reduce_scrutinee);
            nbe_step = (uu___258_2430.nbe_step);
            for_extraction = (uu___258_2430.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___259_2432 = fs  in
          {
            beta = (uu___259_2432.beta);
            iota = (uu___259_2432.iota);
            zeta = (uu___259_2432.zeta);
            weak = (uu___259_2432.weak);
            hnf = (uu___259_2432.hnf);
            primops = (uu___259_2432.primops);
            do_not_unfold_pure_lets = (uu___259_2432.do_not_unfold_pure_lets);
            unfold_until = (uu___259_2432.unfold_until);
            unfold_only = (uu___259_2432.unfold_only);
            unfold_fully = (uu___259_2432.unfold_fully);
            unfold_attr = (uu___259_2432.unfold_attr);
            unfold_tac = (uu___259_2432.unfold_tac);
            pure_subterms_within_computations =
              (uu___259_2432.pure_subterms_within_computations);
            simplify = (uu___259_2432.simplify);
            erase_universes = (uu___259_2432.erase_universes);
            allow_unbound_universes = (uu___259_2432.allow_unbound_universes);
            reify_ = (uu___259_2432.reify_);
            compress_uvars = true;
            no_full_norm = (uu___259_2432.no_full_norm);
            check_no_uvars = (uu___259_2432.check_no_uvars);
            unmeta = (uu___259_2432.unmeta);
            unascribe = (uu___259_2432.unascribe);
            in_full_norm_request = (uu___259_2432.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___259_2432.weakly_reduce_scrutinee);
            nbe_step = (uu___259_2432.nbe_step);
            for_extraction = (uu___259_2432.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___260_2434 = fs  in
          {
            beta = (uu___260_2434.beta);
            iota = (uu___260_2434.iota);
            zeta = (uu___260_2434.zeta);
            weak = (uu___260_2434.weak);
            hnf = (uu___260_2434.hnf);
            primops = (uu___260_2434.primops);
            do_not_unfold_pure_lets = (uu___260_2434.do_not_unfold_pure_lets);
            unfold_until = (uu___260_2434.unfold_until);
            unfold_only = (uu___260_2434.unfold_only);
            unfold_fully = (uu___260_2434.unfold_fully);
            unfold_attr = (uu___260_2434.unfold_attr);
            unfold_tac = (uu___260_2434.unfold_tac);
            pure_subterms_within_computations =
              (uu___260_2434.pure_subterms_within_computations);
            simplify = (uu___260_2434.simplify);
            erase_universes = (uu___260_2434.erase_universes);
            allow_unbound_universes = (uu___260_2434.allow_unbound_universes);
            reify_ = (uu___260_2434.reify_);
            compress_uvars = (uu___260_2434.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___260_2434.check_no_uvars);
            unmeta = (uu___260_2434.unmeta);
            unascribe = (uu___260_2434.unascribe);
            in_full_norm_request = (uu___260_2434.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___260_2434.weakly_reduce_scrutinee);
            nbe_step = (uu___260_2434.nbe_step);
            for_extraction = (uu___260_2434.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___261_2436 = fs  in
          {
            beta = (uu___261_2436.beta);
            iota = (uu___261_2436.iota);
            zeta = (uu___261_2436.zeta);
            weak = (uu___261_2436.weak);
            hnf = (uu___261_2436.hnf);
            primops = (uu___261_2436.primops);
            do_not_unfold_pure_lets = (uu___261_2436.do_not_unfold_pure_lets);
            unfold_until = (uu___261_2436.unfold_until);
            unfold_only = (uu___261_2436.unfold_only);
            unfold_fully = (uu___261_2436.unfold_fully);
            unfold_attr = (uu___261_2436.unfold_attr);
            unfold_tac = (uu___261_2436.unfold_tac);
            pure_subterms_within_computations =
              (uu___261_2436.pure_subterms_within_computations);
            simplify = (uu___261_2436.simplify);
            erase_universes = (uu___261_2436.erase_universes);
            allow_unbound_universes = (uu___261_2436.allow_unbound_universes);
            reify_ = (uu___261_2436.reify_);
            compress_uvars = (uu___261_2436.compress_uvars);
            no_full_norm = (uu___261_2436.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___261_2436.unmeta);
            unascribe = (uu___261_2436.unascribe);
            in_full_norm_request = (uu___261_2436.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___261_2436.weakly_reduce_scrutinee);
            nbe_step = (uu___261_2436.nbe_step);
            for_extraction = (uu___261_2436.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___262_2438 = fs  in
          {
            beta = (uu___262_2438.beta);
            iota = (uu___262_2438.iota);
            zeta = (uu___262_2438.zeta);
            weak = (uu___262_2438.weak);
            hnf = (uu___262_2438.hnf);
            primops = (uu___262_2438.primops);
            do_not_unfold_pure_lets = (uu___262_2438.do_not_unfold_pure_lets);
            unfold_until = (uu___262_2438.unfold_until);
            unfold_only = (uu___262_2438.unfold_only);
            unfold_fully = (uu___262_2438.unfold_fully);
            unfold_attr = (uu___262_2438.unfold_attr);
            unfold_tac = (uu___262_2438.unfold_tac);
            pure_subterms_within_computations =
              (uu___262_2438.pure_subterms_within_computations);
            simplify = (uu___262_2438.simplify);
            erase_universes = (uu___262_2438.erase_universes);
            allow_unbound_universes = (uu___262_2438.allow_unbound_universes);
            reify_ = (uu___262_2438.reify_);
            compress_uvars = (uu___262_2438.compress_uvars);
            no_full_norm = (uu___262_2438.no_full_norm);
            check_no_uvars = (uu___262_2438.check_no_uvars);
            unmeta = true;
            unascribe = (uu___262_2438.unascribe);
            in_full_norm_request = (uu___262_2438.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___262_2438.weakly_reduce_scrutinee);
            nbe_step = (uu___262_2438.nbe_step);
            for_extraction = (uu___262_2438.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___263_2440 = fs  in
          {
            beta = (uu___263_2440.beta);
            iota = (uu___263_2440.iota);
            zeta = (uu___263_2440.zeta);
            weak = (uu___263_2440.weak);
            hnf = (uu___263_2440.hnf);
            primops = (uu___263_2440.primops);
            do_not_unfold_pure_lets = (uu___263_2440.do_not_unfold_pure_lets);
            unfold_until = (uu___263_2440.unfold_until);
            unfold_only = (uu___263_2440.unfold_only);
            unfold_fully = (uu___263_2440.unfold_fully);
            unfold_attr = (uu___263_2440.unfold_attr);
            unfold_tac = (uu___263_2440.unfold_tac);
            pure_subterms_within_computations =
              (uu___263_2440.pure_subterms_within_computations);
            simplify = (uu___263_2440.simplify);
            erase_universes = (uu___263_2440.erase_universes);
            allow_unbound_universes = (uu___263_2440.allow_unbound_universes);
            reify_ = (uu___263_2440.reify_);
            compress_uvars = (uu___263_2440.compress_uvars);
            no_full_norm = (uu___263_2440.no_full_norm);
            check_no_uvars = (uu___263_2440.check_no_uvars);
            unmeta = (uu___263_2440.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___263_2440.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___263_2440.weakly_reduce_scrutinee);
            nbe_step = (uu___263_2440.nbe_step);
            for_extraction = (uu___263_2440.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___264_2442 = fs  in
          {
            beta = (uu___264_2442.beta);
            iota = (uu___264_2442.iota);
            zeta = (uu___264_2442.zeta);
            weak = (uu___264_2442.weak);
            hnf = (uu___264_2442.hnf);
            primops = (uu___264_2442.primops);
            do_not_unfold_pure_lets = (uu___264_2442.do_not_unfold_pure_lets);
            unfold_until = (uu___264_2442.unfold_until);
            unfold_only = (uu___264_2442.unfold_only);
            unfold_fully = (uu___264_2442.unfold_fully);
            unfold_attr = (uu___264_2442.unfold_attr);
            unfold_tac = (uu___264_2442.unfold_tac);
            pure_subterms_within_computations =
              (uu___264_2442.pure_subterms_within_computations);
            simplify = (uu___264_2442.simplify);
            erase_universes = (uu___264_2442.erase_universes);
            allow_unbound_universes = (uu___264_2442.allow_unbound_universes);
            reify_ = (uu___264_2442.reify_);
            compress_uvars = (uu___264_2442.compress_uvars);
            no_full_norm = (uu___264_2442.no_full_norm);
            check_no_uvars = (uu___264_2442.check_no_uvars);
            unmeta = (uu___264_2442.unmeta);
            unascribe = (uu___264_2442.unascribe);
            in_full_norm_request = (uu___264_2442.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___264_2442.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___264_2442.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___265_2444 = fs  in
          {
            beta = (uu___265_2444.beta);
            iota = (uu___265_2444.iota);
            zeta = (uu___265_2444.zeta);
            weak = (uu___265_2444.weak);
            hnf = (uu___265_2444.hnf);
            primops = (uu___265_2444.primops);
            do_not_unfold_pure_lets = (uu___265_2444.do_not_unfold_pure_lets);
            unfold_until = (uu___265_2444.unfold_until);
            unfold_only = (uu___265_2444.unfold_only);
            unfold_fully = (uu___265_2444.unfold_fully);
            unfold_attr = (uu___265_2444.unfold_attr);
            unfold_tac = (uu___265_2444.unfold_tac);
            pure_subterms_within_computations =
              (uu___265_2444.pure_subterms_within_computations);
            simplify = (uu___265_2444.simplify);
            erase_universes = (uu___265_2444.erase_universes);
            allow_unbound_universes = (uu___265_2444.allow_unbound_universes);
            reify_ = (uu___265_2444.reify_);
            compress_uvars = (uu___265_2444.compress_uvars);
            no_full_norm = (uu___265_2444.no_full_norm);
            check_no_uvars = (uu___265_2444.check_no_uvars);
            unmeta = (uu___265_2444.unmeta);
            unascribe = (uu___265_2444.unascribe);
            in_full_norm_request = (uu___265_2444.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___265_2444.weakly_reduce_scrutinee);
            nbe_step = (uu___265_2444.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____2502  -> []) } 
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
    let uu____3562 =
      let uu____3566 =
        let uu____3570 =
          let uu____3572 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____3572  in
        [uu____3570; "}"]  in
      "{" :: uu____3566  in
    FStar_String.concat "\n" uu____3562
  
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
             let uu____3620 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____3620 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____3636 = FStar_Util.psmap_empty ()  in add_steps uu____3636 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____3652 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____3652
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____3666 =
        let uu____3669 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____3669  in
      FStar_Util.is_some uu____3666
  
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
      let uu____3782 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____3782 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____3818 = FStar_Syntax_Embeddings.embed emb x  in
        uu____3818 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____3874 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____3874 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____3893 .
    'Auu____3893 ->
      FStar_Range.range -> 'Auu____3893 FStar_Syntax_Syntax.syntax
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
    let uu____4014 =
      let uu____4023 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____4023  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4014  in
  let arg_as_bounded_int1 uu____4053 =
    match uu____4053 with
    | (a,uu____4067) ->
        let uu____4078 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____4078 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____4122 =
               let uu____4137 =
                 let uu____4138 = FStar_Syntax_Subst.compress hd1  in
                 uu____4138.FStar_Syntax_Syntax.n  in
               (uu____4137, args)  in
             (match uu____4122 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____4159)::[]) when
                  let uu____4194 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____4194 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____4198 =
                    let uu____4199 = FStar_Syntax_Subst.compress arg1  in
                    uu____4199.FStar_Syntax_Syntax.n  in
                  (match uu____4198 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____4221 =
                         let uu____4226 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____4226)  in
                       FStar_Pervasives_Native.Some uu____4221
                   | uu____4231 -> FStar_Pervasives_Native.None)
              | uu____4236 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4298 = f a  in FStar_Pervasives_Native.Some uu____4298
    | uu____4299 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4355 = f a0 a1  in FStar_Pervasives_Native.Some uu____4355
    | uu____4356 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____4425 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____4425  in
  let binary_op1 as_a f res n1 args =
    let uu____4509 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____4509  in
  let as_primitive_step is_strong uu____4565 =
    match uu____4565 with
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
           let uu____4677 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____4677)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4720 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____4720)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____4762 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____4762)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4816 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____4816)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4870 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____4870)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____5025 =
          let uu____5034 = as_a a  in
          let uu____5037 = as_b b  in (uu____5034, uu____5037)  in
        (match uu____5025 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5052 =
               let uu____5053 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5053  in
             FStar_Pervasives_Native.Some uu____5052
         | uu____5054 -> FStar_Pervasives_Native.None)
    | uu____5063 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____5085 =
        let uu____5086 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5086  in
      mk uu____5085 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5100 =
      let uu____5103 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5103  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5100  in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5151 =
      let uu____5152 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5152  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____5151  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____5240 = arg_as_string1 a1  in
        (match uu____5240 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5249 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____5249 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5267 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____5267
              | uu____5269 -> FStar_Pervasives_Native.None)
         | uu____5275 -> FStar_Pervasives_Native.None)
    | uu____5279 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5362 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____5362 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5378 = arg_as_string1 a2  in
             (match uu____5378 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____5391 =
                    let uu____5392 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____5392 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5391
              | uu____5402 -> FStar_Pervasives_Native.None)
         | uu____5406 -> FStar_Pervasives_Native.None)
    | uu____5412 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____5452 =
          let uu____5466 = arg_as_string1 a1  in
          let uu____5470 = arg_as_int1 a2  in
          let uu____5473 = arg_as_int1 a3  in
          (uu____5466, uu____5470, uu____5473)  in
        (match uu____5452 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___267_5506  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____5511 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____5511) ()
              with | uu___266_5514 -> FStar_Pervasives_Native.None)
         | uu____5517 -> FStar_Pervasives_Native.None)
    | uu____5531 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5545 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____5545  in
  let string_of_bool1 rng b =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5601 =
          let uu____5623 = arg_as_string1 fn  in
          let uu____5627 = arg_as_int1 from_line  in
          let uu____5630 = arg_as_int1 from_col  in
          let uu____5633 = arg_as_int1 to_line  in
          let uu____5636 = arg_as_int1 to_col  in
          (uu____5623, uu____5627, uu____5630, uu____5633, uu____5636)  in
        (match uu____5601 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5671 =
                 let uu____5672 = FStar_BigInt.to_int_fs from_l  in
                 let uu____5674 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____5672 uu____5674  in
               let uu____5676 =
                 let uu____5677 = FStar_BigInt.to_int_fs to_l  in
                 let uu____5679 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____5677 uu____5679  in
               FStar_Range.mk_range fn1 uu____5671 uu____5676  in
             let uu____5681 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____5681
         | uu____5682 -> FStar_Pervasives_Native.None)
    | uu____5704 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____5750)::(a1,uu____5752)::(a2,uu____5754)::[] ->
        let uu____5811 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____5811 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5820 -> FStar_Pervasives_Native.None)
    | uu____5821 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____5866)::[] ->
        let uu____5883 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____5883 with
         | FStar_Pervasives_Native.Some r ->
             let uu____5889 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____5889
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____5890 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____5910  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____5945 =
      let uu____5976 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)), uu____5976)
       in
    let uu____6011 =
      let uu____6044 =
        let uu____6075 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____6075)
         in
      let uu____6116 =
        let uu____6149 =
          let uu____6180 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____6180)
           in
        let uu____6221 =
          let uu____6254 =
            let uu____6285 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____6285)
             in
          let uu____6326 =
            let uu____6359 =
              let uu____6390 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____6390)
               in
            let uu____6431 =
              let uu____6464 =
                let uu____6495 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____6507 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____6507)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____6539 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____6539)), uu____6495)
                 in
              let uu____6542 =
                let uu____6575 =
                  let uu____6606 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____6618 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____6618)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____6650 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____6650)), uu____6606)
                   in
                let uu____6653 =
                  let uu____6686 =
                    let uu____6717 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____6729 = FStar_BigInt.gt_big_int x y  in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____6729)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____6761 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____6761)), uu____6717)
                     in
                  let uu____6764 =
                    let uu____6797 =
                      let uu____6828 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____6840 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____6840)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____6872 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____6872)), uu____6828)
                       in
                    let uu____6875 =
                      let uu____6908 =
                        let uu____6939 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____6939)
                         in
                      let uu____6980 =
                        let uu____7013 =
                          let uu____7044 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____7044)
                           in
                        let uu____7081 =
                          let uu____7114 =
                            let uu____7145 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____7145)
                             in
                          let uu____7190 =
                            let uu____7223 =
                              let uu____7254 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____7254)
                               in
                            let uu____7299 =
                              let uu____7332 =
                                let uu____7363 =
                                  FStar_TypeChecker_NBETerm.binary_string_op
                                    (fun x  -> fun y  -> Prims.strcat x y)
                                   in
                                (FStar_Parser_Const.strcat_lid,
                                  (Prims.parse_int "2"),
                                  (Prims.parse_int "0"),
                                  (binary_string_op1
                                     (fun x  -> fun y  -> Prims.strcat x y)),
                                  uu____7363)
                                 in
                              let uu____7408 =
                                let uu____7441 =
                                  let uu____7472 =
                                    FStar_TypeChecker_NBETerm.binary_string_op
                                      (fun x  -> fun y  -> Prims.strcat x y)
                                     in
                                  (FStar_Parser_Const.strcat_lid',
                                    (Prims.parse_int "2"),
                                    (Prims.parse_int "0"),
                                    (binary_string_op1
                                       (fun x  -> fun y  -> Prims.strcat x y)),
                                    uu____7472)
                                   in
                                let uu____7517 =
                                  let uu____7550 =
                                    let uu____7583 =
                                      let uu____7614 =
                                        FStar_TypeChecker_NBETerm.unary_op
                                          FStar_TypeChecker_NBETerm.arg_as_int
                                          FStar_TypeChecker_NBETerm.string_of_int
                                         in
                                      (FStar_Parser_Const.string_of_int_lid,
                                        (Prims.parse_int "1"),
                                        (Prims.parse_int "0"),
                                        (unary_op1 arg_as_int1 string_of_int1),
                                        uu____7614)
                                       in
                                    let uu____7643 =
                                      let uu____7676 =
                                        let uu____7707 =
                                          FStar_TypeChecker_NBETerm.unary_op
                                            FStar_TypeChecker_NBETerm.arg_as_bool
                                            FStar_TypeChecker_NBETerm.string_of_bool
                                           in
                                        (FStar_Parser_Const.string_of_bool_lid,
                                          (Prims.parse_int "1"),
                                          (Prims.parse_int "0"),
                                          (unary_op1 arg_as_bool1
                                             string_of_bool1), uu____7707)
                                         in
                                      let uu____7738 =
                                        let uu____7771 =
                                          let uu____7802 =
                                            FStar_TypeChecker_NBETerm.binary_op
                                              FStar_TypeChecker_NBETerm.arg_as_string
                                              FStar_TypeChecker_NBETerm.string_compare'
                                             in
                                          (FStar_Parser_Const.string_compare,
                                            (Prims.parse_int "2"),
                                            (Prims.parse_int "0"),
                                            (binary_op1 arg_as_string1
                                               string_compare'1), uu____7802)
                                           in
                                        let uu____7833 =
                                          let uu____7866 =
                                            let uu____7899 =
                                              let uu____7932 =
                                                let uu____7963 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                let uu____7971 =
                                                  FStar_TypeChecker_NBETerm.unary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.list_of_string'
                                                   in
                                                (uu____7963,
                                                  (Prims.parse_int "1"),
                                                  (Prims.parse_int "0"),
                                                  (unary_op1 arg_as_string1
                                                     list_of_string'1),
                                                  uu____7971)
                                                 in
                                              let uu____8002 =
                                                let uu____8035 =
                                                  let uu____8066 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  let uu____8074 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      (FStar_TypeChecker_NBETerm.arg_as_list
                                                         FStar_TypeChecker_NBETerm.e_char)
                                                      FStar_TypeChecker_NBETerm.string_of_list'
                                                     in
                                                  (uu____8066,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1
                                                       (arg_as_list1
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'1),
                                                    uu____8074)
                                                   in
                                                let uu____8111 =
                                                  let uu____8144 =
                                                    let uu____8175 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "split"]
                                                       in
                                                    (uu____8175,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_split'1,
                                                      FStar_TypeChecker_NBETerm.string_split')
                                                     in
                                                  let uu____8205 =
                                                    let uu____8238 =
                                                      let uu____8269 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "String";
                                                          "substring"]
                                                         in
                                                      (uu____8269,
                                                        (Prims.parse_int "3"),
                                                        (Prims.parse_int "0"),
                                                        string_substring'1,
                                                        FStar_TypeChecker_NBETerm.string_substring')
                                                       in
                                                    let uu____8299 =
                                                      let uu____8332 =
                                                        let uu____8363 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "String";
                                                            "concat"]
                                                           in
                                                        (uu____8363,
                                                          (Prims.parse_int "2"),
                                                          (Prims.parse_int "0"),
                                                          string_concat'1,
                                                          FStar_TypeChecker_NBETerm.string_concat')
                                                         in
                                                      let uu____8393 =
                                                        let uu____8426 =
                                                          let uu____8457 =
                                                            FStar_Parser_Const.p2l
                                                              ["Prims";
                                                              "mk_range"]
                                                             in
                                                          (uu____8457,
                                                            (Prims.parse_int "5"),
                                                            (Prims.parse_int "0"),
                                                            mk_range1,
                                                            FStar_TypeChecker_NBETerm.mk_range)
                                                           in
                                                        let uu____8485 =
                                                          let uu____8518 =
                                                            let uu____8549 =
                                                              FStar_Parser_Const.p2l
                                                                ["FStar";
                                                                "Range";
                                                                "prims_to_fstar_range"]
                                                               in
                                                            (uu____8549,
                                                              (Prims.parse_int "1"),
                                                              (Prims.parse_int "0"),
                                                              prims_to_fstar_range_step1,
                                                              FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                             in
                                                          [uu____8518]  in
                                                        uu____8426 ::
                                                          uu____8485
                                                         in
                                                      uu____8332 ::
                                                        uu____8393
                                                       in
                                                    uu____8238 :: uu____8299
                                                     in
                                                  uu____8144 :: uu____8205
                                                   in
                                                uu____8035 :: uu____8111  in
                                              uu____7932 :: uu____8002  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (Prims.parse_int "0"),
                                              (decidable_eq1 true),
                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                 true))
                                              :: uu____7899
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (Prims.parse_int "0"),
                                            (decidable_eq1 false),
                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                               false))
                                            :: uu____7866
                                           in
                                        uu____7771 :: uu____7833  in
                                      uu____7676 :: uu____7738  in
                                    uu____7583 :: uu____7643  in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (Prims.parse_int "0"),
                                    (mixed_binary_op1 arg_as_int1
                                       arg_as_char1
                                       (embed_simple
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____9080 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____9080 y)),
                                    (FStar_TypeChecker_NBETerm.mixed_binary_op
                                       FStar_TypeChecker_NBETerm.arg_as_int
                                       FStar_TypeChecker_NBETerm.arg_as_char
                                       (FStar_TypeChecker_NBETerm.embed
                                          FStar_TypeChecker_NBETerm.e_string
                                          bogus_cbs)
                                       (fun x  ->
                                          fun y  ->
                                            let uu____9091 =
                                              FStar_BigInt.to_int_fs x  in
                                            FStar_String.make uu____9091 y)))
                                    :: uu____7550
                                   in
                                uu____7441 :: uu____7517  in
                              uu____7332 :: uu____7408  in
                            uu____7223 :: uu____7299  in
                          uu____7114 :: uu____7190  in
                        uu____7013 :: uu____7081  in
                      uu____6908 :: uu____6980  in
                    uu____6797 :: uu____6875  in
                  uu____6686 :: uu____6764  in
                uu____6575 :: uu____6653  in
              uu____6464 :: uu____6542  in
            uu____6359 :: uu____6431  in
          uu____6254 :: uu____6326  in
        uu____6149 :: uu____6221  in
      uu____6044 :: uu____6116  in
    uu____5945 :: uu____6011  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9687 =
        let uu____9692 =
          let uu____9693 = FStar_Syntax_Syntax.as_arg c  in [uu____9693]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9692  in
      uu____9687 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9825 =
                let uu____9856 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____9863 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____9881  ->
                       fun uu____9882  ->
                         match (uu____9881, uu____9882) with
                         | ((int_to_t1,x),(uu____9901,y)) ->
                             let uu____9911 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____9911)
                   in
                (uu____9856, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____9947  ->
                          fun uu____9948  ->
                            match (uu____9947, uu____9948) with
                            | ((int_to_t1,x),(uu____9967,y)) ->
                                let uu____9977 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded1 r int_to_t1 uu____9977)),
                  uu____9863)
                 in
              let uu____9978 =
                let uu____10011 =
                  let uu____10042 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____10049 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____10067  ->
                         fun uu____10068  ->
                           match (uu____10067, uu____10068) with
                           | ((int_to_t1,x),(uu____10087,y)) ->
                               let uu____10097 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____10097)
                     in
                  (uu____10042, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____10133  ->
                            fun uu____10134  ->
                              match (uu____10133, uu____10134) with
                              | ((int_to_t1,x),(uu____10153,y)) ->
                                  let uu____10163 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____10163)),
                    uu____10049)
                   in
                let uu____10164 =
                  let uu____10197 =
                    let uu____10228 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____10235 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____10253  ->
                           fun uu____10254  ->
                             match (uu____10253, uu____10254) with
                             | ((int_to_t1,x),(uu____10273,y)) ->
                                 let uu____10283 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____10283)
                       in
                    (uu____10228, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____10319  ->
                              fun uu____10320  ->
                                match (uu____10319, uu____10320) with
                                | ((int_to_t1,x),(uu____10339,y)) ->
                                    let uu____10349 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____10349)),
                      uu____10235)
                     in
                  let uu____10350 =
                    let uu____10383 =
                      let uu____10414 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____10421 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____10435  ->
                             match uu____10435 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____10414, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____10473  ->
                                match uu____10473 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____10421)
                       in
                    [uu____10383]  in
                  uu____10197 :: uu____10350  in
                uu____10011 :: uu____10164  in
              uu____9825 :: uu____9978))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____10734 =
                let uu____10765 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____10772 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10790  ->
                       fun uu____10791  ->
                         match (uu____10790, uu____10791) with
                         | ((int_to_t1,x),(uu____10810,y)) ->
                             let uu____10820 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____10820)
                   in
                (uu____10765, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____10856  ->
                          fun uu____10857  ->
                            match (uu____10856, uu____10857) with
                            | ((int_to_t1,x),(uu____10876,y)) ->
                                let uu____10886 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____10886)),
                  uu____10772)
                 in
              let uu____10887 =
                let uu____10920 =
                  let uu____10951 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____10958 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____10976  ->
                         fun uu____10977  ->
                           match (uu____10976, uu____10977) with
                           | ((int_to_t1,x),(uu____10996,y)) ->
                               let uu____11006 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11006)
                     in
                  (uu____10951, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11042  ->
                            fun uu____11043  ->
                              match (uu____11042, uu____11043) with
                              | ((int_to_t1,x),(uu____11062,y)) ->
                                  let uu____11072 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11072)),
                    uu____10958)
                   in
                [uu____10920]  in
              uu____10734 :: uu____10887))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____11181 ->
          let uu____11183 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____11183
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____11290 =
                let uu____11321 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____11328 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11346  ->
                       fun uu____11347  ->
                         match (uu____11346, uu____11347) with
                         | ((int_to_t1,x),(uu____11366,y)) ->
                             let uu____11376 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____11376)
                   in
                (uu____11321, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____11412  ->
                          fun uu____11413  ->
                            match (uu____11412, uu____11413) with
                            | ((int_to_t1,x),(uu____11432,y)) ->
                                let uu____11442 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____11442)),
                  uu____11328)
                 in
              let uu____11443 =
                let uu____11476 =
                  let uu____11507 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____11514 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11532  ->
                         fun uu____11533  ->
                           match (uu____11532, uu____11533) with
                           | ((int_to_t1,x),(uu____11552,y)) ->
                               let uu____11562 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____11562)
                     in
                  (uu____11507, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____11598  ->
                            fun uu____11599  ->
                              match (uu____11598, uu____11599) with
                              | ((int_to_t1,x),(uu____11618,y)) ->
                                  let uu____11628 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____11628)),
                    uu____11514)
                   in
                let uu____11629 =
                  let uu____11662 =
                    let uu____11693 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____11700 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____11718  ->
                           fun uu____11719  ->
                             match (uu____11718, uu____11719) with
                             | ((int_to_t1,x),(uu____11738,y)) ->
                                 let uu____11748 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____11748)
                       in
                    (uu____11693, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____11784  ->
                              fun uu____11785  ->
                                match (uu____11784, uu____11785) with
                                | ((int_to_t1,x),(uu____11804,y)) ->
                                    let uu____11814 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____11814)),
                      uu____11700)
                     in
                  let uu____11815 =
                    let uu____11848 =
                      let uu____11879 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____11886 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____11901  ->
                             match uu____11901 with
                             | (int_to_t1,x) ->
                                 let uu____11908 =
                                   let uu____11909 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____11910 = mask m  in
                                   FStar_BigInt.logand_big_int uu____11909
                                     uu____11910
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____11908)
                         in
                      (uu____11879, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____11943  ->
                                match uu____11943 with
                                | (int_to_t1,x) ->
                                    let uu____11950 =
                                      let uu____11951 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____11952 = mask m  in
                                      FStar_BigInt.logand_big_int uu____11951
                                        uu____11952
                                       in
                                    int_as_bounded1 r int_to_t1 uu____11950)),
                        uu____11886)
                       in
                    let uu____11953 =
                      let uu____11986 =
                        let uu____12017 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____12024 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____12042  ->
                               fun uu____12043  ->
                                 match (uu____12042, uu____12043) with
                                 | ((int_to_t1,x),(uu____12062,y)) ->
                                     let uu____12072 =
                                       let uu____12073 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____12074 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____12073 uu____12074
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____12072)
                           in
                        (uu____12017, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____12110  ->
                                  fun uu____12111  ->
                                    match (uu____12110, uu____12111) with
                                    | ((int_to_t1,x),(uu____12130,y)) ->
                                        let uu____12140 =
                                          let uu____12141 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____12142 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____12141 uu____12142
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____12140)), uu____12024)
                         in
                      let uu____12143 =
                        let uu____12176 =
                          let uu____12207 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____12214 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____12232  ->
                                 fun uu____12233  ->
                                   match (uu____12232, uu____12233) with
                                   | ((int_to_t1,x),(uu____12252,y)) ->
                                       let uu____12262 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____12262)
                             in
                          (uu____12207, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____12298  ->
                                    fun uu____12299  ->
                                      match (uu____12298, uu____12299) with
                                      | ((int_to_t1,x),(uu____12318,y)) ->
                                          let uu____12328 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____12328)), uu____12214)
                           in
                        [uu____12176]  in
                      uu____11986 :: uu____12143  in
                    uu____11848 :: uu____11953  in
                  uu____11662 :: uu____11815  in
                uu____11476 :: uu____11629  in
              uu____11290 :: uu____11443))
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
    | (_typ,uu____12734)::(a1,uu____12736)::(a2,uu____12738)::[] ->
        let uu____12795 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____12795 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___268_12799 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___268_12799.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___268_12799.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___269_12801 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___269_12801.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___269_12801.FStar_Syntax_Syntax.vars)
                })
         | uu____12802 -> FStar_Pervasives_Native.None)
    | uu____12803 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____12835)::(t2,uu____12837)::(a1,uu____12839)::(a2,uu____12841)::[]
        ->
        let uu____12914 =
          let uu____12915 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____12916 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____12915 uu____12916  in
        (match uu____12914 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___270_12920 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___270_12920.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___270_12920.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___271_12922 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___271_12922.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___271_12922.FStar_Syntax_Syntax.vars)
                })
         | uu____12923 -> FStar_Pervasives_Native.None)
    | uu____12924 -> failwith "Unexpected number of arguments"  in
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
  fun uu____12955  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____12972 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____12972 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____13001 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        Prims.strcat uu____13001 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____13012  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____13083  ->
           fun uu____13084  ->
             match (uu____13083, uu____13084) with
             | ((uu____13110,t1),(uu____13112,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____13146  ->
         fun rest  ->
           match uu____13146 with
           | (nm,ms) ->
               let uu____13162 =
                 let uu____13164 =
                   let uu____13166 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____13166  in
                 FStar_Util.format2 "%sms --- %s\n" uu____13164 nm  in
               Prims.strcat uu____13162 rest) pairs1 ""
  
let (plugins :
  (primitive_step -> unit,unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____13197 =
      let uu____13200 = FStar_ST.op_Bang plugins  in p :: uu____13200  in
    FStar_ST.op_Colon_Equals plugins uu____13197  in
  let retrieve uu____13300 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____13375  ->
    let uu____13376 = FStar_Options.no_plugins ()  in
    if uu____13376 then [] else FStar_Pervasives_Native.snd plugins ()
  
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
               (fun uu___238_13424  ->
                  match uu___238_13424 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____13428 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____13434 -> d  in
        let uu____13437 = to_fsteps s  in
        let uu____13438 =
          let uu____13439 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____13442 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____13445 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____13448 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____13451 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____13454 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____13457 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____13460 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____13463 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____13439;
            top = uu____13442;
            cfg = uu____13445;
            primop = uu____13448;
            unfolding = uu____13451;
            b380 = uu____13454;
            wpe = uu____13457;
            norm_delayed = uu____13460;
            print_normalized = uu____13463
          }  in
        let uu____13466 =
          let uu____13469 =
            let uu____13472 = retrieve_plugins ()  in
            FStar_List.append uu____13472 psteps  in
          add_steps built_in_primitive_steps uu____13469  in
        let uu____13475 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____13478 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____13478)
           in
        {
          steps = uu____13437;
          tcenv = e;
          debug = uu____13438;
          delta_level = d1;
          primitive_steps = uu____13466;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____13475;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 