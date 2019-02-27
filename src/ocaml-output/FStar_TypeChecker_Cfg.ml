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
          let uu____65084 =
            let uu____65086 = f1 x  in FStar_String.op_Hat uu____65086 ")"
             in
          FStar_String.op_Hat "Some (" uu____65084
       in
    let b = FStar_Util.string_of_bool  in
    let uu____65097 =
      let uu____65101 = FStar_All.pipe_right f.beta b  in
      let uu____65105 =
        let uu____65109 = FStar_All.pipe_right f.iota b  in
        let uu____65113 =
          let uu____65117 = FStar_All.pipe_right f.zeta b  in
          let uu____65121 =
            let uu____65125 = FStar_All.pipe_right f.weak b  in
            let uu____65129 =
              let uu____65133 = FStar_All.pipe_right f.hnf b  in
              let uu____65137 =
                let uu____65141 = FStar_All.pipe_right f.primops b  in
                let uu____65145 =
                  let uu____65149 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____65153 =
                    let uu____65157 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____65162 =
                      let uu____65166 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____65180 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____65180
                                  (FStar_String.concat ", ")))
                         in
                      let uu____65190 =
                        let uu____65194 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____65208 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____65208
                                    (FStar_String.concat ", ")))
                           in
                        let uu____65218 =
                          let uu____65222 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____65236 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____65236
                                      (FStar_String.concat ", ")))
                             in
                          let uu____65246 =
                            let uu____65250 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____65254 =
                              let uu____65258 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____65262 =
                                let uu____65266 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____65270 =
                                  let uu____65274 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____65278 =
                                    let uu____65282 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____65286 =
                                      let uu____65290 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____65294 =
                                        let uu____65298 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____65302 =
                                          let uu____65306 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____65310 =
                                            let uu____65314 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____65318 =
                                              let uu____65322 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____65326 =
                                                let uu____65330 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____65334 =
                                                  let uu____65338 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____65342 =
                                                    let uu____65346 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____65346]  in
                                                  uu____65338 :: uu____65342
                                                   in
                                                uu____65330 :: uu____65334
                                                 in
                                              uu____65322 :: uu____65326  in
                                            uu____65314 :: uu____65318  in
                                          uu____65306 :: uu____65310  in
                                        uu____65298 :: uu____65302  in
                                      uu____65290 :: uu____65294  in
                                    uu____65282 :: uu____65286  in
                                  uu____65274 :: uu____65278  in
                                uu____65266 :: uu____65270  in
                              uu____65258 :: uu____65262  in
                            uu____65250 :: uu____65254  in
                          uu____65222 :: uu____65246  in
                        uu____65194 :: uu____65218  in
                      uu____65166 :: uu____65190  in
                    uu____65157 :: uu____65162  in
                  uu____65149 :: uu____65153  in
                uu____65141 :: uu____65145  in
              uu____65133 :: uu____65137  in
            uu____65125 :: uu____65129  in
          uu____65117 :: uu____65121  in
        uu____65109 :: uu____65113  in
      uu____65101 :: uu____65105  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____65097
  
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
          let uu___625_65416 = fs  in
          {
            beta = true;
            iota = (uu___625_65416.iota);
            zeta = (uu___625_65416.zeta);
            weak = (uu___625_65416.weak);
            hnf = (uu___625_65416.hnf);
            primops = (uu___625_65416.primops);
            do_not_unfold_pure_lets =
              (uu___625_65416.do_not_unfold_pure_lets);
            unfold_until = (uu___625_65416.unfold_until);
            unfold_only = (uu___625_65416.unfold_only);
            unfold_fully = (uu___625_65416.unfold_fully);
            unfold_attr = (uu___625_65416.unfold_attr);
            unfold_tac = (uu___625_65416.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_65416.pure_subterms_within_computations);
            simplify = (uu___625_65416.simplify);
            erase_universes = (uu___625_65416.erase_universes);
            allow_unbound_universes =
              (uu___625_65416.allow_unbound_universes);
            reify_ = (uu___625_65416.reify_);
            compress_uvars = (uu___625_65416.compress_uvars);
            no_full_norm = (uu___625_65416.no_full_norm);
            check_no_uvars = (uu___625_65416.check_no_uvars);
            unmeta = (uu___625_65416.unmeta);
            unascribe = (uu___625_65416.unascribe);
            in_full_norm_request = (uu___625_65416.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_65416.weakly_reduce_scrutinee);
            nbe_step = (uu___625_65416.nbe_step);
            for_extraction = (uu___625_65416.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_65418 = fs  in
          {
            beta = (uu___628_65418.beta);
            iota = true;
            zeta = (uu___628_65418.zeta);
            weak = (uu___628_65418.weak);
            hnf = (uu___628_65418.hnf);
            primops = (uu___628_65418.primops);
            do_not_unfold_pure_lets =
              (uu___628_65418.do_not_unfold_pure_lets);
            unfold_until = (uu___628_65418.unfold_until);
            unfold_only = (uu___628_65418.unfold_only);
            unfold_fully = (uu___628_65418.unfold_fully);
            unfold_attr = (uu___628_65418.unfold_attr);
            unfold_tac = (uu___628_65418.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_65418.pure_subterms_within_computations);
            simplify = (uu___628_65418.simplify);
            erase_universes = (uu___628_65418.erase_universes);
            allow_unbound_universes =
              (uu___628_65418.allow_unbound_universes);
            reify_ = (uu___628_65418.reify_);
            compress_uvars = (uu___628_65418.compress_uvars);
            no_full_norm = (uu___628_65418.no_full_norm);
            check_no_uvars = (uu___628_65418.check_no_uvars);
            unmeta = (uu___628_65418.unmeta);
            unascribe = (uu___628_65418.unascribe);
            in_full_norm_request = (uu___628_65418.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_65418.weakly_reduce_scrutinee);
            nbe_step = (uu___628_65418.nbe_step);
            for_extraction = (uu___628_65418.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_65420 = fs  in
          {
            beta = (uu___631_65420.beta);
            iota = (uu___631_65420.iota);
            zeta = true;
            weak = (uu___631_65420.weak);
            hnf = (uu___631_65420.hnf);
            primops = (uu___631_65420.primops);
            do_not_unfold_pure_lets =
              (uu___631_65420.do_not_unfold_pure_lets);
            unfold_until = (uu___631_65420.unfold_until);
            unfold_only = (uu___631_65420.unfold_only);
            unfold_fully = (uu___631_65420.unfold_fully);
            unfold_attr = (uu___631_65420.unfold_attr);
            unfold_tac = (uu___631_65420.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_65420.pure_subterms_within_computations);
            simplify = (uu___631_65420.simplify);
            erase_universes = (uu___631_65420.erase_universes);
            allow_unbound_universes =
              (uu___631_65420.allow_unbound_universes);
            reify_ = (uu___631_65420.reify_);
            compress_uvars = (uu___631_65420.compress_uvars);
            no_full_norm = (uu___631_65420.no_full_norm);
            check_no_uvars = (uu___631_65420.check_no_uvars);
            unmeta = (uu___631_65420.unmeta);
            unascribe = (uu___631_65420.unascribe);
            in_full_norm_request = (uu___631_65420.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_65420.weakly_reduce_scrutinee);
            nbe_step = (uu___631_65420.nbe_step);
            for_extraction = (uu___631_65420.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_65422 = fs  in
          {
            beta = false;
            iota = (uu___635_65422.iota);
            zeta = (uu___635_65422.zeta);
            weak = (uu___635_65422.weak);
            hnf = (uu___635_65422.hnf);
            primops = (uu___635_65422.primops);
            do_not_unfold_pure_lets =
              (uu___635_65422.do_not_unfold_pure_lets);
            unfold_until = (uu___635_65422.unfold_until);
            unfold_only = (uu___635_65422.unfold_only);
            unfold_fully = (uu___635_65422.unfold_fully);
            unfold_attr = (uu___635_65422.unfold_attr);
            unfold_tac = (uu___635_65422.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_65422.pure_subterms_within_computations);
            simplify = (uu___635_65422.simplify);
            erase_universes = (uu___635_65422.erase_universes);
            allow_unbound_universes =
              (uu___635_65422.allow_unbound_universes);
            reify_ = (uu___635_65422.reify_);
            compress_uvars = (uu___635_65422.compress_uvars);
            no_full_norm = (uu___635_65422.no_full_norm);
            check_no_uvars = (uu___635_65422.check_no_uvars);
            unmeta = (uu___635_65422.unmeta);
            unascribe = (uu___635_65422.unascribe);
            in_full_norm_request = (uu___635_65422.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_65422.weakly_reduce_scrutinee);
            nbe_step = (uu___635_65422.nbe_step);
            for_extraction = (uu___635_65422.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_65424 = fs  in
          {
            beta = (uu___639_65424.beta);
            iota = false;
            zeta = (uu___639_65424.zeta);
            weak = (uu___639_65424.weak);
            hnf = (uu___639_65424.hnf);
            primops = (uu___639_65424.primops);
            do_not_unfold_pure_lets =
              (uu___639_65424.do_not_unfold_pure_lets);
            unfold_until = (uu___639_65424.unfold_until);
            unfold_only = (uu___639_65424.unfold_only);
            unfold_fully = (uu___639_65424.unfold_fully);
            unfold_attr = (uu___639_65424.unfold_attr);
            unfold_tac = (uu___639_65424.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_65424.pure_subterms_within_computations);
            simplify = (uu___639_65424.simplify);
            erase_universes = (uu___639_65424.erase_universes);
            allow_unbound_universes =
              (uu___639_65424.allow_unbound_universes);
            reify_ = (uu___639_65424.reify_);
            compress_uvars = (uu___639_65424.compress_uvars);
            no_full_norm = (uu___639_65424.no_full_norm);
            check_no_uvars = (uu___639_65424.check_no_uvars);
            unmeta = (uu___639_65424.unmeta);
            unascribe = (uu___639_65424.unascribe);
            in_full_norm_request = (uu___639_65424.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_65424.weakly_reduce_scrutinee);
            nbe_step = (uu___639_65424.nbe_step);
            for_extraction = (uu___639_65424.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_65426 = fs  in
          {
            beta = (uu___643_65426.beta);
            iota = (uu___643_65426.iota);
            zeta = false;
            weak = (uu___643_65426.weak);
            hnf = (uu___643_65426.hnf);
            primops = (uu___643_65426.primops);
            do_not_unfold_pure_lets =
              (uu___643_65426.do_not_unfold_pure_lets);
            unfold_until = (uu___643_65426.unfold_until);
            unfold_only = (uu___643_65426.unfold_only);
            unfold_fully = (uu___643_65426.unfold_fully);
            unfold_attr = (uu___643_65426.unfold_attr);
            unfold_tac = (uu___643_65426.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_65426.pure_subterms_within_computations);
            simplify = (uu___643_65426.simplify);
            erase_universes = (uu___643_65426.erase_universes);
            allow_unbound_universes =
              (uu___643_65426.allow_unbound_universes);
            reify_ = (uu___643_65426.reify_);
            compress_uvars = (uu___643_65426.compress_uvars);
            no_full_norm = (uu___643_65426.no_full_norm);
            check_no_uvars = (uu___643_65426.check_no_uvars);
            unmeta = (uu___643_65426.unmeta);
            unascribe = (uu___643_65426.unascribe);
            in_full_norm_request = (uu___643_65426.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_65426.weakly_reduce_scrutinee);
            nbe_step = (uu___643_65426.nbe_step);
            for_extraction = (uu___643_65426.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____65428 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_65430 = fs  in
          {
            beta = (uu___648_65430.beta);
            iota = (uu___648_65430.iota);
            zeta = (uu___648_65430.zeta);
            weak = true;
            hnf = (uu___648_65430.hnf);
            primops = (uu___648_65430.primops);
            do_not_unfold_pure_lets =
              (uu___648_65430.do_not_unfold_pure_lets);
            unfold_until = (uu___648_65430.unfold_until);
            unfold_only = (uu___648_65430.unfold_only);
            unfold_fully = (uu___648_65430.unfold_fully);
            unfold_attr = (uu___648_65430.unfold_attr);
            unfold_tac = (uu___648_65430.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_65430.pure_subterms_within_computations);
            simplify = (uu___648_65430.simplify);
            erase_universes = (uu___648_65430.erase_universes);
            allow_unbound_universes =
              (uu___648_65430.allow_unbound_universes);
            reify_ = (uu___648_65430.reify_);
            compress_uvars = (uu___648_65430.compress_uvars);
            no_full_norm = (uu___648_65430.no_full_norm);
            check_no_uvars = (uu___648_65430.check_no_uvars);
            unmeta = (uu___648_65430.unmeta);
            unascribe = (uu___648_65430.unascribe);
            in_full_norm_request = (uu___648_65430.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_65430.weakly_reduce_scrutinee);
            nbe_step = (uu___648_65430.nbe_step);
            for_extraction = (uu___648_65430.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_65432 = fs  in
          {
            beta = (uu___651_65432.beta);
            iota = (uu___651_65432.iota);
            zeta = (uu___651_65432.zeta);
            weak = (uu___651_65432.weak);
            hnf = true;
            primops = (uu___651_65432.primops);
            do_not_unfold_pure_lets =
              (uu___651_65432.do_not_unfold_pure_lets);
            unfold_until = (uu___651_65432.unfold_until);
            unfold_only = (uu___651_65432.unfold_only);
            unfold_fully = (uu___651_65432.unfold_fully);
            unfold_attr = (uu___651_65432.unfold_attr);
            unfold_tac = (uu___651_65432.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_65432.pure_subterms_within_computations);
            simplify = (uu___651_65432.simplify);
            erase_universes = (uu___651_65432.erase_universes);
            allow_unbound_universes =
              (uu___651_65432.allow_unbound_universes);
            reify_ = (uu___651_65432.reify_);
            compress_uvars = (uu___651_65432.compress_uvars);
            no_full_norm = (uu___651_65432.no_full_norm);
            check_no_uvars = (uu___651_65432.check_no_uvars);
            unmeta = (uu___651_65432.unmeta);
            unascribe = (uu___651_65432.unascribe);
            in_full_norm_request = (uu___651_65432.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_65432.weakly_reduce_scrutinee);
            nbe_step = (uu___651_65432.nbe_step);
            for_extraction = (uu___651_65432.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_65434 = fs  in
          {
            beta = (uu___654_65434.beta);
            iota = (uu___654_65434.iota);
            zeta = (uu___654_65434.zeta);
            weak = (uu___654_65434.weak);
            hnf = (uu___654_65434.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_65434.do_not_unfold_pure_lets);
            unfold_until = (uu___654_65434.unfold_until);
            unfold_only = (uu___654_65434.unfold_only);
            unfold_fully = (uu___654_65434.unfold_fully);
            unfold_attr = (uu___654_65434.unfold_attr);
            unfold_tac = (uu___654_65434.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_65434.pure_subterms_within_computations);
            simplify = (uu___654_65434.simplify);
            erase_universes = (uu___654_65434.erase_universes);
            allow_unbound_universes =
              (uu___654_65434.allow_unbound_universes);
            reify_ = (uu___654_65434.reify_);
            compress_uvars = (uu___654_65434.compress_uvars);
            no_full_norm = (uu___654_65434.no_full_norm);
            check_no_uvars = (uu___654_65434.check_no_uvars);
            unmeta = (uu___654_65434.unmeta);
            unascribe = (uu___654_65434.unascribe);
            in_full_norm_request = (uu___654_65434.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_65434.weakly_reduce_scrutinee);
            nbe_step = (uu___654_65434.nbe_step);
            for_extraction = (uu___654_65434.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_65436 = fs  in
          {
            beta = (uu___659_65436.beta);
            iota = (uu___659_65436.iota);
            zeta = (uu___659_65436.zeta);
            weak = (uu___659_65436.weak);
            hnf = (uu___659_65436.hnf);
            primops = (uu___659_65436.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_65436.unfold_until);
            unfold_only = (uu___659_65436.unfold_only);
            unfold_fully = (uu___659_65436.unfold_fully);
            unfold_attr = (uu___659_65436.unfold_attr);
            unfold_tac = (uu___659_65436.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_65436.pure_subterms_within_computations);
            simplify = (uu___659_65436.simplify);
            erase_universes = (uu___659_65436.erase_universes);
            allow_unbound_universes =
              (uu___659_65436.allow_unbound_universes);
            reify_ = (uu___659_65436.reify_);
            compress_uvars = (uu___659_65436.compress_uvars);
            no_full_norm = (uu___659_65436.no_full_norm);
            check_no_uvars = (uu___659_65436.check_no_uvars);
            unmeta = (uu___659_65436.unmeta);
            unascribe = (uu___659_65436.unascribe);
            in_full_norm_request = (uu___659_65436.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_65436.weakly_reduce_scrutinee);
            nbe_step = (uu___659_65436.nbe_step);
            for_extraction = (uu___659_65436.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_65439 = fs  in
          {
            beta = (uu___663_65439.beta);
            iota = (uu___663_65439.iota);
            zeta = (uu___663_65439.zeta);
            weak = (uu___663_65439.weak);
            hnf = (uu___663_65439.hnf);
            primops = (uu___663_65439.primops);
            do_not_unfold_pure_lets =
              (uu___663_65439.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_65439.unfold_only);
            unfold_fully = (uu___663_65439.unfold_fully);
            unfold_attr = (uu___663_65439.unfold_attr);
            unfold_tac = (uu___663_65439.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_65439.pure_subterms_within_computations);
            simplify = (uu___663_65439.simplify);
            erase_universes = (uu___663_65439.erase_universes);
            allow_unbound_universes =
              (uu___663_65439.allow_unbound_universes);
            reify_ = (uu___663_65439.reify_);
            compress_uvars = (uu___663_65439.compress_uvars);
            no_full_norm = (uu___663_65439.no_full_norm);
            check_no_uvars = (uu___663_65439.check_no_uvars);
            unmeta = (uu___663_65439.unmeta);
            unascribe = (uu___663_65439.unascribe);
            in_full_norm_request = (uu___663_65439.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_65439.weakly_reduce_scrutinee);
            nbe_step = (uu___663_65439.nbe_step);
            for_extraction = (uu___663_65439.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_65443 = fs  in
          {
            beta = (uu___667_65443.beta);
            iota = (uu___667_65443.iota);
            zeta = (uu___667_65443.zeta);
            weak = (uu___667_65443.weak);
            hnf = (uu___667_65443.hnf);
            primops = (uu___667_65443.primops);
            do_not_unfold_pure_lets =
              (uu___667_65443.do_not_unfold_pure_lets);
            unfold_until = (uu___667_65443.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_65443.unfold_fully);
            unfold_attr = (uu___667_65443.unfold_attr);
            unfold_tac = (uu___667_65443.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_65443.pure_subterms_within_computations);
            simplify = (uu___667_65443.simplify);
            erase_universes = (uu___667_65443.erase_universes);
            allow_unbound_universes =
              (uu___667_65443.allow_unbound_universes);
            reify_ = (uu___667_65443.reify_);
            compress_uvars = (uu___667_65443.compress_uvars);
            no_full_norm = (uu___667_65443.no_full_norm);
            check_no_uvars = (uu___667_65443.check_no_uvars);
            unmeta = (uu___667_65443.unmeta);
            unascribe = (uu___667_65443.unascribe);
            in_full_norm_request = (uu___667_65443.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_65443.weakly_reduce_scrutinee);
            nbe_step = (uu___667_65443.nbe_step);
            for_extraction = (uu___667_65443.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_65449 = fs  in
          {
            beta = (uu___671_65449.beta);
            iota = (uu___671_65449.iota);
            zeta = (uu___671_65449.zeta);
            weak = (uu___671_65449.weak);
            hnf = (uu___671_65449.hnf);
            primops = (uu___671_65449.primops);
            do_not_unfold_pure_lets =
              (uu___671_65449.do_not_unfold_pure_lets);
            unfold_until = (uu___671_65449.unfold_until);
            unfold_only = (uu___671_65449.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_65449.unfold_attr);
            unfold_tac = (uu___671_65449.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_65449.pure_subterms_within_computations);
            simplify = (uu___671_65449.simplify);
            erase_universes = (uu___671_65449.erase_universes);
            allow_unbound_universes =
              (uu___671_65449.allow_unbound_universes);
            reify_ = (uu___671_65449.reify_);
            compress_uvars = (uu___671_65449.compress_uvars);
            no_full_norm = (uu___671_65449.no_full_norm);
            check_no_uvars = (uu___671_65449.check_no_uvars);
            unmeta = (uu___671_65449.unmeta);
            unascribe = (uu___671_65449.unascribe);
            in_full_norm_request = (uu___671_65449.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_65449.weakly_reduce_scrutinee);
            nbe_step = (uu___671_65449.nbe_step);
            for_extraction = (uu___671_65449.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_65455 = fs  in
          {
            beta = (uu___675_65455.beta);
            iota = (uu___675_65455.iota);
            zeta = (uu___675_65455.zeta);
            weak = (uu___675_65455.weak);
            hnf = (uu___675_65455.hnf);
            primops = (uu___675_65455.primops);
            do_not_unfold_pure_lets =
              (uu___675_65455.do_not_unfold_pure_lets);
            unfold_until = (uu___675_65455.unfold_until);
            unfold_only = (uu___675_65455.unfold_only);
            unfold_fully = (uu___675_65455.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_65455.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_65455.pure_subterms_within_computations);
            simplify = (uu___675_65455.simplify);
            erase_universes = (uu___675_65455.erase_universes);
            allow_unbound_universes =
              (uu___675_65455.allow_unbound_universes);
            reify_ = (uu___675_65455.reify_);
            compress_uvars = (uu___675_65455.compress_uvars);
            no_full_norm = (uu___675_65455.no_full_norm);
            check_no_uvars = (uu___675_65455.check_no_uvars);
            unmeta = (uu___675_65455.unmeta);
            unascribe = (uu___675_65455.unascribe);
            in_full_norm_request = (uu___675_65455.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_65455.weakly_reduce_scrutinee);
            nbe_step = (uu___675_65455.nbe_step);
            for_extraction = (uu___675_65455.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_65458 = fs  in
          {
            beta = (uu___678_65458.beta);
            iota = (uu___678_65458.iota);
            zeta = (uu___678_65458.zeta);
            weak = (uu___678_65458.weak);
            hnf = (uu___678_65458.hnf);
            primops = (uu___678_65458.primops);
            do_not_unfold_pure_lets =
              (uu___678_65458.do_not_unfold_pure_lets);
            unfold_until = (uu___678_65458.unfold_until);
            unfold_only = (uu___678_65458.unfold_only);
            unfold_fully = (uu___678_65458.unfold_fully);
            unfold_attr = (uu___678_65458.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_65458.pure_subterms_within_computations);
            simplify = (uu___678_65458.simplify);
            erase_universes = (uu___678_65458.erase_universes);
            allow_unbound_universes =
              (uu___678_65458.allow_unbound_universes);
            reify_ = (uu___678_65458.reify_);
            compress_uvars = (uu___678_65458.compress_uvars);
            no_full_norm = (uu___678_65458.no_full_norm);
            check_no_uvars = (uu___678_65458.check_no_uvars);
            unmeta = (uu___678_65458.unmeta);
            unascribe = (uu___678_65458.unascribe);
            in_full_norm_request = (uu___678_65458.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_65458.weakly_reduce_scrutinee);
            nbe_step = (uu___678_65458.nbe_step);
            for_extraction = (uu___678_65458.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_65460 = fs  in
          {
            beta = (uu___681_65460.beta);
            iota = (uu___681_65460.iota);
            zeta = (uu___681_65460.zeta);
            weak = (uu___681_65460.weak);
            hnf = (uu___681_65460.hnf);
            primops = (uu___681_65460.primops);
            do_not_unfold_pure_lets =
              (uu___681_65460.do_not_unfold_pure_lets);
            unfold_until = (uu___681_65460.unfold_until);
            unfold_only = (uu___681_65460.unfold_only);
            unfold_fully = (uu___681_65460.unfold_fully);
            unfold_attr = (uu___681_65460.unfold_attr);
            unfold_tac = (uu___681_65460.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_65460.simplify);
            erase_universes = (uu___681_65460.erase_universes);
            allow_unbound_universes =
              (uu___681_65460.allow_unbound_universes);
            reify_ = (uu___681_65460.reify_);
            compress_uvars = (uu___681_65460.compress_uvars);
            no_full_norm = (uu___681_65460.no_full_norm);
            check_no_uvars = (uu___681_65460.check_no_uvars);
            unmeta = (uu___681_65460.unmeta);
            unascribe = (uu___681_65460.unascribe);
            in_full_norm_request = (uu___681_65460.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_65460.weakly_reduce_scrutinee);
            nbe_step = (uu___681_65460.nbe_step);
            for_extraction = (uu___681_65460.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_65462 = fs  in
          {
            beta = (uu___684_65462.beta);
            iota = (uu___684_65462.iota);
            zeta = (uu___684_65462.zeta);
            weak = (uu___684_65462.weak);
            hnf = (uu___684_65462.hnf);
            primops = (uu___684_65462.primops);
            do_not_unfold_pure_lets =
              (uu___684_65462.do_not_unfold_pure_lets);
            unfold_until = (uu___684_65462.unfold_until);
            unfold_only = (uu___684_65462.unfold_only);
            unfold_fully = (uu___684_65462.unfold_fully);
            unfold_attr = (uu___684_65462.unfold_attr);
            unfold_tac = (uu___684_65462.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_65462.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_65462.erase_universes);
            allow_unbound_universes =
              (uu___684_65462.allow_unbound_universes);
            reify_ = (uu___684_65462.reify_);
            compress_uvars = (uu___684_65462.compress_uvars);
            no_full_norm = (uu___684_65462.no_full_norm);
            check_no_uvars = (uu___684_65462.check_no_uvars);
            unmeta = (uu___684_65462.unmeta);
            unascribe = (uu___684_65462.unascribe);
            in_full_norm_request = (uu___684_65462.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_65462.weakly_reduce_scrutinee);
            nbe_step = (uu___684_65462.nbe_step);
            for_extraction = (uu___684_65462.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_65464 = fs  in
          {
            beta = (uu___687_65464.beta);
            iota = (uu___687_65464.iota);
            zeta = (uu___687_65464.zeta);
            weak = (uu___687_65464.weak);
            hnf = (uu___687_65464.hnf);
            primops = (uu___687_65464.primops);
            do_not_unfold_pure_lets =
              (uu___687_65464.do_not_unfold_pure_lets);
            unfold_until = (uu___687_65464.unfold_until);
            unfold_only = (uu___687_65464.unfold_only);
            unfold_fully = (uu___687_65464.unfold_fully);
            unfold_attr = (uu___687_65464.unfold_attr);
            unfold_tac = (uu___687_65464.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_65464.pure_subterms_within_computations);
            simplify = (uu___687_65464.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_65464.allow_unbound_universes);
            reify_ = (uu___687_65464.reify_);
            compress_uvars = (uu___687_65464.compress_uvars);
            no_full_norm = (uu___687_65464.no_full_norm);
            check_no_uvars = (uu___687_65464.check_no_uvars);
            unmeta = (uu___687_65464.unmeta);
            unascribe = (uu___687_65464.unascribe);
            in_full_norm_request = (uu___687_65464.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_65464.weakly_reduce_scrutinee);
            nbe_step = (uu___687_65464.nbe_step);
            for_extraction = (uu___687_65464.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_65466 = fs  in
          {
            beta = (uu___690_65466.beta);
            iota = (uu___690_65466.iota);
            zeta = (uu___690_65466.zeta);
            weak = (uu___690_65466.weak);
            hnf = (uu___690_65466.hnf);
            primops = (uu___690_65466.primops);
            do_not_unfold_pure_lets =
              (uu___690_65466.do_not_unfold_pure_lets);
            unfold_until = (uu___690_65466.unfold_until);
            unfold_only = (uu___690_65466.unfold_only);
            unfold_fully = (uu___690_65466.unfold_fully);
            unfold_attr = (uu___690_65466.unfold_attr);
            unfold_tac = (uu___690_65466.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_65466.pure_subterms_within_computations);
            simplify = (uu___690_65466.simplify);
            erase_universes = (uu___690_65466.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_65466.reify_);
            compress_uvars = (uu___690_65466.compress_uvars);
            no_full_norm = (uu___690_65466.no_full_norm);
            check_no_uvars = (uu___690_65466.check_no_uvars);
            unmeta = (uu___690_65466.unmeta);
            unascribe = (uu___690_65466.unascribe);
            in_full_norm_request = (uu___690_65466.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_65466.weakly_reduce_scrutinee);
            nbe_step = (uu___690_65466.nbe_step);
            for_extraction = (uu___690_65466.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_65468 = fs  in
          {
            beta = (uu___693_65468.beta);
            iota = (uu___693_65468.iota);
            zeta = (uu___693_65468.zeta);
            weak = (uu___693_65468.weak);
            hnf = (uu___693_65468.hnf);
            primops = (uu___693_65468.primops);
            do_not_unfold_pure_lets =
              (uu___693_65468.do_not_unfold_pure_lets);
            unfold_until = (uu___693_65468.unfold_until);
            unfold_only = (uu___693_65468.unfold_only);
            unfold_fully = (uu___693_65468.unfold_fully);
            unfold_attr = (uu___693_65468.unfold_attr);
            unfold_tac = (uu___693_65468.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_65468.pure_subterms_within_computations);
            simplify = (uu___693_65468.simplify);
            erase_universes = (uu___693_65468.erase_universes);
            allow_unbound_universes =
              (uu___693_65468.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_65468.compress_uvars);
            no_full_norm = (uu___693_65468.no_full_norm);
            check_no_uvars = (uu___693_65468.check_no_uvars);
            unmeta = (uu___693_65468.unmeta);
            unascribe = (uu___693_65468.unascribe);
            in_full_norm_request = (uu___693_65468.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_65468.weakly_reduce_scrutinee);
            nbe_step = (uu___693_65468.nbe_step);
            for_extraction = (uu___693_65468.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_65470 = fs  in
          {
            beta = (uu___696_65470.beta);
            iota = (uu___696_65470.iota);
            zeta = (uu___696_65470.zeta);
            weak = (uu___696_65470.weak);
            hnf = (uu___696_65470.hnf);
            primops = (uu___696_65470.primops);
            do_not_unfold_pure_lets =
              (uu___696_65470.do_not_unfold_pure_lets);
            unfold_until = (uu___696_65470.unfold_until);
            unfold_only = (uu___696_65470.unfold_only);
            unfold_fully = (uu___696_65470.unfold_fully);
            unfold_attr = (uu___696_65470.unfold_attr);
            unfold_tac = (uu___696_65470.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_65470.pure_subterms_within_computations);
            simplify = (uu___696_65470.simplify);
            erase_universes = (uu___696_65470.erase_universes);
            allow_unbound_universes =
              (uu___696_65470.allow_unbound_universes);
            reify_ = (uu___696_65470.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_65470.no_full_norm);
            check_no_uvars = (uu___696_65470.check_no_uvars);
            unmeta = (uu___696_65470.unmeta);
            unascribe = (uu___696_65470.unascribe);
            in_full_norm_request = (uu___696_65470.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_65470.weakly_reduce_scrutinee);
            nbe_step = (uu___696_65470.nbe_step);
            for_extraction = (uu___696_65470.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_65472 = fs  in
          {
            beta = (uu___699_65472.beta);
            iota = (uu___699_65472.iota);
            zeta = (uu___699_65472.zeta);
            weak = (uu___699_65472.weak);
            hnf = (uu___699_65472.hnf);
            primops = (uu___699_65472.primops);
            do_not_unfold_pure_lets =
              (uu___699_65472.do_not_unfold_pure_lets);
            unfold_until = (uu___699_65472.unfold_until);
            unfold_only = (uu___699_65472.unfold_only);
            unfold_fully = (uu___699_65472.unfold_fully);
            unfold_attr = (uu___699_65472.unfold_attr);
            unfold_tac = (uu___699_65472.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_65472.pure_subterms_within_computations);
            simplify = (uu___699_65472.simplify);
            erase_universes = (uu___699_65472.erase_universes);
            allow_unbound_universes =
              (uu___699_65472.allow_unbound_universes);
            reify_ = (uu___699_65472.reify_);
            compress_uvars = (uu___699_65472.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_65472.check_no_uvars);
            unmeta = (uu___699_65472.unmeta);
            unascribe = (uu___699_65472.unascribe);
            in_full_norm_request = (uu___699_65472.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_65472.weakly_reduce_scrutinee);
            nbe_step = (uu___699_65472.nbe_step);
            for_extraction = (uu___699_65472.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_65474 = fs  in
          {
            beta = (uu___702_65474.beta);
            iota = (uu___702_65474.iota);
            zeta = (uu___702_65474.zeta);
            weak = (uu___702_65474.weak);
            hnf = (uu___702_65474.hnf);
            primops = (uu___702_65474.primops);
            do_not_unfold_pure_lets =
              (uu___702_65474.do_not_unfold_pure_lets);
            unfold_until = (uu___702_65474.unfold_until);
            unfold_only = (uu___702_65474.unfold_only);
            unfold_fully = (uu___702_65474.unfold_fully);
            unfold_attr = (uu___702_65474.unfold_attr);
            unfold_tac = (uu___702_65474.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_65474.pure_subterms_within_computations);
            simplify = (uu___702_65474.simplify);
            erase_universes = (uu___702_65474.erase_universes);
            allow_unbound_universes =
              (uu___702_65474.allow_unbound_universes);
            reify_ = (uu___702_65474.reify_);
            compress_uvars = (uu___702_65474.compress_uvars);
            no_full_norm = (uu___702_65474.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_65474.unmeta);
            unascribe = (uu___702_65474.unascribe);
            in_full_norm_request = (uu___702_65474.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_65474.weakly_reduce_scrutinee);
            nbe_step = (uu___702_65474.nbe_step);
            for_extraction = (uu___702_65474.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_65476 = fs  in
          {
            beta = (uu___705_65476.beta);
            iota = (uu___705_65476.iota);
            zeta = (uu___705_65476.zeta);
            weak = (uu___705_65476.weak);
            hnf = (uu___705_65476.hnf);
            primops = (uu___705_65476.primops);
            do_not_unfold_pure_lets =
              (uu___705_65476.do_not_unfold_pure_lets);
            unfold_until = (uu___705_65476.unfold_until);
            unfold_only = (uu___705_65476.unfold_only);
            unfold_fully = (uu___705_65476.unfold_fully);
            unfold_attr = (uu___705_65476.unfold_attr);
            unfold_tac = (uu___705_65476.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_65476.pure_subterms_within_computations);
            simplify = (uu___705_65476.simplify);
            erase_universes = (uu___705_65476.erase_universes);
            allow_unbound_universes =
              (uu___705_65476.allow_unbound_universes);
            reify_ = (uu___705_65476.reify_);
            compress_uvars = (uu___705_65476.compress_uvars);
            no_full_norm = (uu___705_65476.no_full_norm);
            check_no_uvars = (uu___705_65476.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_65476.unascribe);
            in_full_norm_request = (uu___705_65476.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_65476.weakly_reduce_scrutinee);
            nbe_step = (uu___705_65476.nbe_step);
            for_extraction = (uu___705_65476.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_65478 = fs  in
          {
            beta = (uu___708_65478.beta);
            iota = (uu___708_65478.iota);
            zeta = (uu___708_65478.zeta);
            weak = (uu___708_65478.weak);
            hnf = (uu___708_65478.hnf);
            primops = (uu___708_65478.primops);
            do_not_unfold_pure_lets =
              (uu___708_65478.do_not_unfold_pure_lets);
            unfold_until = (uu___708_65478.unfold_until);
            unfold_only = (uu___708_65478.unfold_only);
            unfold_fully = (uu___708_65478.unfold_fully);
            unfold_attr = (uu___708_65478.unfold_attr);
            unfold_tac = (uu___708_65478.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_65478.pure_subterms_within_computations);
            simplify = (uu___708_65478.simplify);
            erase_universes = (uu___708_65478.erase_universes);
            allow_unbound_universes =
              (uu___708_65478.allow_unbound_universes);
            reify_ = (uu___708_65478.reify_);
            compress_uvars = (uu___708_65478.compress_uvars);
            no_full_norm = (uu___708_65478.no_full_norm);
            check_no_uvars = (uu___708_65478.check_no_uvars);
            unmeta = (uu___708_65478.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_65478.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_65478.weakly_reduce_scrutinee);
            nbe_step = (uu___708_65478.nbe_step);
            for_extraction = (uu___708_65478.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_65480 = fs  in
          {
            beta = (uu___711_65480.beta);
            iota = (uu___711_65480.iota);
            zeta = (uu___711_65480.zeta);
            weak = (uu___711_65480.weak);
            hnf = (uu___711_65480.hnf);
            primops = (uu___711_65480.primops);
            do_not_unfold_pure_lets =
              (uu___711_65480.do_not_unfold_pure_lets);
            unfold_until = (uu___711_65480.unfold_until);
            unfold_only = (uu___711_65480.unfold_only);
            unfold_fully = (uu___711_65480.unfold_fully);
            unfold_attr = (uu___711_65480.unfold_attr);
            unfold_tac = (uu___711_65480.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_65480.pure_subterms_within_computations);
            simplify = (uu___711_65480.simplify);
            erase_universes = (uu___711_65480.erase_universes);
            allow_unbound_universes =
              (uu___711_65480.allow_unbound_universes);
            reify_ = (uu___711_65480.reify_);
            compress_uvars = (uu___711_65480.compress_uvars);
            no_full_norm = (uu___711_65480.no_full_norm);
            check_no_uvars = (uu___711_65480.check_no_uvars);
            unmeta = (uu___711_65480.unmeta);
            unascribe = (uu___711_65480.unascribe);
            in_full_norm_request = (uu___711_65480.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_65480.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_65480.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_65482 = fs  in
          {
            beta = (uu___714_65482.beta);
            iota = (uu___714_65482.iota);
            zeta = (uu___714_65482.zeta);
            weak = (uu___714_65482.weak);
            hnf = (uu___714_65482.hnf);
            primops = (uu___714_65482.primops);
            do_not_unfold_pure_lets =
              (uu___714_65482.do_not_unfold_pure_lets);
            unfold_until = (uu___714_65482.unfold_until);
            unfold_only = (uu___714_65482.unfold_only);
            unfold_fully = (uu___714_65482.unfold_fully);
            unfold_attr = (uu___714_65482.unfold_attr);
            unfold_tac = (uu___714_65482.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_65482.pure_subterms_within_computations);
            simplify = (uu___714_65482.simplify);
            erase_universes = (uu___714_65482.erase_universes);
            allow_unbound_universes =
              (uu___714_65482.allow_unbound_universes);
            reify_ = (uu___714_65482.reify_);
            compress_uvars = (uu___714_65482.compress_uvars);
            no_full_norm = (uu___714_65482.no_full_norm);
            check_no_uvars = (uu___714_65482.check_no_uvars);
            unmeta = (uu___714_65482.unmeta);
            unascribe = (uu___714_65482.unascribe);
            in_full_norm_request = (uu___714_65482.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_65482.weakly_reduce_scrutinee);
            nbe_step = (uu___714_65482.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____65540  -> [])
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
    let uu____66600 =
      let uu____66604 =
        let uu____66608 =
          let uu____66610 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____66610  in
        [uu____66608; "}"]  in
      "{" :: uu____66604  in
    FStar_String.concat "\n" uu____66600
  
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
             let uu____66658 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____66658 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____66674 = FStar_Util.psmap_empty ()  in add_steps uu____66674 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____66690 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____66690
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____66704 =
        let uu____66707 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____66707  in
      FStar_Util.is_some uu____66704
  
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
      let uu____66820 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____66820 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____66856 = FStar_Syntax_Embeddings.embed emb x  in
        uu____66856 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____66912 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____66912 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____66931 .
    'Auu____66931 ->
      FStar_Range.range -> 'Auu____66931 FStar_Syntax_Syntax.syntax
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
    let uu____67052 =
      let uu____67061 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____67061  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____67052  in
  let arg_as_bounded_int1 uu____67091 =
    match uu____67091 with
    | (a,uu____67105) ->
        let uu____67116 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____67116 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____67160 =
               let uu____67175 =
                 let uu____67176 = FStar_Syntax_Subst.compress hd1  in
                 uu____67176.FStar_Syntax_Syntax.n  in
               (uu____67175, args)  in
             (match uu____67160 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____67197)::[]) when
                  let uu____67232 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____67232 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____67236 =
                    let uu____67237 = FStar_Syntax_Subst.compress arg1  in
                    uu____67237.FStar_Syntax_Syntax.n  in
                  (match uu____67236 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____67259 =
                         let uu____67264 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____67264)  in
                       FStar_Pervasives_Native.Some uu____67259
                   | uu____67269 -> FStar_Pervasives_Native.None)
              | uu____67274 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____67336 = f a  in FStar_Pervasives_Native.Some uu____67336
    | uu____67337 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____67393 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____67393
    | uu____67394 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____67463 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____67463  in
  let binary_op1 as_a f res n1 args =
    let uu____67547 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____67547  in
  let as_primitive_step is_strong uu____67603 =
    match uu____67603 with
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
           let uu____67715 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____67715)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67758 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____67758)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____67800 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____67800)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67854 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____67854)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67908 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____67908)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____68063 =
          let uu____68072 = as_a a  in
          let uu____68075 = as_b b  in (uu____68072, uu____68075)  in
        (match uu____68063 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____68090 =
               let uu____68091 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____68091  in
             FStar_Pervasives_Native.Some uu____68090
         | uu____68092 -> FStar_Pervasives_Native.None)
    | uu____68101 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____68123 =
        let uu____68124 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____68124  in
      mk uu____68123 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____68138 =
      let uu____68141 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____68141  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____68138
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____68189 =
      let uu____68190 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____68190  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____68189  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____68278 = arg_as_string1 a1  in
        (match uu____68278 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68287 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____68287 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____68305 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____68305
              | uu____68307 -> FStar_Pervasives_Native.None)
         | uu____68313 -> FStar_Pervasives_Native.None)
    | uu____68317 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68400 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____68400 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68416 = arg_as_string1 a2  in
             (match uu____68416 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68429 =
                    let uu____68430 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____68430 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____68429
              | uu____68440 -> FStar_Pervasives_Native.None)
         | uu____68444 -> FStar_Pervasives_Native.None)
    | uu____68450 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____68490 =
          let uu____68504 = arg_as_string1 a1  in
          let uu____68508 = arg_as_int1 a2  in
          let uu____68511 = arg_as_int1 a3  in
          (uu____68504, uu____68508, uu____68511)  in
        (match uu____68490 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_68544  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68549 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68549) ()
              with | uu___1030_68552 -> FStar_Pervasives_Native.None)
         | uu____68555 -> FStar_Pervasives_Native.None)
    | uu____68569 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____68583 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____68583  in
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
        let uu____68664 =
          let uu____68674 = arg_as_string1 a1  in
          let uu____68678 = arg_as_int1 a2  in (uu____68674, uu____68678)  in
        (match uu____68664 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_68702  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68707 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68707) ()
              with | uu___1064_68710 -> FStar_Pervasives_Native.None)
         | uu____68713 -> FStar_Pervasives_Native.None)
    | uu____68723 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68756 =
          let uu____68767 = arg_as_string1 a1  in
          let uu____68771 = arg_as_char1 a2  in (uu____68767, uu____68771)
           in
        (match uu____68756 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_68800  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68804 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68804) ()
              with | uu___1085_68806 -> FStar_Pervasives_Native.None)
         | uu____68809 -> FStar_Pervasives_Native.None)
    | uu____68820 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68856 =
          let uu____68878 = arg_as_string1 fn  in
          let uu____68882 = arg_as_int1 from_line  in
          let uu____68885 = arg_as_int1 from_col  in
          let uu____68888 = arg_as_int1 to_line  in
          let uu____68891 = arg_as_int1 to_col  in
          (uu____68878, uu____68882, uu____68885, uu____68888, uu____68891)
           in
        (match uu____68856 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68926 =
                 let uu____68927 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68929 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68927 uu____68929  in
               let uu____68931 =
                 let uu____68932 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68934 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68932 uu____68934  in
               FStar_Range.mk_range fn1 uu____68926 uu____68931  in
             let uu____68936 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____68936
         | uu____68937 -> FStar_Pervasives_Native.None)
    | uu____68959 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____69005)::(a1,uu____69007)::(a2,uu____69009)::[] ->
        let uu____69066 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____69066 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____69075 -> FStar_Pervasives_Native.None)
    | uu____69076 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____69121)::[] ->
        let uu____69138 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____69138 with
         | FStar_Pervasives_Native.Some r ->
             let uu____69144 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____69144
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____69145 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____69165  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____69200 =
      let uu____69231 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____69231)
       in
    let uu____69266 =
      let uu____69299 =
        let uu____69330 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____69330)
         in
      let uu____69371 =
        let uu____69404 =
          let uu____69435 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____69435)
           in
        let uu____69476 =
          let uu____69509 =
            let uu____69540 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____69540)
             in
          let uu____69581 =
            let uu____69614 =
              let uu____69645 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____69645)
               in
            let uu____69686 =
              let uu____69719 =
                let uu____69750 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____69762 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____69762)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____69794 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____69794)), uu____69750)
                 in
              let uu____69797 =
                let uu____69830 =
                  let uu____69861 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____69873 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____69873)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____69905 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____69905)), uu____69861)
                   in
                let uu____69908 =
                  let uu____69941 =
                    let uu____69972 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____69984 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____69984)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____70016 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____70016)), uu____69972)
                     in
                  let uu____70019 =
                    let uu____70052 =
                      let uu____70083 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____70095 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____70095)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____70127 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____70127)), uu____70083)
                       in
                    let uu____70130 =
                      let uu____70163 =
                        let uu____70194 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____70194)
                         in
                      let uu____70235 =
                        let uu____70268 =
                          let uu____70299 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____70299)
                           in
                        let uu____70336 =
                          let uu____70369 =
                            let uu____70400 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____70400)
                             in
                          let uu____70445 =
                            let uu____70478 =
                              let uu____70509 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____70509)
                               in
                            let uu____70554 =
                              let uu____70587 =
                                let uu____70618 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____70618)
                                 in
                              let uu____70647 =
                                let uu____70680 =
                                  let uu____70711 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____70711)
                                   in
                                let uu____70742 =
                                  let uu____70775 =
                                    let uu____70806 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____70806)
                                     in
                                  let uu____70837 =
                                    let uu____70870 =
                                      let uu____70901 =
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
                                           string_of_list'1), uu____70901)
                                       in
                                    let uu____70938 =
                                      let uu____70971 =
                                        let uu____71004 =
                                          let uu____71037 =
                                            let uu____71068 =
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
                                              uu____71068)
                                             in
                                          let uu____71113 =
                                            let uu____71146 =
                                              let uu____71179 =
                                                let uu____71210 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____71210)
                                                 in
                                              let uu____71241 =
                                                let uu____71274 =
                                                  let uu____71305 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____71305)
                                                   in
                                                let uu____71336 =
                                                  let uu____71369 =
                                                    let uu____71400 =
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
                                                      uu____71400)
                                                     in
                                                  let uu____71431 =
                                                    let uu____71464 =
                                                      let uu____71497 =
                                                        let uu____71530 =
                                                          let uu____71563 =
                                                            let uu____71596 =
                                                              let uu____71629
                                                                =
                                                                let uu____71660
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____71660,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____71688
                                                                =
                                                                let uu____71721
                                                                  =
                                                                  let uu____71752
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____71752,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____71721]
                                                                 in
                                                              uu____71629 ::
                                                                uu____71688
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____71596
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____71563
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____71530
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____71497
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____71464
                                                     in
                                                  uu____71369 :: uu____71431
                                                   in
                                                uu____71274 :: uu____71336
                                                 in
                                              uu____71179 :: uu____71241  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____71146
                                             in
                                          uu____71037 :: uu____71113  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____71004
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
                                                  let uu____72423 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____72423 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____72434 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____72434
                                                  y)))
                                        :: uu____70971
                                       in
                                    uu____70870 :: uu____70938  in
                                  uu____70775 :: uu____70837  in
                                uu____70680 :: uu____70742  in
                              uu____70587 :: uu____70647  in
                            uu____70478 :: uu____70554  in
                          uu____70369 :: uu____70445  in
                        uu____70268 :: uu____70336  in
                      uu____70163 :: uu____70235  in
                    uu____70052 :: uu____70130  in
                  uu____69941 :: uu____70019  in
                uu____69830 :: uu____69908  in
              uu____69719 :: uu____69797  in
            uu____69614 :: uu____69686  in
          uu____69509 :: uu____69581  in
        uu____69404 :: uu____69476  in
      uu____69299 :: uu____69371  in
    uu____69200 :: uu____69266  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____73090 =
        let uu____73095 =
          let uu____73096 = FStar_Syntax_Syntax.as_arg c  in [uu____73096]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____73095  in
      uu____73090 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____73228 =
                let uu____73259 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____73266 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____73284  ->
                       fun uu____73285  ->
                         match (uu____73284, uu____73285) with
                         | ((int_to_t1,x),(uu____73304,y)) ->
                             let uu____73314 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____73314)
                   in
                (uu____73259, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____73350  ->
                          fun uu____73351  ->
                            match (uu____73350, uu____73351) with
                            | ((int_to_t1,x),(uu____73370,y)) ->
                                let uu____73380 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____73380)),
                  uu____73266)
                 in
              let uu____73381 =
                let uu____73414 =
                  let uu____73445 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____73452 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____73470  ->
                         fun uu____73471  ->
                           match (uu____73470, uu____73471) with
                           | ((int_to_t1,x),(uu____73490,y)) ->
                               let uu____73500 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____73500)
                     in
                  (uu____73445, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____73536  ->
                            fun uu____73537  ->
                              match (uu____73536, uu____73537) with
                              | ((int_to_t1,x),(uu____73556,y)) ->
                                  let uu____73566 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____73566)),
                    uu____73452)
                   in
                let uu____73567 =
                  let uu____73600 =
                    let uu____73631 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____73638 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____73656  ->
                           fun uu____73657  ->
                             match (uu____73656, uu____73657) with
                             | ((int_to_t1,x),(uu____73676,y)) ->
                                 let uu____73686 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____73686)
                       in
                    (uu____73631, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____73722  ->
                              fun uu____73723  ->
                                match (uu____73722, uu____73723) with
                                | ((int_to_t1,x),(uu____73742,y)) ->
                                    let uu____73752 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____73752)),
                      uu____73638)
                     in
                  let uu____73753 =
                    let uu____73786 =
                      let uu____73817 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____73824 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____73838  ->
                             match uu____73838 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____73817, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____73876  ->
                                match uu____73876 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____73824)
                       in
                    [uu____73786]  in
                  uu____73600 :: uu____73753  in
                uu____73414 :: uu____73567  in
              uu____73228 :: uu____73381))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74137 =
                let uu____74168 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____74175 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74193  ->
                       fun uu____74194  ->
                         match (uu____74193, uu____74194) with
                         | ((int_to_t1,x),(uu____74213,y)) ->
                             let uu____74223 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74223)
                   in
                (uu____74168, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74259  ->
                          fun uu____74260  ->
                            match (uu____74259, uu____74260) with
                            | ((int_to_t1,x),(uu____74279,y)) ->
                                let uu____74289 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74289)),
                  uu____74175)
                 in
              let uu____74290 =
                let uu____74323 =
                  let uu____74354 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____74361 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____74379  ->
                         fun uu____74380  ->
                           match (uu____74379, uu____74380) with
                           | ((int_to_t1,x),(uu____74399,y)) ->
                               let uu____74409 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____74409)
                     in
                  (uu____74354, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____74445  ->
                            fun uu____74446  ->
                              match (uu____74445, uu____74446) with
                              | ((int_to_t1,x),(uu____74465,y)) ->
                                  let uu____74475 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____74475)),
                    uu____74361)
                   in
                [uu____74323]  in
              uu____74137 :: uu____74290))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____74584 ->
          let uu____74586 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____74586
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74693 =
                let uu____74724 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____74731 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74749  ->
                       fun uu____74750  ->
                         match (uu____74749, uu____74750) with
                         | ((int_to_t1,x),(uu____74769,y)) ->
                             let uu____74779 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74779)
                   in
                (uu____74724, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74815  ->
                          fun uu____74816  ->
                            match (uu____74815, uu____74816) with
                            | ((int_to_t1,x),(uu____74835,y)) ->
                                let uu____74845 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74845)),
                  uu____74731)
                 in
              let uu____74846 =
                let uu____74879 =
                  let uu____74910 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____74917 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____74935  ->
                         fun uu____74936  ->
                           match (uu____74935, uu____74936) with
                           | ((int_to_t1,x),(uu____74955,y)) ->
                               let uu____74965 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____74965)
                     in
                  (uu____74910, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____75001  ->
                            fun uu____75002  ->
                              match (uu____75001, uu____75002) with
                              | ((int_to_t1,x),(uu____75021,y)) ->
                                  let uu____75031 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____75031)),
                    uu____74917)
                   in
                let uu____75032 =
                  let uu____75065 =
                    let uu____75096 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____75103 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____75121  ->
                           fun uu____75122  ->
                             match (uu____75121, uu____75122) with
                             | ((int_to_t1,x),(uu____75141,y)) ->
                                 let uu____75151 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75151)
                       in
                    (uu____75096, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____75187  ->
                              fun uu____75188  ->
                                match (uu____75187, uu____75188) with
                                | ((int_to_t1,x),(uu____75207,y)) ->
                                    let uu____75217 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____75217)),
                      uu____75103)
                     in
                  let uu____75218 =
                    let uu____75251 =
                      let uu____75282 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____75289 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____75304  ->
                             match uu____75304 with
                             | (int_to_t1,x) ->
                                 let uu____75311 =
                                   let uu____75312 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____75313 = mask m  in
                                   FStar_BigInt.logand_big_int uu____75312
                                     uu____75313
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75311)
                         in
                      (uu____75282, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____75346  ->
                                match uu____75346 with
                                | (int_to_t1,x) ->
                                    let uu____75353 =
                                      let uu____75354 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____75355 = mask m  in
                                      FStar_BigInt.logand_big_int uu____75354
                                        uu____75355
                                       in
                                    int_as_bounded1 r int_to_t1 uu____75353)),
                        uu____75289)
                       in
                    let uu____75356 =
                      let uu____75389 =
                        let uu____75420 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____75427 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____75445  ->
                               fun uu____75446  ->
                                 match (uu____75445, uu____75446) with
                                 | ((int_to_t1,x),(uu____75465,y)) ->
                                     let uu____75475 =
                                       let uu____75476 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____75477 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____75476 uu____75477
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____75475)
                           in
                        (uu____75420, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____75513  ->
                                  fun uu____75514  ->
                                    match (uu____75513, uu____75514) with
                                    | ((int_to_t1,x),(uu____75533,y)) ->
                                        let uu____75543 =
                                          let uu____75544 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____75545 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____75544 uu____75545
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____75543)), uu____75427)
                         in
                      let uu____75546 =
                        let uu____75579 =
                          let uu____75610 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____75617 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____75635  ->
                                 fun uu____75636  ->
                                   match (uu____75635, uu____75636) with
                                   | ((int_to_t1,x),(uu____75655,y)) ->
                                       let uu____75665 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____75665)
                             in
                          (uu____75610, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____75701  ->
                                    fun uu____75702  ->
                                      match (uu____75701, uu____75702) with
                                      | ((int_to_t1,x),(uu____75721,y)) ->
                                          let uu____75731 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____75731)), uu____75617)
                           in
                        [uu____75579]  in
                      uu____75389 :: uu____75546  in
                    uu____75251 :: uu____75356  in
                  uu____75065 :: uu____75218  in
                uu____74879 :: uu____75032  in
              uu____74693 :: uu____74846))
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
    | (_typ,uu____76137)::(a1,uu____76139)::(a2,uu____76141)::[] ->
        let uu____76198 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____76198 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1406_76202 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1406_76202.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1406_76202.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1409_76204 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1409_76204.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1409_76204.FStar_Syntax_Syntax.vars)
                })
         | uu____76205 -> FStar_Pervasives_Native.None)
    | uu____76206 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____76238)::(t2,uu____76240)::(a1,uu____76242)::(a2,uu____76244)::[]
        ->
        let uu____76317 =
          let uu____76318 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____76319 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____76318 uu____76319  in
        (match uu____76317 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1432_76323 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1432_76323.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1432_76323.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1435_76325 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1435_76325.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1435_76325.FStar_Syntax_Syntax.vars)
                })
         | uu____76326 -> FStar_Pervasives_Native.None)
    | uu____76327 -> failwith "Unexpected number of arguments"  in
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
  fun uu____76358  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____76375 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____76375 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____76404 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____76404 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____76415  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____76486  ->
           fun uu____76487  ->
             match (uu____76486, uu____76487) with
             | ((uu____76513,t1),(uu____76515,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____76549  ->
         fun rest  ->
           match uu____76549 with
           | (nm,ms) ->
               let uu____76565 =
                 let uu____76567 =
                   let uu____76569 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____76569  in
                 FStar_Util.format2 "%sms --- %s\n" uu____76567 nm  in
               FStar_String.op_Hat uu____76565 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____76600 =
      let uu____76603 = FStar_ST.op_Bang plugins  in p :: uu____76603  in
    FStar_ST.op_Colon_Equals plugins uu____76600  in
  let retrieve uu____76703 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____76778  ->
    let uu____76779 = FStar_Options.no_plugins ()  in
    if uu____76779 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____76800 = FStar_Options.use_nbe ()  in
    if uu____76800
    then
      let uu___1478_76803 = s  in
      {
        beta = (uu___1478_76803.beta);
        iota = (uu___1478_76803.iota);
        zeta = (uu___1478_76803.zeta);
        weak = (uu___1478_76803.weak);
        hnf = (uu___1478_76803.hnf);
        primops = (uu___1478_76803.primops);
        do_not_unfold_pure_lets = (uu___1478_76803.do_not_unfold_pure_lets);
        unfold_until = (uu___1478_76803.unfold_until);
        unfold_only = (uu___1478_76803.unfold_only);
        unfold_fully = (uu___1478_76803.unfold_fully);
        unfold_attr = (uu___1478_76803.unfold_attr);
        unfold_tac = (uu___1478_76803.unfold_tac);
        pure_subterms_within_computations =
          (uu___1478_76803.pure_subterms_within_computations);
        simplify = (uu___1478_76803.simplify);
        erase_universes = (uu___1478_76803.erase_universes);
        allow_unbound_universes = (uu___1478_76803.allow_unbound_universes);
        reify_ = (uu___1478_76803.reify_);
        compress_uvars = (uu___1478_76803.compress_uvars);
        no_full_norm = (uu___1478_76803.no_full_norm);
        check_no_uvars = (uu___1478_76803.check_no_uvars);
        unmeta = (uu___1478_76803.unmeta);
        unascribe = (uu___1478_76803.unascribe);
        in_full_norm_request = (uu___1478_76803.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1478_76803.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1478_76803.for_extraction)
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
               (fun uu___531_76840  ->
                  match uu___531_76840 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____76844 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____76850 -> d  in
        let uu____76853 =
          let uu____76854 = to_fsteps s  in
          FStar_All.pipe_right uu____76854 add_nbe  in
        let uu____76855 =
          let uu____76856 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____76859 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____76862 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____76865 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____76868 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____76871 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____76874 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____76877 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____76880 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____76856;
            top = uu____76859;
            cfg = uu____76862;
            primop = uu____76865;
            unfolding = uu____76868;
            b380 = uu____76871;
            wpe = uu____76874;
            norm_delayed = uu____76877;
            print_normalized = uu____76880
          }  in
        let uu____76883 =
          let uu____76886 =
            let uu____76889 = retrieve_plugins ()  in
            FStar_List.append uu____76889 psteps  in
          add_steps built_in_primitive_steps uu____76886  in
        let uu____76892 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____76895 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____76895)
           in
        {
          steps = uu____76853;
          tcenv = e;
          debug = uu____76855;
          delta_level = d1;
          primitive_steps = uu____76883;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____76892;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 