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
          let uu____3929 =
            let uu____3931 = f1 x  in FStar_String.op_Hat uu____3931 ")"  in
          FStar_String.op_Hat "Some (" uu____3929
       in
    let b = FStar_Util.string_of_bool  in
    let uu____3942 =
      let uu____3946 = FStar_All.pipe_right f.beta b  in
      let uu____3950 =
        let uu____3954 = FStar_All.pipe_right f.iota b  in
        let uu____3958 =
          let uu____3962 = FStar_All.pipe_right f.zeta b  in
          let uu____3966 =
            let uu____3970 = FStar_All.pipe_right f.weak b  in
            let uu____3974 =
              let uu____3978 = FStar_All.pipe_right f.hnf b  in
              let uu____3982 =
                let uu____3986 = FStar_All.pipe_right f.primops b  in
                let uu____3990 =
                  let uu____3994 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____3998 =
                    let uu____4002 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____4007 =
                      let uu____4011 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____4037 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____4037
                                  (FStar_String.concat ", ")))
                         in
                      let uu____4051 =
                        let uu____4055 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____4081 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____4081
                                    (FStar_String.concat ", ")))
                           in
                        let uu____4095 =
                          let uu____4099 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____4125 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____4125
                                      (FStar_String.concat ", ")))
                             in
                          let uu____4139 =
                            let uu____4143 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____4147 =
                              let uu____4151 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____4155 =
                                let uu____4159 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____4163 =
                                  let uu____4167 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____4171 =
                                    let uu____4175 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____4179 =
                                      let uu____4183 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____4187 =
                                        let uu____4191 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____4195 =
                                          let uu____4199 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____4203 =
                                            let uu____4207 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____4211 =
                                              let uu____4215 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____4219 =
                                                let uu____4223 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____4227 =
                                                  let uu____4231 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____4235 =
                                                    let uu____4239 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____4239]  in
                                                  uu____4231 :: uu____4235
                                                   in
                                                uu____4223 :: uu____4227  in
                                              uu____4215 :: uu____4219  in
                                            uu____4207 :: uu____4211  in
                                          uu____4199 :: uu____4203  in
                                        uu____4191 :: uu____4195  in
                                      uu____4183 :: uu____4187  in
                                    uu____4175 :: uu____4179  in
                                  uu____4167 :: uu____4171  in
                                uu____4159 :: uu____4163  in
                              uu____4151 :: uu____4155  in
                            uu____4143 :: uu____4147  in
                          uu____4099 :: uu____4139  in
                        uu____4055 :: uu____4095  in
                      uu____4011 :: uu____4051  in
                    uu____4002 :: uu____4007  in
                  uu____3994 :: uu____3998  in
                uu____3986 :: uu____3990  in
              uu____3978 :: uu____3982  in
            uu____3970 :: uu____3974  in
          uu____3962 :: uu____3966  in
        uu____3954 :: uu____3958  in
      uu____3946 :: uu____3950  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____3942
  
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
          let uu___94_4503 = fs  in
          {
            beta = true;
            iota = (uu___94_4503.iota);
            zeta = (uu___94_4503.zeta);
            weak = (uu___94_4503.weak);
            hnf = (uu___94_4503.hnf);
            primops = (uu___94_4503.primops);
            do_not_unfold_pure_lets = (uu___94_4503.do_not_unfold_pure_lets);
            unfold_until = (uu___94_4503.unfold_until);
            unfold_only = (uu___94_4503.unfold_only);
            unfold_fully = (uu___94_4503.unfold_fully);
            unfold_attr = (uu___94_4503.unfold_attr);
            unfold_tac = (uu___94_4503.unfold_tac);
            pure_subterms_within_computations =
              (uu___94_4503.pure_subterms_within_computations);
            simplify = (uu___94_4503.simplify);
            erase_universes = (uu___94_4503.erase_universes);
            allow_unbound_universes = (uu___94_4503.allow_unbound_universes);
            reify_ = (uu___94_4503.reify_);
            compress_uvars = (uu___94_4503.compress_uvars);
            no_full_norm = (uu___94_4503.no_full_norm);
            check_no_uvars = (uu___94_4503.check_no_uvars);
            unmeta = (uu___94_4503.unmeta);
            unascribe = (uu___94_4503.unascribe);
            in_full_norm_request = (uu___94_4503.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___94_4503.weakly_reduce_scrutinee);
            nbe_step = (uu___94_4503.nbe_step);
            for_extraction = (uu___94_4503.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___97_4557 = fs  in
          {
            beta = (uu___97_4557.beta);
            iota = true;
            zeta = (uu___97_4557.zeta);
            weak = (uu___97_4557.weak);
            hnf = (uu___97_4557.hnf);
            primops = (uu___97_4557.primops);
            do_not_unfold_pure_lets = (uu___97_4557.do_not_unfold_pure_lets);
            unfold_until = (uu___97_4557.unfold_until);
            unfold_only = (uu___97_4557.unfold_only);
            unfold_fully = (uu___97_4557.unfold_fully);
            unfold_attr = (uu___97_4557.unfold_attr);
            unfold_tac = (uu___97_4557.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_4557.pure_subterms_within_computations);
            simplify = (uu___97_4557.simplify);
            erase_universes = (uu___97_4557.erase_universes);
            allow_unbound_universes = (uu___97_4557.allow_unbound_universes);
            reify_ = (uu___97_4557.reify_);
            compress_uvars = (uu___97_4557.compress_uvars);
            no_full_norm = (uu___97_4557.no_full_norm);
            check_no_uvars = (uu___97_4557.check_no_uvars);
            unmeta = (uu___97_4557.unmeta);
            unascribe = (uu___97_4557.unascribe);
            in_full_norm_request = (uu___97_4557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___97_4557.weakly_reduce_scrutinee);
            nbe_step = (uu___97_4557.nbe_step);
            for_extraction = (uu___97_4557.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___100_4611 = fs  in
          {
            beta = (uu___100_4611.beta);
            iota = (uu___100_4611.iota);
            zeta = true;
            weak = (uu___100_4611.weak);
            hnf = (uu___100_4611.hnf);
            primops = (uu___100_4611.primops);
            do_not_unfold_pure_lets = (uu___100_4611.do_not_unfold_pure_lets);
            unfold_until = (uu___100_4611.unfold_until);
            unfold_only = (uu___100_4611.unfold_only);
            unfold_fully = (uu___100_4611.unfold_fully);
            unfold_attr = (uu___100_4611.unfold_attr);
            unfold_tac = (uu___100_4611.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_4611.pure_subterms_within_computations);
            simplify = (uu___100_4611.simplify);
            erase_universes = (uu___100_4611.erase_universes);
            allow_unbound_universes = (uu___100_4611.allow_unbound_universes);
            reify_ = (uu___100_4611.reify_);
            compress_uvars = (uu___100_4611.compress_uvars);
            no_full_norm = (uu___100_4611.no_full_norm);
            check_no_uvars = (uu___100_4611.check_no_uvars);
            unmeta = (uu___100_4611.unmeta);
            unascribe = (uu___100_4611.unascribe);
            in_full_norm_request = (uu___100_4611.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_4611.weakly_reduce_scrutinee);
            nbe_step = (uu___100_4611.nbe_step);
            for_extraction = (uu___100_4611.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___104_4665 = fs  in
          {
            beta = false;
            iota = (uu___104_4665.iota);
            zeta = (uu___104_4665.zeta);
            weak = (uu___104_4665.weak);
            hnf = (uu___104_4665.hnf);
            primops = (uu___104_4665.primops);
            do_not_unfold_pure_lets = (uu___104_4665.do_not_unfold_pure_lets);
            unfold_until = (uu___104_4665.unfold_until);
            unfold_only = (uu___104_4665.unfold_only);
            unfold_fully = (uu___104_4665.unfold_fully);
            unfold_attr = (uu___104_4665.unfold_attr);
            unfold_tac = (uu___104_4665.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_4665.pure_subterms_within_computations);
            simplify = (uu___104_4665.simplify);
            erase_universes = (uu___104_4665.erase_universes);
            allow_unbound_universes = (uu___104_4665.allow_unbound_universes);
            reify_ = (uu___104_4665.reify_);
            compress_uvars = (uu___104_4665.compress_uvars);
            no_full_norm = (uu___104_4665.no_full_norm);
            check_no_uvars = (uu___104_4665.check_no_uvars);
            unmeta = (uu___104_4665.unmeta);
            unascribe = (uu___104_4665.unascribe);
            in_full_norm_request = (uu___104_4665.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___104_4665.weakly_reduce_scrutinee);
            nbe_step = (uu___104_4665.nbe_step);
            for_extraction = (uu___104_4665.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___108_4719 = fs  in
          {
            beta = (uu___108_4719.beta);
            iota = false;
            zeta = (uu___108_4719.zeta);
            weak = (uu___108_4719.weak);
            hnf = (uu___108_4719.hnf);
            primops = (uu___108_4719.primops);
            do_not_unfold_pure_lets = (uu___108_4719.do_not_unfold_pure_lets);
            unfold_until = (uu___108_4719.unfold_until);
            unfold_only = (uu___108_4719.unfold_only);
            unfold_fully = (uu___108_4719.unfold_fully);
            unfold_attr = (uu___108_4719.unfold_attr);
            unfold_tac = (uu___108_4719.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_4719.pure_subterms_within_computations);
            simplify = (uu___108_4719.simplify);
            erase_universes = (uu___108_4719.erase_universes);
            allow_unbound_universes = (uu___108_4719.allow_unbound_universes);
            reify_ = (uu___108_4719.reify_);
            compress_uvars = (uu___108_4719.compress_uvars);
            no_full_norm = (uu___108_4719.no_full_norm);
            check_no_uvars = (uu___108_4719.check_no_uvars);
            unmeta = (uu___108_4719.unmeta);
            unascribe = (uu___108_4719.unascribe);
            in_full_norm_request = (uu___108_4719.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___108_4719.weakly_reduce_scrutinee);
            nbe_step = (uu___108_4719.nbe_step);
            for_extraction = (uu___108_4719.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___112_4773 = fs  in
          {
            beta = (uu___112_4773.beta);
            iota = (uu___112_4773.iota);
            zeta = false;
            weak = (uu___112_4773.weak);
            hnf = (uu___112_4773.hnf);
            primops = (uu___112_4773.primops);
            do_not_unfold_pure_lets = (uu___112_4773.do_not_unfold_pure_lets);
            unfold_until = (uu___112_4773.unfold_until);
            unfold_only = (uu___112_4773.unfold_only);
            unfold_fully = (uu___112_4773.unfold_fully);
            unfold_attr = (uu___112_4773.unfold_attr);
            unfold_tac = (uu___112_4773.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_4773.pure_subterms_within_computations);
            simplify = (uu___112_4773.simplify);
            erase_universes = (uu___112_4773.erase_universes);
            allow_unbound_universes = (uu___112_4773.allow_unbound_universes);
            reify_ = (uu___112_4773.reify_);
            compress_uvars = (uu___112_4773.compress_uvars);
            no_full_norm = (uu___112_4773.no_full_norm);
            check_no_uvars = (uu___112_4773.check_no_uvars);
            unmeta = (uu___112_4773.unmeta);
            unascribe = (uu___112_4773.unascribe);
            in_full_norm_request = (uu___112_4773.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___112_4773.weakly_reduce_scrutinee);
            nbe_step = (uu___112_4773.nbe_step);
            for_extraction = (uu___112_4773.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____4827 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___117_4855 = fs  in
          {
            beta = (uu___117_4855.beta);
            iota = (uu___117_4855.iota);
            zeta = (uu___117_4855.zeta);
            weak = true;
            hnf = (uu___117_4855.hnf);
            primops = (uu___117_4855.primops);
            do_not_unfold_pure_lets = (uu___117_4855.do_not_unfold_pure_lets);
            unfold_until = (uu___117_4855.unfold_until);
            unfold_only = (uu___117_4855.unfold_only);
            unfold_fully = (uu___117_4855.unfold_fully);
            unfold_attr = (uu___117_4855.unfold_attr);
            unfold_tac = (uu___117_4855.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_4855.pure_subterms_within_computations);
            simplify = (uu___117_4855.simplify);
            erase_universes = (uu___117_4855.erase_universes);
            allow_unbound_universes = (uu___117_4855.allow_unbound_universes);
            reify_ = (uu___117_4855.reify_);
            compress_uvars = (uu___117_4855.compress_uvars);
            no_full_norm = (uu___117_4855.no_full_norm);
            check_no_uvars = (uu___117_4855.check_no_uvars);
            unmeta = (uu___117_4855.unmeta);
            unascribe = (uu___117_4855.unascribe);
            in_full_norm_request = (uu___117_4855.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___117_4855.weakly_reduce_scrutinee);
            nbe_step = (uu___117_4855.nbe_step);
            for_extraction = (uu___117_4855.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___120_4909 = fs  in
          {
            beta = (uu___120_4909.beta);
            iota = (uu___120_4909.iota);
            zeta = (uu___120_4909.zeta);
            weak = (uu___120_4909.weak);
            hnf = true;
            primops = (uu___120_4909.primops);
            do_not_unfold_pure_lets = (uu___120_4909.do_not_unfold_pure_lets);
            unfold_until = (uu___120_4909.unfold_until);
            unfold_only = (uu___120_4909.unfold_only);
            unfold_fully = (uu___120_4909.unfold_fully);
            unfold_attr = (uu___120_4909.unfold_attr);
            unfold_tac = (uu___120_4909.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_4909.pure_subterms_within_computations);
            simplify = (uu___120_4909.simplify);
            erase_universes = (uu___120_4909.erase_universes);
            allow_unbound_universes = (uu___120_4909.allow_unbound_universes);
            reify_ = (uu___120_4909.reify_);
            compress_uvars = (uu___120_4909.compress_uvars);
            no_full_norm = (uu___120_4909.no_full_norm);
            check_no_uvars = (uu___120_4909.check_no_uvars);
            unmeta = (uu___120_4909.unmeta);
            unascribe = (uu___120_4909.unascribe);
            in_full_norm_request = (uu___120_4909.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___120_4909.weakly_reduce_scrutinee);
            nbe_step = (uu___120_4909.nbe_step);
            for_extraction = (uu___120_4909.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___123_4963 = fs  in
          {
            beta = (uu___123_4963.beta);
            iota = (uu___123_4963.iota);
            zeta = (uu___123_4963.zeta);
            weak = (uu___123_4963.weak);
            hnf = (uu___123_4963.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___123_4963.do_not_unfold_pure_lets);
            unfold_until = (uu___123_4963.unfold_until);
            unfold_only = (uu___123_4963.unfold_only);
            unfold_fully = (uu___123_4963.unfold_fully);
            unfold_attr = (uu___123_4963.unfold_attr);
            unfold_tac = (uu___123_4963.unfold_tac);
            pure_subterms_within_computations =
              (uu___123_4963.pure_subterms_within_computations);
            simplify = (uu___123_4963.simplify);
            erase_universes = (uu___123_4963.erase_universes);
            allow_unbound_universes = (uu___123_4963.allow_unbound_universes);
            reify_ = (uu___123_4963.reify_);
            compress_uvars = (uu___123_4963.compress_uvars);
            no_full_norm = (uu___123_4963.no_full_norm);
            check_no_uvars = (uu___123_4963.check_no_uvars);
            unmeta = (uu___123_4963.unmeta);
            unascribe = (uu___123_4963.unascribe);
            in_full_norm_request = (uu___123_4963.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___123_4963.weakly_reduce_scrutinee);
            nbe_step = (uu___123_4963.nbe_step);
            for_extraction = (uu___123_4963.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding uu____5017 -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___129_5019 = fs  in
          {
            beta = (uu___129_5019.beta);
            iota = (uu___129_5019.iota);
            zeta = (uu___129_5019.zeta);
            weak = (uu___129_5019.weak);
            hnf = (uu___129_5019.hnf);
            primops = (uu___129_5019.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___129_5019.unfold_until);
            unfold_only = (uu___129_5019.unfold_only);
            unfold_fully = (uu___129_5019.unfold_fully);
            unfold_attr = (uu___129_5019.unfold_attr);
            unfold_tac = (uu___129_5019.unfold_tac);
            pure_subterms_within_computations =
              (uu___129_5019.pure_subterms_within_computations);
            simplify = (uu___129_5019.simplify);
            erase_universes = (uu___129_5019.erase_universes);
            allow_unbound_universes = (uu___129_5019.allow_unbound_universes);
            reify_ = (uu___129_5019.reify_);
            compress_uvars = (uu___129_5019.compress_uvars);
            no_full_norm = (uu___129_5019.no_full_norm);
            check_no_uvars = (uu___129_5019.check_no_uvars);
            unmeta = (uu___129_5019.unmeta);
            unascribe = (uu___129_5019.unascribe);
            in_full_norm_request = (uu___129_5019.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___129_5019.weakly_reduce_scrutinee);
            nbe_step = (uu___129_5019.nbe_step);
            for_extraction = (uu___129_5019.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___133_5074 = fs  in
          {
            beta = (uu___133_5074.beta);
            iota = (uu___133_5074.iota);
            zeta = (uu___133_5074.zeta);
            weak = (uu___133_5074.weak);
            hnf = (uu___133_5074.hnf);
            primops = (uu___133_5074.primops);
            do_not_unfold_pure_lets = (uu___133_5074.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___133_5074.unfold_only);
            unfold_fully = (uu___133_5074.unfold_fully);
            unfold_attr = (uu___133_5074.unfold_attr);
            unfold_tac = (uu___133_5074.unfold_tac);
            pure_subterms_within_computations =
              (uu___133_5074.pure_subterms_within_computations);
            simplify = (uu___133_5074.simplify);
            erase_universes = (uu___133_5074.erase_universes);
            allow_unbound_universes = (uu___133_5074.allow_unbound_universes);
            reify_ = (uu___133_5074.reify_);
            compress_uvars = (uu___133_5074.compress_uvars);
            no_full_norm = (uu___133_5074.no_full_norm);
            check_no_uvars = (uu___133_5074.check_no_uvars);
            unmeta = (uu___133_5074.unmeta);
            unascribe = (uu___133_5074.unascribe);
            in_full_norm_request = (uu___133_5074.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___133_5074.weakly_reduce_scrutinee);
            nbe_step = (uu___133_5074.nbe_step);
            for_extraction = (uu___133_5074.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___137_5134 = fs  in
          {
            beta = (uu___137_5134.beta);
            iota = (uu___137_5134.iota);
            zeta = (uu___137_5134.zeta);
            weak = (uu___137_5134.weak);
            hnf = (uu___137_5134.hnf);
            primops = (uu___137_5134.primops);
            do_not_unfold_pure_lets = (uu___137_5134.do_not_unfold_pure_lets);
            unfold_until = (uu___137_5134.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___137_5134.unfold_fully);
            unfold_attr = (uu___137_5134.unfold_attr);
            unfold_tac = (uu___137_5134.unfold_tac);
            pure_subterms_within_computations =
              (uu___137_5134.pure_subterms_within_computations);
            simplify = (uu___137_5134.simplify);
            erase_universes = (uu___137_5134.erase_universes);
            allow_unbound_universes = (uu___137_5134.allow_unbound_universes);
            reify_ = (uu___137_5134.reify_);
            compress_uvars = (uu___137_5134.compress_uvars);
            no_full_norm = (uu___137_5134.no_full_norm);
            check_no_uvars = (uu___137_5134.check_no_uvars);
            unmeta = (uu___137_5134.unmeta);
            unascribe = (uu___137_5134.unascribe);
            in_full_norm_request = (uu___137_5134.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___137_5134.weakly_reduce_scrutinee);
            nbe_step = (uu___137_5134.nbe_step);
            for_extraction = (uu___137_5134.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___141_5200 = fs  in
          {
            beta = (uu___141_5200.beta);
            iota = (uu___141_5200.iota);
            zeta = (uu___141_5200.zeta);
            weak = (uu___141_5200.weak);
            hnf = (uu___141_5200.hnf);
            primops = (uu___141_5200.primops);
            do_not_unfold_pure_lets = (uu___141_5200.do_not_unfold_pure_lets);
            unfold_until = (uu___141_5200.unfold_until);
            unfold_only = (uu___141_5200.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___141_5200.unfold_attr);
            unfold_tac = (uu___141_5200.unfold_tac);
            pure_subterms_within_computations =
              (uu___141_5200.pure_subterms_within_computations);
            simplify = (uu___141_5200.simplify);
            erase_universes = (uu___141_5200.erase_universes);
            allow_unbound_universes = (uu___141_5200.allow_unbound_universes);
            reify_ = (uu___141_5200.reify_);
            compress_uvars = (uu___141_5200.compress_uvars);
            no_full_norm = (uu___141_5200.no_full_norm);
            check_no_uvars = (uu___141_5200.check_no_uvars);
            unmeta = (uu___141_5200.unmeta);
            unascribe = (uu___141_5200.unascribe);
            in_full_norm_request = (uu___141_5200.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___141_5200.weakly_reduce_scrutinee);
            nbe_step = (uu___141_5200.nbe_step);
            for_extraction = (uu___141_5200.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___145_5266 = fs  in
          {
            beta = (uu___145_5266.beta);
            iota = (uu___145_5266.iota);
            zeta = (uu___145_5266.zeta);
            weak = (uu___145_5266.weak);
            hnf = (uu___145_5266.hnf);
            primops = (uu___145_5266.primops);
            do_not_unfold_pure_lets = (uu___145_5266.do_not_unfold_pure_lets);
            unfold_until = (uu___145_5266.unfold_until);
            unfold_only = (uu___145_5266.unfold_only);
            unfold_fully = (uu___145_5266.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___145_5266.unfold_tac);
            pure_subterms_within_computations =
              (uu___145_5266.pure_subterms_within_computations);
            simplify = (uu___145_5266.simplify);
            erase_universes = (uu___145_5266.erase_universes);
            allow_unbound_universes = (uu___145_5266.allow_unbound_universes);
            reify_ = (uu___145_5266.reify_);
            compress_uvars = (uu___145_5266.compress_uvars);
            no_full_norm = (uu___145_5266.no_full_norm);
            check_no_uvars = (uu___145_5266.check_no_uvars);
            unmeta = (uu___145_5266.unmeta);
            unascribe = (uu___145_5266.unascribe);
            in_full_norm_request = (uu___145_5266.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___145_5266.weakly_reduce_scrutinee);
            nbe_step = (uu___145_5266.nbe_step);
            for_extraction = (uu___145_5266.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___148_5325 = fs  in
          {
            beta = (uu___148_5325.beta);
            iota = (uu___148_5325.iota);
            zeta = (uu___148_5325.zeta);
            weak = (uu___148_5325.weak);
            hnf = (uu___148_5325.hnf);
            primops = (uu___148_5325.primops);
            do_not_unfold_pure_lets = (uu___148_5325.do_not_unfold_pure_lets);
            unfold_until = (uu___148_5325.unfold_until);
            unfold_only = (uu___148_5325.unfold_only);
            unfold_fully = (uu___148_5325.unfold_fully);
            unfold_attr = (uu___148_5325.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___148_5325.pure_subterms_within_computations);
            simplify = (uu___148_5325.simplify);
            erase_universes = (uu___148_5325.erase_universes);
            allow_unbound_universes = (uu___148_5325.allow_unbound_universes);
            reify_ = (uu___148_5325.reify_);
            compress_uvars = (uu___148_5325.compress_uvars);
            no_full_norm = (uu___148_5325.no_full_norm);
            check_no_uvars = (uu___148_5325.check_no_uvars);
            unmeta = (uu___148_5325.unmeta);
            unascribe = (uu___148_5325.unascribe);
            in_full_norm_request = (uu___148_5325.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___148_5325.weakly_reduce_scrutinee);
            nbe_step = (uu___148_5325.nbe_step);
            for_extraction = (uu___148_5325.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___151_5379 = fs  in
          {
            beta = (uu___151_5379.beta);
            iota = (uu___151_5379.iota);
            zeta = (uu___151_5379.zeta);
            weak = (uu___151_5379.weak);
            hnf = (uu___151_5379.hnf);
            primops = (uu___151_5379.primops);
            do_not_unfold_pure_lets = (uu___151_5379.do_not_unfold_pure_lets);
            unfold_until = (uu___151_5379.unfold_until);
            unfold_only = (uu___151_5379.unfold_only);
            unfold_fully = (uu___151_5379.unfold_fully);
            unfold_attr = (uu___151_5379.unfold_attr);
            unfold_tac = (uu___151_5379.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___151_5379.simplify);
            erase_universes = (uu___151_5379.erase_universes);
            allow_unbound_universes = (uu___151_5379.allow_unbound_universes);
            reify_ = (uu___151_5379.reify_);
            compress_uvars = (uu___151_5379.compress_uvars);
            no_full_norm = (uu___151_5379.no_full_norm);
            check_no_uvars = (uu___151_5379.check_no_uvars);
            unmeta = (uu___151_5379.unmeta);
            unascribe = (uu___151_5379.unascribe);
            in_full_norm_request = (uu___151_5379.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___151_5379.weakly_reduce_scrutinee);
            nbe_step = (uu___151_5379.nbe_step);
            for_extraction = (uu___151_5379.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___154_5433 = fs  in
          {
            beta = (uu___154_5433.beta);
            iota = (uu___154_5433.iota);
            zeta = (uu___154_5433.zeta);
            weak = (uu___154_5433.weak);
            hnf = (uu___154_5433.hnf);
            primops = (uu___154_5433.primops);
            do_not_unfold_pure_lets = (uu___154_5433.do_not_unfold_pure_lets);
            unfold_until = (uu___154_5433.unfold_until);
            unfold_only = (uu___154_5433.unfold_only);
            unfold_fully = (uu___154_5433.unfold_fully);
            unfold_attr = (uu___154_5433.unfold_attr);
            unfold_tac = (uu___154_5433.unfold_tac);
            pure_subterms_within_computations =
              (uu___154_5433.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___154_5433.erase_universes);
            allow_unbound_universes = (uu___154_5433.allow_unbound_universes);
            reify_ = (uu___154_5433.reify_);
            compress_uvars = (uu___154_5433.compress_uvars);
            no_full_norm = (uu___154_5433.no_full_norm);
            check_no_uvars = (uu___154_5433.check_no_uvars);
            unmeta = (uu___154_5433.unmeta);
            unascribe = (uu___154_5433.unascribe);
            in_full_norm_request = (uu___154_5433.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___154_5433.weakly_reduce_scrutinee);
            nbe_step = (uu___154_5433.nbe_step);
            for_extraction = (uu___154_5433.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___157_5487 = fs  in
          {
            beta = (uu___157_5487.beta);
            iota = (uu___157_5487.iota);
            zeta = (uu___157_5487.zeta);
            weak = (uu___157_5487.weak);
            hnf = (uu___157_5487.hnf);
            primops = (uu___157_5487.primops);
            do_not_unfold_pure_lets = (uu___157_5487.do_not_unfold_pure_lets);
            unfold_until = (uu___157_5487.unfold_until);
            unfold_only = (uu___157_5487.unfold_only);
            unfold_fully = (uu___157_5487.unfold_fully);
            unfold_attr = (uu___157_5487.unfold_attr);
            unfold_tac = (uu___157_5487.unfold_tac);
            pure_subterms_within_computations =
              (uu___157_5487.pure_subterms_within_computations);
            simplify = (uu___157_5487.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___157_5487.allow_unbound_universes);
            reify_ = (uu___157_5487.reify_);
            compress_uvars = (uu___157_5487.compress_uvars);
            no_full_norm = (uu___157_5487.no_full_norm);
            check_no_uvars = (uu___157_5487.check_no_uvars);
            unmeta = (uu___157_5487.unmeta);
            unascribe = (uu___157_5487.unascribe);
            in_full_norm_request = (uu___157_5487.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___157_5487.weakly_reduce_scrutinee);
            nbe_step = (uu___157_5487.nbe_step);
            for_extraction = (uu___157_5487.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___160_5541 = fs  in
          {
            beta = (uu___160_5541.beta);
            iota = (uu___160_5541.iota);
            zeta = (uu___160_5541.zeta);
            weak = (uu___160_5541.weak);
            hnf = (uu___160_5541.hnf);
            primops = (uu___160_5541.primops);
            do_not_unfold_pure_lets = (uu___160_5541.do_not_unfold_pure_lets);
            unfold_until = (uu___160_5541.unfold_until);
            unfold_only = (uu___160_5541.unfold_only);
            unfold_fully = (uu___160_5541.unfold_fully);
            unfold_attr = (uu___160_5541.unfold_attr);
            unfold_tac = (uu___160_5541.unfold_tac);
            pure_subterms_within_computations =
              (uu___160_5541.pure_subterms_within_computations);
            simplify = (uu___160_5541.simplify);
            erase_universes = (uu___160_5541.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___160_5541.reify_);
            compress_uvars = (uu___160_5541.compress_uvars);
            no_full_norm = (uu___160_5541.no_full_norm);
            check_no_uvars = (uu___160_5541.check_no_uvars);
            unmeta = (uu___160_5541.unmeta);
            unascribe = (uu___160_5541.unascribe);
            in_full_norm_request = (uu___160_5541.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___160_5541.weakly_reduce_scrutinee);
            nbe_step = (uu___160_5541.nbe_step);
            for_extraction = (uu___160_5541.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___163_5595 = fs  in
          {
            beta = (uu___163_5595.beta);
            iota = (uu___163_5595.iota);
            zeta = (uu___163_5595.zeta);
            weak = (uu___163_5595.weak);
            hnf = (uu___163_5595.hnf);
            primops = (uu___163_5595.primops);
            do_not_unfold_pure_lets = (uu___163_5595.do_not_unfold_pure_lets);
            unfold_until = (uu___163_5595.unfold_until);
            unfold_only = (uu___163_5595.unfold_only);
            unfold_fully = (uu___163_5595.unfold_fully);
            unfold_attr = (uu___163_5595.unfold_attr);
            unfold_tac = (uu___163_5595.unfold_tac);
            pure_subterms_within_computations =
              (uu___163_5595.pure_subterms_within_computations);
            simplify = (uu___163_5595.simplify);
            erase_universes = (uu___163_5595.erase_universes);
            allow_unbound_universes = (uu___163_5595.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___163_5595.compress_uvars);
            no_full_norm = (uu___163_5595.no_full_norm);
            check_no_uvars = (uu___163_5595.check_no_uvars);
            unmeta = (uu___163_5595.unmeta);
            unascribe = (uu___163_5595.unascribe);
            in_full_norm_request = (uu___163_5595.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___163_5595.weakly_reduce_scrutinee);
            nbe_step = (uu___163_5595.nbe_step);
            for_extraction = (uu___163_5595.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___166_5649 = fs  in
          {
            beta = (uu___166_5649.beta);
            iota = (uu___166_5649.iota);
            zeta = (uu___166_5649.zeta);
            weak = (uu___166_5649.weak);
            hnf = (uu___166_5649.hnf);
            primops = (uu___166_5649.primops);
            do_not_unfold_pure_lets = (uu___166_5649.do_not_unfold_pure_lets);
            unfold_until = (uu___166_5649.unfold_until);
            unfold_only = (uu___166_5649.unfold_only);
            unfold_fully = (uu___166_5649.unfold_fully);
            unfold_attr = (uu___166_5649.unfold_attr);
            unfold_tac = (uu___166_5649.unfold_tac);
            pure_subterms_within_computations =
              (uu___166_5649.pure_subterms_within_computations);
            simplify = (uu___166_5649.simplify);
            erase_universes = (uu___166_5649.erase_universes);
            allow_unbound_universes = (uu___166_5649.allow_unbound_universes);
            reify_ = (uu___166_5649.reify_);
            compress_uvars = true;
            no_full_norm = (uu___166_5649.no_full_norm);
            check_no_uvars = (uu___166_5649.check_no_uvars);
            unmeta = (uu___166_5649.unmeta);
            unascribe = (uu___166_5649.unascribe);
            in_full_norm_request = (uu___166_5649.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___166_5649.weakly_reduce_scrutinee);
            nbe_step = (uu___166_5649.nbe_step);
            for_extraction = (uu___166_5649.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___169_5703 = fs  in
          {
            beta = (uu___169_5703.beta);
            iota = (uu___169_5703.iota);
            zeta = (uu___169_5703.zeta);
            weak = (uu___169_5703.weak);
            hnf = (uu___169_5703.hnf);
            primops = (uu___169_5703.primops);
            do_not_unfold_pure_lets = (uu___169_5703.do_not_unfold_pure_lets);
            unfold_until = (uu___169_5703.unfold_until);
            unfold_only = (uu___169_5703.unfold_only);
            unfold_fully = (uu___169_5703.unfold_fully);
            unfold_attr = (uu___169_5703.unfold_attr);
            unfold_tac = (uu___169_5703.unfold_tac);
            pure_subterms_within_computations =
              (uu___169_5703.pure_subterms_within_computations);
            simplify = (uu___169_5703.simplify);
            erase_universes = (uu___169_5703.erase_universes);
            allow_unbound_universes = (uu___169_5703.allow_unbound_universes);
            reify_ = (uu___169_5703.reify_);
            compress_uvars = (uu___169_5703.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___169_5703.check_no_uvars);
            unmeta = (uu___169_5703.unmeta);
            unascribe = (uu___169_5703.unascribe);
            in_full_norm_request = (uu___169_5703.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___169_5703.weakly_reduce_scrutinee);
            nbe_step = (uu___169_5703.nbe_step);
            for_extraction = (uu___169_5703.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___172_5757 = fs  in
          {
            beta = (uu___172_5757.beta);
            iota = (uu___172_5757.iota);
            zeta = (uu___172_5757.zeta);
            weak = (uu___172_5757.weak);
            hnf = (uu___172_5757.hnf);
            primops = (uu___172_5757.primops);
            do_not_unfold_pure_lets = (uu___172_5757.do_not_unfold_pure_lets);
            unfold_until = (uu___172_5757.unfold_until);
            unfold_only = (uu___172_5757.unfold_only);
            unfold_fully = (uu___172_5757.unfold_fully);
            unfold_attr = (uu___172_5757.unfold_attr);
            unfold_tac = (uu___172_5757.unfold_tac);
            pure_subterms_within_computations =
              (uu___172_5757.pure_subterms_within_computations);
            simplify = (uu___172_5757.simplify);
            erase_universes = (uu___172_5757.erase_universes);
            allow_unbound_universes = (uu___172_5757.allow_unbound_universes);
            reify_ = (uu___172_5757.reify_);
            compress_uvars = (uu___172_5757.compress_uvars);
            no_full_norm = (uu___172_5757.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___172_5757.unmeta);
            unascribe = (uu___172_5757.unascribe);
            in_full_norm_request = (uu___172_5757.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___172_5757.weakly_reduce_scrutinee);
            nbe_step = (uu___172_5757.nbe_step);
            for_extraction = (uu___172_5757.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___175_5811 = fs  in
          {
            beta = (uu___175_5811.beta);
            iota = (uu___175_5811.iota);
            zeta = (uu___175_5811.zeta);
            weak = (uu___175_5811.weak);
            hnf = (uu___175_5811.hnf);
            primops = (uu___175_5811.primops);
            do_not_unfold_pure_lets = (uu___175_5811.do_not_unfold_pure_lets);
            unfold_until = (uu___175_5811.unfold_until);
            unfold_only = (uu___175_5811.unfold_only);
            unfold_fully = (uu___175_5811.unfold_fully);
            unfold_attr = (uu___175_5811.unfold_attr);
            unfold_tac = (uu___175_5811.unfold_tac);
            pure_subterms_within_computations =
              (uu___175_5811.pure_subterms_within_computations);
            simplify = (uu___175_5811.simplify);
            erase_universes = (uu___175_5811.erase_universes);
            allow_unbound_universes = (uu___175_5811.allow_unbound_universes);
            reify_ = (uu___175_5811.reify_);
            compress_uvars = (uu___175_5811.compress_uvars);
            no_full_norm = (uu___175_5811.no_full_norm);
            check_no_uvars = (uu___175_5811.check_no_uvars);
            unmeta = true;
            unascribe = (uu___175_5811.unascribe);
            in_full_norm_request = (uu___175_5811.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___175_5811.weakly_reduce_scrutinee);
            nbe_step = (uu___175_5811.nbe_step);
            for_extraction = (uu___175_5811.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___178_5865 = fs  in
          {
            beta = (uu___178_5865.beta);
            iota = (uu___178_5865.iota);
            zeta = (uu___178_5865.zeta);
            weak = (uu___178_5865.weak);
            hnf = (uu___178_5865.hnf);
            primops = (uu___178_5865.primops);
            do_not_unfold_pure_lets = (uu___178_5865.do_not_unfold_pure_lets);
            unfold_until = (uu___178_5865.unfold_until);
            unfold_only = (uu___178_5865.unfold_only);
            unfold_fully = (uu___178_5865.unfold_fully);
            unfold_attr = (uu___178_5865.unfold_attr);
            unfold_tac = (uu___178_5865.unfold_tac);
            pure_subterms_within_computations =
              (uu___178_5865.pure_subterms_within_computations);
            simplify = (uu___178_5865.simplify);
            erase_universes = (uu___178_5865.erase_universes);
            allow_unbound_universes = (uu___178_5865.allow_unbound_universes);
            reify_ = (uu___178_5865.reify_);
            compress_uvars = (uu___178_5865.compress_uvars);
            no_full_norm = (uu___178_5865.no_full_norm);
            check_no_uvars = (uu___178_5865.check_no_uvars);
            unmeta = (uu___178_5865.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___178_5865.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___178_5865.weakly_reduce_scrutinee);
            nbe_step = (uu___178_5865.nbe_step);
            for_extraction = (uu___178_5865.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___181_5919 = fs  in
          {
            beta = (uu___181_5919.beta);
            iota = (uu___181_5919.iota);
            zeta = (uu___181_5919.zeta);
            weak = (uu___181_5919.weak);
            hnf = (uu___181_5919.hnf);
            primops = (uu___181_5919.primops);
            do_not_unfold_pure_lets = (uu___181_5919.do_not_unfold_pure_lets);
            unfold_until = (uu___181_5919.unfold_until);
            unfold_only = (uu___181_5919.unfold_only);
            unfold_fully = (uu___181_5919.unfold_fully);
            unfold_attr = (uu___181_5919.unfold_attr);
            unfold_tac = (uu___181_5919.unfold_tac);
            pure_subterms_within_computations =
              (uu___181_5919.pure_subterms_within_computations);
            simplify = (uu___181_5919.simplify);
            erase_universes = (uu___181_5919.erase_universes);
            allow_unbound_universes = (uu___181_5919.allow_unbound_universes);
            reify_ = (uu___181_5919.reify_);
            compress_uvars = (uu___181_5919.compress_uvars);
            no_full_norm = (uu___181_5919.no_full_norm);
            check_no_uvars = (uu___181_5919.check_no_uvars);
            unmeta = (uu___181_5919.unmeta);
            unascribe = (uu___181_5919.unascribe);
            in_full_norm_request = (uu___181_5919.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___181_5919.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___181_5919.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___184_5973 = fs  in
          {
            beta = (uu___184_5973.beta);
            iota = (uu___184_5973.iota);
            zeta = (uu___184_5973.zeta);
            weak = (uu___184_5973.weak);
            hnf = (uu___184_5973.hnf);
            primops = (uu___184_5973.primops);
            do_not_unfold_pure_lets = (uu___184_5973.do_not_unfold_pure_lets);
            unfold_until = (uu___184_5973.unfold_until);
            unfold_only = (uu___184_5973.unfold_only);
            unfold_fully = (uu___184_5973.unfold_fully);
            unfold_attr = (uu___184_5973.unfold_attr);
            unfold_tac = (uu___184_5973.unfold_tac);
            pure_subterms_within_computations =
              (uu___184_5973.pure_subterms_within_computations);
            simplify = (uu___184_5973.simplify);
            erase_universes = (uu___184_5973.erase_universes);
            allow_unbound_universes = (uu___184_5973.allow_unbound_universes);
            reify_ = (uu___184_5973.reify_);
            compress_uvars = (uu___184_5973.compress_uvars);
            no_full_norm = (uu___184_5973.no_full_norm);
            check_no_uvars = (uu___184_5973.check_no_uvars);
            unmeta = (uu___184_5973.unmeta);
            unascribe = (uu___184_5973.unascribe);
            in_full_norm_request = (uu___184_5973.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___184_5973.weakly_reduce_scrutinee);
            nbe_step = (uu___184_5973.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____6179  -> []) } 
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
    let uu____10010 =
      let uu____10014 =
        let uu____10018 =
          let uu____10020 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____10020  in
        [uu____10018; "}"]  in
      "{" :: uu____10014  in
    FStar_String.concat "\n" uu____10010
  
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
             let uu____10312 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____10312 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____10388 = FStar_Util.psmap_empty ()  in add_steps uu____10388 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____10516 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____10516
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____10622 =
        let uu____10637 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____10637  in
      FStar_Util.is_some uu____10622
  
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
      let uu____11198 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____11198 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____11238 = FStar_Syntax_Embeddings.embed emb x  in
        uu____11238 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____11283 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____11283 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____11298 .
    'Auu____11298 ->
      FStar_Range.range -> 'Auu____11298 FStar_Syntax_Syntax.syntax
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
    let uu____11487 =
      let uu____11500 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____11500  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____11487  in
  let arg_as_bounded_int1 uu____11545 =
    match uu____11545 with
    | (a,uu____11566) ->
        let uu____11588 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____11588 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____11667 =
               let uu____11686 =
                 let uu____11687 = FStar_Syntax_Subst.compress hd1  in
                 uu____11687.FStar_Syntax_Syntax.n  in
               (uu____11686, args)  in
             (match uu____11667 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____11723)::[]) when
                  let uu____11781 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____11781 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____11797 =
                    let uu____11798 = FStar_Syntax_Subst.compress arg1  in
                    uu____11798.FStar_Syntax_Syntax.n  in
                  (match uu____11797 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____11831 =
                         let uu____11839 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____11839)  in
                       FStar_Pervasives_Native.Some uu____11831
                   | uu____11850 -> FStar_Pervasives_Native.None)
              | uu____11858 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____11927 = f a  in FStar_Pervasives_Native.Some uu____11927
    | uu____11928 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____11984 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____11984
    | uu____11985 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____12068 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____12068  in
  let binary_op1 as_a f res n1 args =
    let uu____12174 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____12174  in
  let as_primitive_step is_strong uu____12283 =
    match uu____12283 with
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
           let uu____12443 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____12443)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____12491 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____12491)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____12538 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____12538)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____12597 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____12597)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____12656 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____12656)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____12849 =
          let uu____12858 = as_a a  in
          let uu____12861 = as_b b  in (uu____12858, uu____12861)  in
        (match uu____12849 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____12880 =
               let uu____12889 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____12889  in
             FStar_Pervasives_Native.Some uu____12880
         | uu____12894 -> FStar_Pervasives_Native.None)
    | uu____12907 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____12953 =
        let uu____12954 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____12954  in
      mk uu____12953 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____12986 =
      let uu____12993 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____12993  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____12986
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____13069 =
      let uu____13070 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____13070  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____13069  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____13196 = arg_as_string1 a1  in
        (match uu____13196 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____13209 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____13209 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____13231 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____13231
              | uu____13245 -> FStar_Pervasives_Native.None)
         | uu____13255 -> FStar_Pervasives_Native.None)
    | uu____13263 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____13392 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____13392 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____13412 = arg_as_string1 a2  in
             (match uu____13412 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____13429 =
                    let uu____13438 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____13438 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____13429
              | uu____13452 -> FStar_Pervasives_Native.None)
         | uu____13460 -> FStar_Pervasives_Native.None)
    | uu____13470 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____13528 =
          let uu____13542 = arg_as_string1 a1  in
          let uu____13546 = arg_as_int1 a2  in
          let uu____13549 = arg_as_int1 a3  in
          (uu____13542, uu____13546, uu____13549)  in
        (match uu____13528 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___501_13590  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____13599 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____13599) ()
              with | uu___500_13614 -> FStar_Pervasives_Native.None)
         | uu____13625 -> FStar_Pervasives_Native.None)
    | uu____13643 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____13669 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____13669  in
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
        let uu____13784 =
          let uu____13794 = arg_as_string1 a1  in
          let uu____13798 = arg_as_int1 a2  in (uu____13794, uu____13798)  in
        (match uu____13784 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___535_13830  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____13839 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____13839) ()
              with | uu___534_13854 -> FStar_Pervasives_Native.None)
         | uu____13865 -> FStar_Pervasives_Native.None)
    | uu____13879 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____13926 =
          let uu____13937 = arg_as_string1 a1  in
          let uu____13941 = arg_as_char1 a2  in (uu____13937, uu____13941)
           in
        (match uu____13926 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___556_13978  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____13986 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____13986) ()
              with | uu___555_14000 -> FStar_Pervasives_Native.None)
         | uu____14011 -> FStar_Pervasives_Native.None)
    | uu____14026 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____14076 =
          let uu____14098 = arg_as_string1 fn  in
          let uu____14102 = arg_as_int1 from_line  in
          let uu____14105 = arg_as_int1 from_col  in
          let uu____14108 = arg_as_int1 to_line  in
          let uu____14111 = arg_as_int1 to_col  in
          (uu____14098, uu____14102, uu____14105, uu____14108, uu____14111)
           in
        (match uu____14076 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____14150 =
                 let uu____14151 = FStar_BigInt.to_int_fs from_l  in
                 let uu____14153 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____14151 uu____14153  in
               let uu____14155 =
                 let uu____14156 = FStar_BigInt.to_int_fs to_l  in
                 let uu____14158 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____14156 uu____14158  in
               FStar_Range.mk_range fn1 uu____14150 uu____14155  in
             let uu____14160 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____14160
         | uu____14173 -> FStar_Pervasives_Native.None)
    | uu____14199 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____14279)::(a1,uu____14281)::(a2,uu____14283)::[] ->
        let uu____14380 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____14380 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____14409 -> FStar_Pervasives_Native.None)
    | uu____14414 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____14481)::[] ->
        let uu____14514 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____14514 with
         | FStar_Pervasives_Native.Some r ->
             let uu____14524 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____14524
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____14541 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____14577  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____14625 =
      let uu____14665 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____14665)
       in
    let uu____14709 =
      let uu____14751 =
        let uu____14791 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____14791)
         in
      let uu____14841 =
        let uu____14883 =
          let uu____14923 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____14923)
           in
        let uu____14973 =
          let uu____15015 =
            let uu____15055 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____15055)
             in
          let uu____15105 =
            let uu____15147 =
              let uu____15187 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____15187)
               in
            let uu____15237 =
              let uu____15279 =
                let uu____15319 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____15331 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____15331)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____15372 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____15372)), uu____15319)
                 in
              let uu____15375 =
                let uu____15417 =
                  let uu____15457 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____15469 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____15469)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____15510 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____15510)), uu____15457)
                   in
                let uu____15513 =
                  let uu____15555 =
                    let uu____15595 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____15607 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____15607)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____15648 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____15648)), uu____15595)
                     in
                  let uu____15651 =
                    let uu____15693 =
                      let uu____15733 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____15745 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____15745)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____15786 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____15786)), uu____15733)
                       in
                    let uu____15789 =
                      let uu____15831 =
                        let uu____15871 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____15871)
                         in
                      let uu____15921 =
                        let uu____15963 =
                          let uu____16003 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____16003)
                           in
                        let uu____16049 =
                          let uu____16091 =
                            let uu____16131 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____16131)
                             in
                          let uu____16185 =
                            let uu____16227 =
                              let uu____16267 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____16267)
                               in
                            let uu____16321 =
                              let uu____16363 =
                                let uu____16403 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____16403)
                                 in
                              let uu____16441 =
                                let uu____16483 =
                                  let uu____16523 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____16523)
                                   in
                                let uu____16563 =
                                  let uu____16605 =
                                    let uu____16645 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____16645)
                                     in
                                  let uu____16685 =
                                    let uu____16727 =
                                      let uu____16767 =
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
                                           string_of_list'1), uu____16767)
                                       in
                                    let uu____16813 =
                                      let uu____16855 =
                                        let uu____16897 =
                                          let uu____16939 =
                                            let uu____16979 =
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
                                              uu____16979)
                                             in
                                          let uu____17033 =
                                            let uu____17075 =
                                              let uu____17117 =
                                                let uu____17157 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____17157)
                                                 in
                                              let uu____17197 =
                                                let uu____17239 =
                                                  let uu____17279 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____17279)
                                                   in
                                                let uu____17319 =
                                                  let uu____17361 =
                                                    let uu____17401 =
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
                                                      uu____17401)
                                                     in
                                                  let uu____17441 =
                                                    let uu____17483 =
                                                      let uu____17525 =
                                                        let uu____17567 =
                                                          let uu____17609 =
                                                            let uu____17651 =
                                                              let uu____17693
                                                                =
                                                                let uu____17733
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____17733,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____17778
                                                                =
                                                                let uu____17820
                                                                  =
                                                                  let uu____17860
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____17860,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____17820]
                                                                 in
                                                              uu____17693 ::
                                                                uu____17778
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____17651
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____17609
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____17567
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____17525
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____17483
                                                     in
                                                  uu____17361 :: uu____17441
                                                   in
                                                uu____17239 :: uu____17319
                                                 in
                                              uu____17117 :: uu____17197  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____17075
                                             in
                                          uu____16939 :: uu____17033  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____16897
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
                                                  let uu____18755 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____18755 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____18766 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____18766
                                                  y)))
                                        :: uu____16855
                                       in
                                    uu____16727 :: uu____16813  in
                                  uu____16605 :: uu____16685  in
                                uu____16483 :: uu____16563  in
                              uu____16363 :: uu____16441  in
                            uu____16227 :: uu____16321  in
                          uu____16091 :: uu____16185  in
                        uu____15963 :: uu____16049  in
                      uu____15831 :: uu____15921  in
                    uu____15693 :: uu____15789  in
                  uu____15555 :: uu____15651  in
                uu____15417 :: uu____15513  in
              uu____15279 :: uu____15375  in
            uu____15147 :: uu____15237  in
          uu____15015 :: uu____15105  in
        uu____14883 :: uu____14973  in
      uu____14751 :: uu____14841  in
    uu____14625 :: uu____14709  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____19628 =
        let uu____19633 =
          let uu____19634 = FStar_Syntax_Syntax.as_arg c  in [uu____19634]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____19633  in
      uu____19628 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____19803 =
                let uu____19843 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____19858 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____19879  ->
                       fun uu____19880  ->
                         match (uu____19879, uu____19880) with
                         | ((int_to_t1,x),(uu____19911,y)) ->
                             let uu____19939 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____19939)
                   in
                (uu____19843, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____19987  ->
                          fun uu____19988  ->
                            match (uu____19987, uu____19988) with
                            | ((int_to_t1,x),(uu____20023,y)) ->
                                let uu____20051 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____20051)),
                  uu____19858)
                 in
              let uu____20052 =
                let uu____20094 =
                  let uu____20134 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____20149 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____20170  ->
                         fun uu____20171  ->
                           match (uu____20170, uu____20171) with
                           | ((int_to_t1,x),(uu____20202,y)) ->
                               let uu____20230 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____20230)
                     in
                  (uu____20134, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____20278  ->
                            fun uu____20279  ->
                              match (uu____20278, uu____20279) with
                              | ((int_to_t1,x),(uu____20314,y)) ->
                                  let uu____20342 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____20342)),
                    uu____20149)
                   in
                let uu____20343 =
                  let uu____20385 =
                    let uu____20425 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____20440 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____20461  ->
                           fun uu____20462  ->
                             match (uu____20461, uu____20462) with
                             | ((int_to_t1,x),(uu____20493,y)) ->
                                 let uu____20521 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____20521)
                       in
                    (uu____20425, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____20569  ->
                              fun uu____20570  ->
                                match (uu____20569, uu____20570) with
                                | ((int_to_t1,x),(uu____20605,y)) ->
                                    let uu____20633 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____20633)),
                      uu____20440)
                     in
                  let uu____20634 =
                    let uu____20676 =
                      let uu____20716 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____20731 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____20748  ->
                             match uu____20748 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____20716, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____20807  ->
                                match uu____20807 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____20731)
                       in
                    [uu____20676]  in
                  uu____20385 :: uu____20634  in
                uu____20094 :: uu____20343  in
              uu____19803 :: uu____20052))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____21153 =
                let uu____21193 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____21208 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____21229  ->
                       fun uu____21230  ->
                         match (uu____21229, uu____21230) with
                         | ((int_to_t1,x),(uu____21261,y)) ->
                             let uu____21289 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____21289)
                   in
                (uu____21193, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____21337  ->
                          fun uu____21338  ->
                            match (uu____21337, uu____21338) with
                            | ((int_to_t1,x),(uu____21373,y)) ->
                                let uu____21401 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____21401)),
                  uu____21208)
                 in
              let uu____21402 =
                let uu____21444 =
                  let uu____21484 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____21499 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____21520  ->
                         fun uu____21521  ->
                           match (uu____21520, uu____21521) with
                           | ((int_to_t1,x),(uu____21552,y)) ->
                               let uu____21580 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____21580)
                     in
                  (uu____21484, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____21628  ->
                            fun uu____21629  ->
                              match (uu____21628, uu____21629) with
                              | ((int_to_t1,x),(uu____21664,y)) ->
                                  let uu____21692 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____21692)),
                    uu____21499)
                   in
                [uu____21444]  in
              uu____21153 :: uu____21402))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____21828 ->
          let uu____21830 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____21830
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____21964 =
                let uu____22004 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____22019 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____22040  ->
                       fun uu____22041  ->
                         match (uu____22040, uu____22041) with
                         | ((int_to_t1,x),(uu____22072,y)) ->
                             let uu____22100 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____22100)
                   in
                (uu____22004, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____22148  ->
                          fun uu____22149  ->
                            match (uu____22148, uu____22149) with
                            | ((int_to_t1,x),(uu____22184,y)) ->
                                let uu____22212 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____22212)),
                  uu____22019)
                 in
              let uu____22213 =
                let uu____22255 =
                  let uu____22295 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____22310 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____22331  ->
                         fun uu____22332  ->
                           match (uu____22331, uu____22332) with
                           | ((int_to_t1,x),(uu____22363,y)) ->
                               let uu____22391 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____22391)
                     in
                  (uu____22295, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____22439  ->
                            fun uu____22440  ->
                              match (uu____22439, uu____22440) with
                              | ((int_to_t1,x),(uu____22475,y)) ->
                                  let uu____22503 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____22503)),
                    uu____22310)
                   in
                let uu____22504 =
                  let uu____22546 =
                    let uu____22586 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____22601 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____22622  ->
                           fun uu____22623  ->
                             match (uu____22622, uu____22623) with
                             | ((int_to_t1,x),(uu____22654,y)) ->
                                 let uu____22682 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____22682)
                       in
                    (uu____22586, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____22730  ->
                              fun uu____22731  ->
                                match (uu____22730, uu____22731) with
                                | ((int_to_t1,x),(uu____22766,y)) ->
                                    let uu____22794 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____22794)),
                      uu____22601)
                     in
                  let uu____22795 =
                    let uu____22837 =
                      let uu____22877 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____22892 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____22910  ->
                             match uu____22910 with
                             | (int_to_t1,x) ->
                                 let uu____22926 =
                                   let uu____22927 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____22928 = mask m  in
                                   FStar_BigInt.logand_big_int uu____22927
                                     uu____22928
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____22926)
                         in
                      (uu____22877, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____22973  ->
                                match uu____22973 with
                                | (int_to_t1,x) ->
                                    let uu____22993 =
                                      let uu____22994 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____22995 = mask m  in
                                      FStar_BigInt.logand_big_int uu____22994
                                        uu____22995
                                       in
                                    int_as_bounded1 r int_to_t1 uu____22993)),
                        uu____22892)
                       in
                    let uu____22996 =
                      let uu____23038 =
                        let uu____23078 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____23093 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____23114  ->
                               fun uu____23115  ->
                                 match (uu____23114, uu____23115) with
                                 | ((int_to_t1,x),(uu____23146,y)) ->
                                     let uu____23174 =
                                       let uu____23175 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____23176 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____23175 uu____23176
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____23174)
                           in
                        (uu____23078, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____23224  ->
                                  fun uu____23225  ->
                                    match (uu____23224, uu____23225) with
                                    | ((int_to_t1,x),(uu____23260,y)) ->
                                        let uu____23288 =
                                          let uu____23289 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____23290 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____23289 uu____23290
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____23288)), uu____23093)
                         in
                      let uu____23291 =
                        let uu____23333 =
                          let uu____23373 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____23388 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____23409  ->
                                 fun uu____23410  ->
                                   match (uu____23409, uu____23410) with
                                   | ((int_to_t1,x),(uu____23441,y)) ->
                                       let uu____23469 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____23469)
                             in
                          (uu____23373, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____23517  ->
                                    fun uu____23518  ->
                                      match (uu____23517, uu____23518) with
                                      | ((int_to_t1,x),(uu____23553,y)) ->
                                          let uu____23581 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____23581)), uu____23388)
                           in
                        [uu____23333]  in
                      uu____23038 :: uu____23291  in
                    uu____22837 :: uu____22996  in
                  uu____22546 :: uu____22795  in
                uu____22255 :: uu____22504  in
              uu____21964 :: uu____22213))
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
    | (_typ,uu____24217)::(a1,uu____24219)::(a2,uu____24221)::[] ->
        let uu____24318 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____24318 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___876_24330 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___876_24330.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___876_24330.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___879_24344 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___879_24344.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___879_24344.FStar_Syntax_Syntax.vars)
                })
         | uu____24353 -> FStar_Pervasives_Native.None)
    | uu____24358 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____24408)::(t2,uu____24410)::(a1,uu____24412)::(a2,uu____24414)::[]
        ->
        let uu____24539 =
          let uu____24540 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____24541 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____24540 uu____24541  in
        (match uu____24539 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___902_24553 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___902_24553.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___902_24553.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___905_24567 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___905_24567.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___905_24567.FStar_Syntax_Syntax.vars)
                })
         | uu____24576 -> FStar_Pervasives_Native.None)
    | uu____24581 -> failwith "Unexpected number of arguments"  in
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
  fun uu____24708  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____24725 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____24725 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____24754 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____24754 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____24765  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____24836  ->
           fun uu____24837  ->
             match (uu____24836, uu____24837) with
             | ((uu____24863,t1),(uu____24865,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____24899  ->
         fun rest  ->
           match uu____24899 with
           | (nm,ms) ->
               let uu____24915 =
                 let uu____24917 =
                   let uu____24919 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____24919  in
                 FStar_Util.format2 "%sms --- %s\n" uu____24917 nm  in
               FStar_String.op_Hat uu____24915 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____25034 =
      let uu____25049 = FStar_ST.op_Bang plugins  in p :: uu____25049  in
    FStar_ST.op_Colon_Equals plugins uu____25034  in
  let retrieve uu____25189 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____25350  ->
    let uu____25351 = FStar_Options.no_plugins ()  in
    if uu____25351 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____25498 = FStar_Options.use_nbe ()  in
    if uu____25498
    then
      let uu___948_25527 = s  in
      {
        beta = (uu___948_25527.beta);
        iota = (uu___948_25527.iota);
        zeta = (uu___948_25527.zeta);
        weak = (uu___948_25527.weak);
        hnf = (uu___948_25527.hnf);
        primops = (uu___948_25527.primops);
        do_not_unfold_pure_lets = (uu___948_25527.do_not_unfold_pure_lets);
        unfold_until = (uu___948_25527.unfold_until);
        unfold_only = (uu___948_25527.unfold_only);
        unfold_fully = (uu___948_25527.unfold_fully);
        unfold_attr = (uu___948_25527.unfold_attr);
        unfold_tac = (uu___948_25527.unfold_tac);
        pure_subterms_within_computations =
          (uu___948_25527.pure_subterms_within_computations);
        simplify = (uu___948_25527.simplify);
        erase_universes = (uu___948_25527.erase_universes);
        allow_unbound_universes = (uu___948_25527.allow_unbound_universes);
        reify_ = (uu___948_25527.reify_);
        compress_uvars = (uu___948_25527.compress_uvars);
        no_full_norm = (uu___948_25527.no_full_norm);
        check_no_uvars = (uu___948_25527.check_no_uvars);
        unmeta = (uu___948_25527.unmeta);
        unascribe = (uu___948_25527.unascribe);
        in_full_norm_request = (uu___948_25527.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___948_25527.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___948_25527.for_extraction)
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
               (fun uu___0_25783  ->
                  match uu___0_25783 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding b ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only b]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____25789 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____25795 -> d  in
        let uu____25798 =
          let uu____25851 = to_fsteps s  in
          FStar_All.pipe_right uu____25851 add_nbe  in
        let uu____25956 =
          let uu____25975 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____25978 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____25981 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____25984 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____25987 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____25990 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____25993 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____25996 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____25999 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____25975;
            top = uu____25978;
            cfg = uu____25981;
            primop = uu____25984;
            unfolding = uu____25987;
            b380 = uu____25990;
            wpe = uu____25993;
            norm_delayed = uu____25996;
            print_normalized = uu____25999
          }  in
        let uu____26002 =
          let uu____26017 =
            let uu____26032 = retrieve_plugins ()  in
            FStar_List.append uu____26032 psteps  in
          add_steps built_in_primitive_steps uu____26017  in
        let uu____26059 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____26062 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____26062)
           in
        {
          steps = uu____25798;
          tcenv = e;
          debug = uu____25956;
          delta_level = d1;
          primitive_steps = uu____26002;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____26059;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 