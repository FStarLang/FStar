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
          let uu____61005 =
            let uu____61007 = f1 x  in FStar_String.op_Hat uu____61007 ")"
             in
          FStar_String.op_Hat "Some (" uu____61005
       in
    let b = FStar_Util.string_of_bool  in
    let uu____61018 =
      let uu____61022 = FStar_All.pipe_right f.beta b  in
      let uu____61026 =
        let uu____61030 = FStar_All.pipe_right f.iota b  in
        let uu____61034 =
          let uu____61038 = FStar_All.pipe_right f.zeta b  in
          let uu____61042 =
            let uu____61046 = FStar_All.pipe_right f.weak b  in
            let uu____61050 =
              let uu____61054 = FStar_All.pipe_right f.hnf b  in
              let uu____61058 =
                let uu____61062 = FStar_All.pipe_right f.primops b  in
                let uu____61066 =
                  let uu____61070 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____61074 =
                    let uu____61078 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____61083 =
                      let uu____61087 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____61101 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____61101
                                  (FStar_String.concat ", ")))
                         in
                      let uu____61111 =
                        let uu____61115 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____61129 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____61129
                                    (FStar_String.concat ", ")))
                           in
                        let uu____61139 =
                          let uu____61143 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____61157 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____61157
                                      (FStar_String.concat ", ")))
                             in
                          let uu____61167 =
                            let uu____61171 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____61175 =
                              let uu____61179 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____61183 =
                                let uu____61187 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____61191 =
                                  let uu____61195 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____61199 =
                                    let uu____61203 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____61207 =
                                      let uu____61211 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____61215 =
                                        let uu____61219 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____61223 =
                                          let uu____61227 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____61231 =
                                            let uu____61235 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____61239 =
                                              let uu____61243 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____61247 =
                                                let uu____61251 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____61255 =
                                                  let uu____61259 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____61263 =
                                                    let uu____61267 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____61267]  in
                                                  uu____61259 :: uu____61263
                                                   in
                                                uu____61251 :: uu____61255
                                                 in
                                              uu____61243 :: uu____61247  in
                                            uu____61235 :: uu____61239  in
                                          uu____61227 :: uu____61231  in
                                        uu____61219 :: uu____61223  in
                                      uu____61211 :: uu____61215  in
                                    uu____61203 :: uu____61207  in
                                  uu____61195 :: uu____61199  in
                                uu____61187 :: uu____61191  in
                              uu____61179 :: uu____61183  in
                            uu____61171 :: uu____61175  in
                          uu____61143 :: uu____61167  in
                        uu____61115 :: uu____61139  in
                      uu____61087 :: uu____61111  in
                    uu____61078 :: uu____61083  in
                  uu____61070 :: uu____61074  in
                uu____61062 :: uu____61066  in
              uu____61054 :: uu____61058  in
            uu____61046 :: uu____61050  in
          uu____61038 :: uu____61042  in
        uu____61030 :: uu____61034  in
      uu____61022 :: uu____61026  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____61018
  
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
          let uu___625_61337 = fs  in
          {
            beta = true;
            iota = (uu___625_61337.iota);
            zeta = (uu___625_61337.zeta);
            weak = (uu___625_61337.weak);
            hnf = (uu___625_61337.hnf);
            primops = (uu___625_61337.primops);
            do_not_unfold_pure_lets =
              (uu___625_61337.do_not_unfold_pure_lets);
            unfold_until = (uu___625_61337.unfold_until);
            unfold_only = (uu___625_61337.unfold_only);
            unfold_fully = (uu___625_61337.unfold_fully);
            unfold_attr = (uu___625_61337.unfold_attr);
            unfold_tac = (uu___625_61337.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_61337.pure_subterms_within_computations);
            simplify = (uu___625_61337.simplify);
            erase_universes = (uu___625_61337.erase_universes);
            allow_unbound_universes =
              (uu___625_61337.allow_unbound_universes);
            reify_ = (uu___625_61337.reify_);
            compress_uvars = (uu___625_61337.compress_uvars);
            no_full_norm = (uu___625_61337.no_full_norm);
            check_no_uvars = (uu___625_61337.check_no_uvars);
            unmeta = (uu___625_61337.unmeta);
            unascribe = (uu___625_61337.unascribe);
            in_full_norm_request = (uu___625_61337.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_61337.weakly_reduce_scrutinee);
            nbe_step = (uu___625_61337.nbe_step);
            for_extraction = (uu___625_61337.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_61339 = fs  in
          {
            beta = (uu___628_61339.beta);
            iota = true;
            zeta = (uu___628_61339.zeta);
            weak = (uu___628_61339.weak);
            hnf = (uu___628_61339.hnf);
            primops = (uu___628_61339.primops);
            do_not_unfold_pure_lets =
              (uu___628_61339.do_not_unfold_pure_lets);
            unfold_until = (uu___628_61339.unfold_until);
            unfold_only = (uu___628_61339.unfold_only);
            unfold_fully = (uu___628_61339.unfold_fully);
            unfold_attr = (uu___628_61339.unfold_attr);
            unfold_tac = (uu___628_61339.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_61339.pure_subterms_within_computations);
            simplify = (uu___628_61339.simplify);
            erase_universes = (uu___628_61339.erase_universes);
            allow_unbound_universes =
              (uu___628_61339.allow_unbound_universes);
            reify_ = (uu___628_61339.reify_);
            compress_uvars = (uu___628_61339.compress_uvars);
            no_full_norm = (uu___628_61339.no_full_norm);
            check_no_uvars = (uu___628_61339.check_no_uvars);
            unmeta = (uu___628_61339.unmeta);
            unascribe = (uu___628_61339.unascribe);
            in_full_norm_request = (uu___628_61339.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_61339.weakly_reduce_scrutinee);
            nbe_step = (uu___628_61339.nbe_step);
            for_extraction = (uu___628_61339.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_61341 = fs  in
          {
            beta = (uu___631_61341.beta);
            iota = (uu___631_61341.iota);
            zeta = true;
            weak = (uu___631_61341.weak);
            hnf = (uu___631_61341.hnf);
            primops = (uu___631_61341.primops);
            do_not_unfold_pure_lets =
              (uu___631_61341.do_not_unfold_pure_lets);
            unfold_until = (uu___631_61341.unfold_until);
            unfold_only = (uu___631_61341.unfold_only);
            unfold_fully = (uu___631_61341.unfold_fully);
            unfold_attr = (uu___631_61341.unfold_attr);
            unfold_tac = (uu___631_61341.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_61341.pure_subterms_within_computations);
            simplify = (uu___631_61341.simplify);
            erase_universes = (uu___631_61341.erase_universes);
            allow_unbound_universes =
              (uu___631_61341.allow_unbound_universes);
            reify_ = (uu___631_61341.reify_);
            compress_uvars = (uu___631_61341.compress_uvars);
            no_full_norm = (uu___631_61341.no_full_norm);
            check_no_uvars = (uu___631_61341.check_no_uvars);
            unmeta = (uu___631_61341.unmeta);
            unascribe = (uu___631_61341.unascribe);
            in_full_norm_request = (uu___631_61341.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_61341.weakly_reduce_scrutinee);
            nbe_step = (uu___631_61341.nbe_step);
            for_extraction = (uu___631_61341.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_61343 = fs  in
          {
            beta = false;
            iota = (uu___635_61343.iota);
            zeta = (uu___635_61343.zeta);
            weak = (uu___635_61343.weak);
            hnf = (uu___635_61343.hnf);
            primops = (uu___635_61343.primops);
            do_not_unfold_pure_lets =
              (uu___635_61343.do_not_unfold_pure_lets);
            unfold_until = (uu___635_61343.unfold_until);
            unfold_only = (uu___635_61343.unfold_only);
            unfold_fully = (uu___635_61343.unfold_fully);
            unfold_attr = (uu___635_61343.unfold_attr);
            unfold_tac = (uu___635_61343.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_61343.pure_subterms_within_computations);
            simplify = (uu___635_61343.simplify);
            erase_universes = (uu___635_61343.erase_universes);
            allow_unbound_universes =
              (uu___635_61343.allow_unbound_universes);
            reify_ = (uu___635_61343.reify_);
            compress_uvars = (uu___635_61343.compress_uvars);
            no_full_norm = (uu___635_61343.no_full_norm);
            check_no_uvars = (uu___635_61343.check_no_uvars);
            unmeta = (uu___635_61343.unmeta);
            unascribe = (uu___635_61343.unascribe);
            in_full_norm_request = (uu___635_61343.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_61343.weakly_reduce_scrutinee);
            nbe_step = (uu___635_61343.nbe_step);
            for_extraction = (uu___635_61343.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_61345 = fs  in
          {
            beta = (uu___639_61345.beta);
            iota = false;
            zeta = (uu___639_61345.zeta);
            weak = (uu___639_61345.weak);
            hnf = (uu___639_61345.hnf);
            primops = (uu___639_61345.primops);
            do_not_unfold_pure_lets =
              (uu___639_61345.do_not_unfold_pure_lets);
            unfold_until = (uu___639_61345.unfold_until);
            unfold_only = (uu___639_61345.unfold_only);
            unfold_fully = (uu___639_61345.unfold_fully);
            unfold_attr = (uu___639_61345.unfold_attr);
            unfold_tac = (uu___639_61345.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_61345.pure_subterms_within_computations);
            simplify = (uu___639_61345.simplify);
            erase_universes = (uu___639_61345.erase_universes);
            allow_unbound_universes =
              (uu___639_61345.allow_unbound_universes);
            reify_ = (uu___639_61345.reify_);
            compress_uvars = (uu___639_61345.compress_uvars);
            no_full_norm = (uu___639_61345.no_full_norm);
            check_no_uvars = (uu___639_61345.check_no_uvars);
            unmeta = (uu___639_61345.unmeta);
            unascribe = (uu___639_61345.unascribe);
            in_full_norm_request = (uu___639_61345.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_61345.weakly_reduce_scrutinee);
            nbe_step = (uu___639_61345.nbe_step);
            for_extraction = (uu___639_61345.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_61347 = fs  in
          {
            beta = (uu___643_61347.beta);
            iota = (uu___643_61347.iota);
            zeta = false;
            weak = (uu___643_61347.weak);
            hnf = (uu___643_61347.hnf);
            primops = (uu___643_61347.primops);
            do_not_unfold_pure_lets =
              (uu___643_61347.do_not_unfold_pure_lets);
            unfold_until = (uu___643_61347.unfold_until);
            unfold_only = (uu___643_61347.unfold_only);
            unfold_fully = (uu___643_61347.unfold_fully);
            unfold_attr = (uu___643_61347.unfold_attr);
            unfold_tac = (uu___643_61347.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_61347.pure_subterms_within_computations);
            simplify = (uu___643_61347.simplify);
            erase_universes = (uu___643_61347.erase_universes);
            allow_unbound_universes =
              (uu___643_61347.allow_unbound_universes);
            reify_ = (uu___643_61347.reify_);
            compress_uvars = (uu___643_61347.compress_uvars);
            no_full_norm = (uu___643_61347.no_full_norm);
            check_no_uvars = (uu___643_61347.check_no_uvars);
            unmeta = (uu___643_61347.unmeta);
            unascribe = (uu___643_61347.unascribe);
            in_full_norm_request = (uu___643_61347.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_61347.weakly_reduce_scrutinee);
            nbe_step = (uu___643_61347.nbe_step);
            for_extraction = (uu___643_61347.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____61349 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_61351 = fs  in
          {
            beta = (uu___648_61351.beta);
            iota = (uu___648_61351.iota);
            zeta = (uu___648_61351.zeta);
            weak = true;
            hnf = (uu___648_61351.hnf);
            primops = (uu___648_61351.primops);
            do_not_unfold_pure_lets =
              (uu___648_61351.do_not_unfold_pure_lets);
            unfold_until = (uu___648_61351.unfold_until);
            unfold_only = (uu___648_61351.unfold_only);
            unfold_fully = (uu___648_61351.unfold_fully);
            unfold_attr = (uu___648_61351.unfold_attr);
            unfold_tac = (uu___648_61351.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_61351.pure_subterms_within_computations);
            simplify = (uu___648_61351.simplify);
            erase_universes = (uu___648_61351.erase_universes);
            allow_unbound_universes =
              (uu___648_61351.allow_unbound_universes);
            reify_ = (uu___648_61351.reify_);
            compress_uvars = (uu___648_61351.compress_uvars);
            no_full_norm = (uu___648_61351.no_full_norm);
            check_no_uvars = (uu___648_61351.check_no_uvars);
            unmeta = (uu___648_61351.unmeta);
            unascribe = (uu___648_61351.unascribe);
            in_full_norm_request = (uu___648_61351.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_61351.weakly_reduce_scrutinee);
            nbe_step = (uu___648_61351.nbe_step);
            for_extraction = (uu___648_61351.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_61353 = fs  in
          {
            beta = (uu___651_61353.beta);
            iota = (uu___651_61353.iota);
            zeta = (uu___651_61353.zeta);
            weak = (uu___651_61353.weak);
            hnf = true;
            primops = (uu___651_61353.primops);
            do_not_unfold_pure_lets =
              (uu___651_61353.do_not_unfold_pure_lets);
            unfold_until = (uu___651_61353.unfold_until);
            unfold_only = (uu___651_61353.unfold_only);
            unfold_fully = (uu___651_61353.unfold_fully);
            unfold_attr = (uu___651_61353.unfold_attr);
            unfold_tac = (uu___651_61353.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_61353.pure_subterms_within_computations);
            simplify = (uu___651_61353.simplify);
            erase_universes = (uu___651_61353.erase_universes);
            allow_unbound_universes =
              (uu___651_61353.allow_unbound_universes);
            reify_ = (uu___651_61353.reify_);
            compress_uvars = (uu___651_61353.compress_uvars);
            no_full_norm = (uu___651_61353.no_full_norm);
            check_no_uvars = (uu___651_61353.check_no_uvars);
            unmeta = (uu___651_61353.unmeta);
            unascribe = (uu___651_61353.unascribe);
            in_full_norm_request = (uu___651_61353.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_61353.weakly_reduce_scrutinee);
            nbe_step = (uu___651_61353.nbe_step);
            for_extraction = (uu___651_61353.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_61355 = fs  in
          {
            beta = (uu___654_61355.beta);
            iota = (uu___654_61355.iota);
            zeta = (uu___654_61355.zeta);
            weak = (uu___654_61355.weak);
            hnf = (uu___654_61355.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_61355.do_not_unfold_pure_lets);
            unfold_until = (uu___654_61355.unfold_until);
            unfold_only = (uu___654_61355.unfold_only);
            unfold_fully = (uu___654_61355.unfold_fully);
            unfold_attr = (uu___654_61355.unfold_attr);
            unfold_tac = (uu___654_61355.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_61355.pure_subterms_within_computations);
            simplify = (uu___654_61355.simplify);
            erase_universes = (uu___654_61355.erase_universes);
            allow_unbound_universes =
              (uu___654_61355.allow_unbound_universes);
            reify_ = (uu___654_61355.reify_);
            compress_uvars = (uu___654_61355.compress_uvars);
            no_full_norm = (uu___654_61355.no_full_norm);
            check_no_uvars = (uu___654_61355.check_no_uvars);
            unmeta = (uu___654_61355.unmeta);
            unascribe = (uu___654_61355.unascribe);
            in_full_norm_request = (uu___654_61355.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_61355.weakly_reduce_scrutinee);
            nbe_step = (uu___654_61355.nbe_step);
            for_extraction = (uu___654_61355.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_61357 = fs  in
          {
            beta = (uu___659_61357.beta);
            iota = (uu___659_61357.iota);
            zeta = (uu___659_61357.zeta);
            weak = (uu___659_61357.weak);
            hnf = (uu___659_61357.hnf);
            primops = (uu___659_61357.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_61357.unfold_until);
            unfold_only = (uu___659_61357.unfold_only);
            unfold_fully = (uu___659_61357.unfold_fully);
            unfold_attr = (uu___659_61357.unfold_attr);
            unfold_tac = (uu___659_61357.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_61357.pure_subterms_within_computations);
            simplify = (uu___659_61357.simplify);
            erase_universes = (uu___659_61357.erase_universes);
            allow_unbound_universes =
              (uu___659_61357.allow_unbound_universes);
            reify_ = (uu___659_61357.reify_);
            compress_uvars = (uu___659_61357.compress_uvars);
            no_full_norm = (uu___659_61357.no_full_norm);
            check_no_uvars = (uu___659_61357.check_no_uvars);
            unmeta = (uu___659_61357.unmeta);
            unascribe = (uu___659_61357.unascribe);
            in_full_norm_request = (uu___659_61357.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_61357.weakly_reduce_scrutinee);
            nbe_step = (uu___659_61357.nbe_step);
            for_extraction = (uu___659_61357.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_61360 = fs  in
          {
            beta = (uu___663_61360.beta);
            iota = (uu___663_61360.iota);
            zeta = (uu___663_61360.zeta);
            weak = (uu___663_61360.weak);
            hnf = (uu___663_61360.hnf);
            primops = (uu___663_61360.primops);
            do_not_unfold_pure_lets =
              (uu___663_61360.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_61360.unfold_only);
            unfold_fully = (uu___663_61360.unfold_fully);
            unfold_attr = (uu___663_61360.unfold_attr);
            unfold_tac = (uu___663_61360.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_61360.pure_subterms_within_computations);
            simplify = (uu___663_61360.simplify);
            erase_universes = (uu___663_61360.erase_universes);
            allow_unbound_universes =
              (uu___663_61360.allow_unbound_universes);
            reify_ = (uu___663_61360.reify_);
            compress_uvars = (uu___663_61360.compress_uvars);
            no_full_norm = (uu___663_61360.no_full_norm);
            check_no_uvars = (uu___663_61360.check_no_uvars);
            unmeta = (uu___663_61360.unmeta);
            unascribe = (uu___663_61360.unascribe);
            in_full_norm_request = (uu___663_61360.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_61360.weakly_reduce_scrutinee);
            nbe_step = (uu___663_61360.nbe_step);
            for_extraction = (uu___663_61360.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_61364 = fs  in
          {
            beta = (uu___667_61364.beta);
            iota = (uu___667_61364.iota);
            zeta = (uu___667_61364.zeta);
            weak = (uu___667_61364.weak);
            hnf = (uu___667_61364.hnf);
            primops = (uu___667_61364.primops);
            do_not_unfold_pure_lets =
              (uu___667_61364.do_not_unfold_pure_lets);
            unfold_until = (uu___667_61364.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_61364.unfold_fully);
            unfold_attr = (uu___667_61364.unfold_attr);
            unfold_tac = (uu___667_61364.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_61364.pure_subterms_within_computations);
            simplify = (uu___667_61364.simplify);
            erase_universes = (uu___667_61364.erase_universes);
            allow_unbound_universes =
              (uu___667_61364.allow_unbound_universes);
            reify_ = (uu___667_61364.reify_);
            compress_uvars = (uu___667_61364.compress_uvars);
            no_full_norm = (uu___667_61364.no_full_norm);
            check_no_uvars = (uu___667_61364.check_no_uvars);
            unmeta = (uu___667_61364.unmeta);
            unascribe = (uu___667_61364.unascribe);
            in_full_norm_request = (uu___667_61364.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_61364.weakly_reduce_scrutinee);
            nbe_step = (uu___667_61364.nbe_step);
            for_extraction = (uu___667_61364.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_61370 = fs  in
          {
            beta = (uu___671_61370.beta);
            iota = (uu___671_61370.iota);
            zeta = (uu___671_61370.zeta);
            weak = (uu___671_61370.weak);
            hnf = (uu___671_61370.hnf);
            primops = (uu___671_61370.primops);
            do_not_unfold_pure_lets =
              (uu___671_61370.do_not_unfold_pure_lets);
            unfold_until = (uu___671_61370.unfold_until);
            unfold_only = (uu___671_61370.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_61370.unfold_attr);
            unfold_tac = (uu___671_61370.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_61370.pure_subterms_within_computations);
            simplify = (uu___671_61370.simplify);
            erase_universes = (uu___671_61370.erase_universes);
            allow_unbound_universes =
              (uu___671_61370.allow_unbound_universes);
            reify_ = (uu___671_61370.reify_);
            compress_uvars = (uu___671_61370.compress_uvars);
            no_full_norm = (uu___671_61370.no_full_norm);
            check_no_uvars = (uu___671_61370.check_no_uvars);
            unmeta = (uu___671_61370.unmeta);
            unascribe = (uu___671_61370.unascribe);
            in_full_norm_request = (uu___671_61370.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_61370.weakly_reduce_scrutinee);
            nbe_step = (uu___671_61370.nbe_step);
            for_extraction = (uu___671_61370.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_61376 = fs  in
          {
            beta = (uu___675_61376.beta);
            iota = (uu___675_61376.iota);
            zeta = (uu___675_61376.zeta);
            weak = (uu___675_61376.weak);
            hnf = (uu___675_61376.hnf);
            primops = (uu___675_61376.primops);
            do_not_unfold_pure_lets =
              (uu___675_61376.do_not_unfold_pure_lets);
            unfold_until = (uu___675_61376.unfold_until);
            unfold_only = (uu___675_61376.unfold_only);
            unfold_fully = (uu___675_61376.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_61376.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_61376.pure_subterms_within_computations);
            simplify = (uu___675_61376.simplify);
            erase_universes = (uu___675_61376.erase_universes);
            allow_unbound_universes =
              (uu___675_61376.allow_unbound_universes);
            reify_ = (uu___675_61376.reify_);
            compress_uvars = (uu___675_61376.compress_uvars);
            no_full_norm = (uu___675_61376.no_full_norm);
            check_no_uvars = (uu___675_61376.check_no_uvars);
            unmeta = (uu___675_61376.unmeta);
            unascribe = (uu___675_61376.unascribe);
            in_full_norm_request = (uu___675_61376.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_61376.weakly_reduce_scrutinee);
            nbe_step = (uu___675_61376.nbe_step);
            for_extraction = (uu___675_61376.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_61379 = fs  in
          {
            beta = (uu___678_61379.beta);
            iota = (uu___678_61379.iota);
            zeta = (uu___678_61379.zeta);
            weak = (uu___678_61379.weak);
            hnf = (uu___678_61379.hnf);
            primops = (uu___678_61379.primops);
            do_not_unfold_pure_lets =
              (uu___678_61379.do_not_unfold_pure_lets);
            unfold_until = (uu___678_61379.unfold_until);
            unfold_only = (uu___678_61379.unfold_only);
            unfold_fully = (uu___678_61379.unfold_fully);
            unfold_attr = (uu___678_61379.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_61379.pure_subterms_within_computations);
            simplify = (uu___678_61379.simplify);
            erase_universes = (uu___678_61379.erase_universes);
            allow_unbound_universes =
              (uu___678_61379.allow_unbound_universes);
            reify_ = (uu___678_61379.reify_);
            compress_uvars = (uu___678_61379.compress_uvars);
            no_full_norm = (uu___678_61379.no_full_norm);
            check_no_uvars = (uu___678_61379.check_no_uvars);
            unmeta = (uu___678_61379.unmeta);
            unascribe = (uu___678_61379.unascribe);
            in_full_norm_request = (uu___678_61379.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_61379.weakly_reduce_scrutinee);
            nbe_step = (uu___678_61379.nbe_step);
            for_extraction = (uu___678_61379.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_61381 = fs  in
          {
            beta = (uu___681_61381.beta);
            iota = (uu___681_61381.iota);
            zeta = (uu___681_61381.zeta);
            weak = (uu___681_61381.weak);
            hnf = (uu___681_61381.hnf);
            primops = (uu___681_61381.primops);
            do_not_unfold_pure_lets =
              (uu___681_61381.do_not_unfold_pure_lets);
            unfold_until = (uu___681_61381.unfold_until);
            unfold_only = (uu___681_61381.unfold_only);
            unfold_fully = (uu___681_61381.unfold_fully);
            unfold_attr = (uu___681_61381.unfold_attr);
            unfold_tac = (uu___681_61381.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_61381.simplify);
            erase_universes = (uu___681_61381.erase_universes);
            allow_unbound_universes =
              (uu___681_61381.allow_unbound_universes);
            reify_ = (uu___681_61381.reify_);
            compress_uvars = (uu___681_61381.compress_uvars);
            no_full_norm = (uu___681_61381.no_full_norm);
            check_no_uvars = (uu___681_61381.check_no_uvars);
            unmeta = (uu___681_61381.unmeta);
            unascribe = (uu___681_61381.unascribe);
            in_full_norm_request = (uu___681_61381.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_61381.weakly_reduce_scrutinee);
            nbe_step = (uu___681_61381.nbe_step);
            for_extraction = (uu___681_61381.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_61383 = fs  in
          {
            beta = (uu___684_61383.beta);
            iota = (uu___684_61383.iota);
            zeta = (uu___684_61383.zeta);
            weak = (uu___684_61383.weak);
            hnf = (uu___684_61383.hnf);
            primops = (uu___684_61383.primops);
            do_not_unfold_pure_lets =
              (uu___684_61383.do_not_unfold_pure_lets);
            unfold_until = (uu___684_61383.unfold_until);
            unfold_only = (uu___684_61383.unfold_only);
            unfold_fully = (uu___684_61383.unfold_fully);
            unfold_attr = (uu___684_61383.unfold_attr);
            unfold_tac = (uu___684_61383.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_61383.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_61383.erase_universes);
            allow_unbound_universes =
              (uu___684_61383.allow_unbound_universes);
            reify_ = (uu___684_61383.reify_);
            compress_uvars = (uu___684_61383.compress_uvars);
            no_full_norm = (uu___684_61383.no_full_norm);
            check_no_uvars = (uu___684_61383.check_no_uvars);
            unmeta = (uu___684_61383.unmeta);
            unascribe = (uu___684_61383.unascribe);
            in_full_norm_request = (uu___684_61383.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_61383.weakly_reduce_scrutinee);
            nbe_step = (uu___684_61383.nbe_step);
            for_extraction = (uu___684_61383.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_61385 = fs  in
          {
            beta = (uu___687_61385.beta);
            iota = (uu___687_61385.iota);
            zeta = (uu___687_61385.zeta);
            weak = (uu___687_61385.weak);
            hnf = (uu___687_61385.hnf);
            primops = (uu___687_61385.primops);
            do_not_unfold_pure_lets =
              (uu___687_61385.do_not_unfold_pure_lets);
            unfold_until = (uu___687_61385.unfold_until);
            unfold_only = (uu___687_61385.unfold_only);
            unfold_fully = (uu___687_61385.unfold_fully);
            unfold_attr = (uu___687_61385.unfold_attr);
            unfold_tac = (uu___687_61385.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_61385.pure_subterms_within_computations);
            simplify = (uu___687_61385.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_61385.allow_unbound_universes);
            reify_ = (uu___687_61385.reify_);
            compress_uvars = (uu___687_61385.compress_uvars);
            no_full_norm = (uu___687_61385.no_full_norm);
            check_no_uvars = (uu___687_61385.check_no_uvars);
            unmeta = (uu___687_61385.unmeta);
            unascribe = (uu___687_61385.unascribe);
            in_full_norm_request = (uu___687_61385.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_61385.weakly_reduce_scrutinee);
            nbe_step = (uu___687_61385.nbe_step);
            for_extraction = (uu___687_61385.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_61387 = fs  in
          {
            beta = (uu___690_61387.beta);
            iota = (uu___690_61387.iota);
            zeta = (uu___690_61387.zeta);
            weak = (uu___690_61387.weak);
            hnf = (uu___690_61387.hnf);
            primops = (uu___690_61387.primops);
            do_not_unfold_pure_lets =
              (uu___690_61387.do_not_unfold_pure_lets);
            unfold_until = (uu___690_61387.unfold_until);
            unfold_only = (uu___690_61387.unfold_only);
            unfold_fully = (uu___690_61387.unfold_fully);
            unfold_attr = (uu___690_61387.unfold_attr);
            unfold_tac = (uu___690_61387.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_61387.pure_subterms_within_computations);
            simplify = (uu___690_61387.simplify);
            erase_universes = (uu___690_61387.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_61387.reify_);
            compress_uvars = (uu___690_61387.compress_uvars);
            no_full_norm = (uu___690_61387.no_full_norm);
            check_no_uvars = (uu___690_61387.check_no_uvars);
            unmeta = (uu___690_61387.unmeta);
            unascribe = (uu___690_61387.unascribe);
            in_full_norm_request = (uu___690_61387.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_61387.weakly_reduce_scrutinee);
            nbe_step = (uu___690_61387.nbe_step);
            for_extraction = (uu___690_61387.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_61389 = fs  in
          {
            beta = (uu___693_61389.beta);
            iota = (uu___693_61389.iota);
            zeta = (uu___693_61389.zeta);
            weak = (uu___693_61389.weak);
            hnf = (uu___693_61389.hnf);
            primops = (uu___693_61389.primops);
            do_not_unfold_pure_lets =
              (uu___693_61389.do_not_unfold_pure_lets);
            unfold_until = (uu___693_61389.unfold_until);
            unfold_only = (uu___693_61389.unfold_only);
            unfold_fully = (uu___693_61389.unfold_fully);
            unfold_attr = (uu___693_61389.unfold_attr);
            unfold_tac = (uu___693_61389.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_61389.pure_subterms_within_computations);
            simplify = (uu___693_61389.simplify);
            erase_universes = (uu___693_61389.erase_universes);
            allow_unbound_universes =
              (uu___693_61389.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_61389.compress_uvars);
            no_full_norm = (uu___693_61389.no_full_norm);
            check_no_uvars = (uu___693_61389.check_no_uvars);
            unmeta = (uu___693_61389.unmeta);
            unascribe = (uu___693_61389.unascribe);
            in_full_norm_request = (uu___693_61389.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_61389.weakly_reduce_scrutinee);
            nbe_step = (uu___693_61389.nbe_step);
            for_extraction = (uu___693_61389.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_61391 = fs  in
          {
            beta = (uu___696_61391.beta);
            iota = (uu___696_61391.iota);
            zeta = (uu___696_61391.zeta);
            weak = (uu___696_61391.weak);
            hnf = (uu___696_61391.hnf);
            primops = (uu___696_61391.primops);
            do_not_unfold_pure_lets =
              (uu___696_61391.do_not_unfold_pure_lets);
            unfold_until = (uu___696_61391.unfold_until);
            unfold_only = (uu___696_61391.unfold_only);
            unfold_fully = (uu___696_61391.unfold_fully);
            unfold_attr = (uu___696_61391.unfold_attr);
            unfold_tac = (uu___696_61391.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_61391.pure_subterms_within_computations);
            simplify = (uu___696_61391.simplify);
            erase_universes = (uu___696_61391.erase_universes);
            allow_unbound_universes =
              (uu___696_61391.allow_unbound_universes);
            reify_ = (uu___696_61391.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_61391.no_full_norm);
            check_no_uvars = (uu___696_61391.check_no_uvars);
            unmeta = (uu___696_61391.unmeta);
            unascribe = (uu___696_61391.unascribe);
            in_full_norm_request = (uu___696_61391.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_61391.weakly_reduce_scrutinee);
            nbe_step = (uu___696_61391.nbe_step);
            for_extraction = (uu___696_61391.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_61393 = fs  in
          {
            beta = (uu___699_61393.beta);
            iota = (uu___699_61393.iota);
            zeta = (uu___699_61393.zeta);
            weak = (uu___699_61393.weak);
            hnf = (uu___699_61393.hnf);
            primops = (uu___699_61393.primops);
            do_not_unfold_pure_lets =
              (uu___699_61393.do_not_unfold_pure_lets);
            unfold_until = (uu___699_61393.unfold_until);
            unfold_only = (uu___699_61393.unfold_only);
            unfold_fully = (uu___699_61393.unfold_fully);
            unfold_attr = (uu___699_61393.unfold_attr);
            unfold_tac = (uu___699_61393.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_61393.pure_subterms_within_computations);
            simplify = (uu___699_61393.simplify);
            erase_universes = (uu___699_61393.erase_universes);
            allow_unbound_universes =
              (uu___699_61393.allow_unbound_universes);
            reify_ = (uu___699_61393.reify_);
            compress_uvars = (uu___699_61393.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_61393.check_no_uvars);
            unmeta = (uu___699_61393.unmeta);
            unascribe = (uu___699_61393.unascribe);
            in_full_norm_request = (uu___699_61393.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_61393.weakly_reduce_scrutinee);
            nbe_step = (uu___699_61393.nbe_step);
            for_extraction = (uu___699_61393.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_61395 = fs  in
          {
            beta = (uu___702_61395.beta);
            iota = (uu___702_61395.iota);
            zeta = (uu___702_61395.zeta);
            weak = (uu___702_61395.weak);
            hnf = (uu___702_61395.hnf);
            primops = (uu___702_61395.primops);
            do_not_unfold_pure_lets =
              (uu___702_61395.do_not_unfold_pure_lets);
            unfold_until = (uu___702_61395.unfold_until);
            unfold_only = (uu___702_61395.unfold_only);
            unfold_fully = (uu___702_61395.unfold_fully);
            unfold_attr = (uu___702_61395.unfold_attr);
            unfold_tac = (uu___702_61395.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_61395.pure_subterms_within_computations);
            simplify = (uu___702_61395.simplify);
            erase_universes = (uu___702_61395.erase_universes);
            allow_unbound_universes =
              (uu___702_61395.allow_unbound_universes);
            reify_ = (uu___702_61395.reify_);
            compress_uvars = (uu___702_61395.compress_uvars);
            no_full_norm = (uu___702_61395.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_61395.unmeta);
            unascribe = (uu___702_61395.unascribe);
            in_full_norm_request = (uu___702_61395.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_61395.weakly_reduce_scrutinee);
            nbe_step = (uu___702_61395.nbe_step);
            for_extraction = (uu___702_61395.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_61397 = fs  in
          {
            beta = (uu___705_61397.beta);
            iota = (uu___705_61397.iota);
            zeta = (uu___705_61397.zeta);
            weak = (uu___705_61397.weak);
            hnf = (uu___705_61397.hnf);
            primops = (uu___705_61397.primops);
            do_not_unfold_pure_lets =
              (uu___705_61397.do_not_unfold_pure_lets);
            unfold_until = (uu___705_61397.unfold_until);
            unfold_only = (uu___705_61397.unfold_only);
            unfold_fully = (uu___705_61397.unfold_fully);
            unfold_attr = (uu___705_61397.unfold_attr);
            unfold_tac = (uu___705_61397.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_61397.pure_subterms_within_computations);
            simplify = (uu___705_61397.simplify);
            erase_universes = (uu___705_61397.erase_universes);
            allow_unbound_universes =
              (uu___705_61397.allow_unbound_universes);
            reify_ = (uu___705_61397.reify_);
            compress_uvars = (uu___705_61397.compress_uvars);
            no_full_norm = (uu___705_61397.no_full_norm);
            check_no_uvars = (uu___705_61397.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_61397.unascribe);
            in_full_norm_request = (uu___705_61397.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_61397.weakly_reduce_scrutinee);
            nbe_step = (uu___705_61397.nbe_step);
            for_extraction = (uu___705_61397.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_61399 = fs  in
          {
            beta = (uu___708_61399.beta);
            iota = (uu___708_61399.iota);
            zeta = (uu___708_61399.zeta);
            weak = (uu___708_61399.weak);
            hnf = (uu___708_61399.hnf);
            primops = (uu___708_61399.primops);
            do_not_unfold_pure_lets =
              (uu___708_61399.do_not_unfold_pure_lets);
            unfold_until = (uu___708_61399.unfold_until);
            unfold_only = (uu___708_61399.unfold_only);
            unfold_fully = (uu___708_61399.unfold_fully);
            unfold_attr = (uu___708_61399.unfold_attr);
            unfold_tac = (uu___708_61399.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_61399.pure_subterms_within_computations);
            simplify = (uu___708_61399.simplify);
            erase_universes = (uu___708_61399.erase_universes);
            allow_unbound_universes =
              (uu___708_61399.allow_unbound_universes);
            reify_ = (uu___708_61399.reify_);
            compress_uvars = (uu___708_61399.compress_uvars);
            no_full_norm = (uu___708_61399.no_full_norm);
            check_no_uvars = (uu___708_61399.check_no_uvars);
            unmeta = (uu___708_61399.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_61399.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_61399.weakly_reduce_scrutinee);
            nbe_step = (uu___708_61399.nbe_step);
            for_extraction = (uu___708_61399.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_61401 = fs  in
          {
            beta = (uu___711_61401.beta);
            iota = (uu___711_61401.iota);
            zeta = (uu___711_61401.zeta);
            weak = (uu___711_61401.weak);
            hnf = (uu___711_61401.hnf);
            primops = (uu___711_61401.primops);
            do_not_unfold_pure_lets =
              (uu___711_61401.do_not_unfold_pure_lets);
            unfold_until = (uu___711_61401.unfold_until);
            unfold_only = (uu___711_61401.unfold_only);
            unfold_fully = (uu___711_61401.unfold_fully);
            unfold_attr = (uu___711_61401.unfold_attr);
            unfold_tac = (uu___711_61401.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_61401.pure_subterms_within_computations);
            simplify = (uu___711_61401.simplify);
            erase_universes = (uu___711_61401.erase_universes);
            allow_unbound_universes =
              (uu___711_61401.allow_unbound_universes);
            reify_ = (uu___711_61401.reify_);
            compress_uvars = (uu___711_61401.compress_uvars);
            no_full_norm = (uu___711_61401.no_full_norm);
            check_no_uvars = (uu___711_61401.check_no_uvars);
            unmeta = (uu___711_61401.unmeta);
            unascribe = (uu___711_61401.unascribe);
            in_full_norm_request = (uu___711_61401.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_61401.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_61401.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_61403 = fs  in
          {
            beta = (uu___714_61403.beta);
            iota = (uu___714_61403.iota);
            zeta = (uu___714_61403.zeta);
            weak = (uu___714_61403.weak);
            hnf = (uu___714_61403.hnf);
            primops = (uu___714_61403.primops);
            do_not_unfold_pure_lets =
              (uu___714_61403.do_not_unfold_pure_lets);
            unfold_until = (uu___714_61403.unfold_until);
            unfold_only = (uu___714_61403.unfold_only);
            unfold_fully = (uu___714_61403.unfold_fully);
            unfold_attr = (uu___714_61403.unfold_attr);
            unfold_tac = (uu___714_61403.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_61403.pure_subterms_within_computations);
            simplify = (uu___714_61403.simplify);
            erase_universes = (uu___714_61403.erase_universes);
            allow_unbound_universes =
              (uu___714_61403.allow_unbound_universes);
            reify_ = (uu___714_61403.reify_);
            compress_uvars = (uu___714_61403.compress_uvars);
            no_full_norm = (uu___714_61403.no_full_norm);
            check_no_uvars = (uu___714_61403.check_no_uvars);
            unmeta = (uu___714_61403.unmeta);
            unascribe = (uu___714_61403.unascribe);
            in_full_norm_request = (uu___714_61403.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_61403.weakly_reduce_scrutinee);
            nbe_step = (uu___714_61403.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____61461  -> [])
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
    let uu____62510 =
      let uu____62514 =
        let uu____62518 =
          let uu____62520 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____62520  in
        [uu____62518; "}"]  in
      "{" :: uu____62514  in
    FStar_String.concat "\n" uu____62510
  
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
             let uu____62568 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____62568 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____62584 = FStar_Util.psmap_empty ()  in add_steps uu____62584 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____62600 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____62600
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____62614 =
        let uu____62617 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____62617  in
      FStar_Util.is_some uu____62614
  
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
      let uu____62730 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____62730 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____62766 = FStar_Syntax_Embeddings.embed emb x  in
        uu____62766 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____62799 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____62799 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____62814 .
    'Auu____62814 ->
      FStar_Range.range -> 'Auu____62814 FStar_Syntax_Syntax.syntax
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
    let uu____62935 =
      let uu____62944 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____62944  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62935  in
  let arg_as_bounded_int1 uu____62974 =
    match uu____62974 with
    | (a,uu____62988) ->
        let uu____62999 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____62999 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____63043 =
               let uu____63058 =
                 let uu____63059 = FStar_Syntax_Subst.compress hd1  in
                 uu____63059.FStar_Syntax_Syntax.n  in
               (uu____63058, args)  in
             (match uu____63043 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____63080)::[]) when
                  let uu____63115 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____63115 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____63119 =
                    let uu____63120 = FStar_Syntax_Subst.compress arg1  in
                    uu____63120.FStar_Syntax_Syntax.n  in
                  (match uu____63119 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____63142 =
                         let uu____63147 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____63147)  in
                       FStar_Pervasives_Native.Some uu____63142
                   | uu____63152 -> FStar_Pervasives_Native.None)
              | uu____63157 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____63219 = f a  in FStar_Pervasives_Native.Some uu____63219
    | uu____63220 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____63276 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____63276
    | uu____63277 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____63344 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____63344  in
  let binary_op1 as_a f res n1 args =
    let uu____63426 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____63426  in
  let as_primitive_step is_strong uu____63481 =
    match uu____63481 with
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
           let uu____63589 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____63589)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____63631 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____63631)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____63672 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____63672)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____63725 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____63725)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____63778 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____63778)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____63931 =
          let uu____63940 = as_a a  in
          let uu____63943 = as_b b  in (uu____63940, uu____63943)  in
        (match uu____63931 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____63958 =
               let uu____63959 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____63959  in
             FStar_Pervasives_Native.Some uu____63958
         | uu____63960 -> FStar_Pervasives_Native.None)
    | uu____63969 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____63991 =
        let uu____63992 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____63992  in
      mk uu____63991 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____64006 =
      let uu____64009 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____64009  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____64006
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____64057 =
      let uu____64058 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____64058  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____64057  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____64144 = arg_as_string1 a1  in
        (match uu____64144 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____64153 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____64153 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____64171 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____64171
              | uu____64173 -> FStar_Pervasives_Native.None)
         | uu____64179 -> FStar_Pervasives_Native.None)
    | uu____64183 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____64264 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____64264 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____64280 = arg_as_string1 a2  in
             (match uu____64280 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____64293 =
                    let uu____64294 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____64294 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____64293
              | uu____64304 -> FStar_Pervasives_Native.None)
         | uu____64308 -> FStar_Pervasives_Native.None)
    | uu____64314 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____64352 =
          let uu____64366 = arg_as_string1 a1  in
          let uu____64370 = arg_as_int1 a2  in
          let uu____64373 = arg_as_int1 a3  in
          (uu____64366, uu____64370, uu____64373)  in
        (match uu____64352 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_64406  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____64411 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____64411) ()
              with | uu___1030_64414 -> FStar_Pervasives_Native.None)
         | uu____64417 -> FStar_Pervasives_Native.None)
    | uu____64431 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____64445 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____64445  in
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
        let uu____64524 =
          let uu____64534 = arg_as_string1 a1  in
          let uu____64538 = arg_as_int1 a2  in (uu____64534, uu____64538)  in
        (match uu____64524 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_64562  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____64567 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____64567) ()
              with | uu___1064_64570 -> FStar_Pervasives_Native.None)
         | uu____64573 -> FStar_Pervasives_Native.None)
    | uu____64583 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____64614 =
          let uu____64625 = arg_as_string1 a1  in
          let uu____64629 = arg_as_char1 a2  in (uu____64625, uu____64629)
           in
        (match uu____64614 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_64658  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____64662 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____64662) ()
              with | uu___1085_64664 -> FStar_Pervasives_Native.None)
         | uu____64667 -> FStar_Pervasives_Native.None)
    | uu____64678 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____64712 =
          let uu____64734 = arg_as_string1 fn  in
          let uu____64738 = arg_as_int1 from_line  in
          let uu____64741 = arg_as_int1 from_col  in
          let uu____64744 = arg_as_int1 to_line  in
          let uu____64747 = arg_as_int1 to_col  in
          (uu____64734, uu____64738, uu____64741, uu____64744, uu____64747)
           in
        (match uu____64712 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____64782 =
                 let uu____64783 = FStar_BigInt.to_int_fs from_l  in
                 let uu____64785 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____64783 uu____64785  in
               let uu____64787 =
                 let uu____64788 = FStar_BigInt.to_int_fs to_l  in
                 let uu____64790 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____64788 uu____64790  in
               FStar_Range.mk_range fn1 uu____64782 uu____64787  in
             let uu____64792 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64792
         | uu____64793 -> FStar_Pervasives_Native.None)
    | uu____64815 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____64859)::(a1,uu____64861)::(a2,uu____64863)::[] ->
        let uu____64920 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____64920 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____64929 -> FStar_Pervasives_Native.None)
    | uu____64930 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____64973)::[] ->
        let uu____64990 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____64990 with
         | FStar_Pervasives_Native.Some r ->
             let uu____64996 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64996
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____64997 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____65017  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____65051 =
      let uu____65081 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____65081)
       in
    let uu____65115 =
      let uu____65147 =
        let uu____65177 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____65177)
         in
      let uu____65217 =
        let uu____65249 =
          let uu____65279 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____65279)
           in
        let uu____65319 =
          let uu____65351 =
            let uu____65381 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____65381)
             in
          let uu____65421 =
            let uu____65453 =
              let uu____65483 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____65483)
               in
            let uu____65523 =
              let uu____65555 =
                let uu____65585 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____65597 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____65597)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____65628 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____65628)), uu____65585)
                 in
              let uu____65631 =
                let uu____65663 =
                  let uu____65693 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____65705 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____65705)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____65736 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____65736)), uu____65693)
                   in
                let uu____65739 =
                  let uu____65771 =
                    let uu____65801 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____65813 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____65813)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____65844 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____65844)), uu____65801)
                     in
                  let uu____65847 =
                    let uu____65879 =
                      let uu____65909 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____65921 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____65921)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____65952 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____65952)), uu____65909)
                       in
                    let uu____65955 =
                      let uu____65987 =
                        let uu____66017 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____66017)
                         in
                      let uu____66057 =
                        let uu____66089 =
                          let uu____66119 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____66119)
                           in
                        let uu____66155 =
                          let uu____66187 =
                            let uu____66217 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____66217)
                             in
                          let uu____66261 =
                            let uu____66293 =
                              let uu____66323 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____66323)
                               in
                            let uu____66367 =
                              let uu____66399 =
                                let uu____66429 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____66429)
                                 in
                              let uu____66457 =
                                let uu____66489 =
                                  let uu____66519 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____66519)
                                   in
                                let uu____66549 =
                                  let uu____66581 =
                                    let uu____66611 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____66611)
                                     in
                                  let uu____66641 =
                                    let uu____66673 =
                                      let uu____66703 =
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
                                           string_of_list'1), uu____66703)
                                       in
                                    let uu____66739 =
                                      let uu____66771 =
                                        let uu____66803 =
                                          let uu____66835 =
                                            let uu____66865 =
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
                                              uu____66865)
                                             in
                                          let uu____66909 =
                                            let uu____66941 =
                                              let uu____66973 =
                                                let uu____67003 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____67003)
                                                 in
                                              let uu____67033 =
                                                let uu____67065 =
                                                  let uu____67095 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____67095)
                                                   in
                                                let uu____67125 =
                                                  let uu____67157 =
                                                    let uu____67187 =
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
                                                      uu____67187)
                                                     in
                                                  let uu____67217 =
                                                    let uu____67249 =
                                                      let uu____67281 =
                                                        let uu____67313 =
                                                          let uu____67345 =
                                                            let uu____67377 =
                                                              let uu____67409
                                                                =
                                                                let uu____67439
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____67439,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____67466
                                                                =
                                                                let uu____67498
                                                                  =
                                                                  let uu____67528
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____67528,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____67498]
                                                                 in
                                                              uu____67409 ::
                                                                uu____67466
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____67377
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____67345
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____67313
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____67281
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____67249
                                                     in
                                                  uu____67157 :: uu____67217
                                                   in
                                                uu____67065 :: uu____67125
                                                 in
                                              uu____66973 :: uu____67033  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____66941
                                             in
                                          uu____66835 :: uu____66909  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____66803
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
                                                  let uu____68175 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____68175 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____68186 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____68186
                                                  y)))
                                        :: uu____66771
                                       in
                                    uu____66673 :: uu____66739  in
                                  uu____66581 :: uu____66641  in
                                uu____66489 :: uu____66549  in
                              uu____66399 :: uu____66457  in
                            uu____66293 :: uu____66367  in
                          uu____66187 :: uu____66261  in
                        uu____66089 :: uu____66155  in
                      uu____65987 :: uu____66057  in
                    uu____65879 :: uu____65955  in
                  uu____65771 :: uu____65847  in
                uu____65663 :: uu____65739  in
              uu____65555 :: uu____65631  in
            uu____65453 :: uu____65523  in
          uu____65351 :: uu____65421  in
        uu____65249 :: uu____65319  in
      uu____65147 :: uu____65217  in
    uu____65051 :: uu____65115  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____68822 =
        let uu____68827 =
          let uu____68828 = FStar_Syntax_Syntax.as_arg c  in [uu____68828]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____68827  in
      uu____68822 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____68955 =
                let uu____68985 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____68992 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69010  ->
                       fun uu____69011  ->
                         match (uu____69010, uu____69011) with
                         | ((int_to_t1,x),(uu____69030,y)) ->
                             let uu____69040 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69040)
                   in
                (uu____68985, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69075  ->
                          fun uu____69076  ->
                            match (uu____69075, uu____69076) with
                            | ((int_to_t1,x),(uu____69095,y)) ->
                                let uu____69105 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69105)),
                  uu____68992)
                 in
              let uu____69106 =
                let uu____69138 =
                  let uu____69168 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____69175 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____69193  ->
                         fun uu____69194  ->
                           match (uu____69193, uu____69194) with
                           | ((int_to_t1,x),(uu____69213,y)) ->
                               let uu____69223 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____69223)
                     in
                  (uu____69168, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____69258  ->
                            fun uu____69259  ->
                              match (uu____69258, uu____69259) with
                              | ((int_to_t1,x),(uu____69278,y)) ->
                                  let uu____69288 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____69288)),
                    uu____69175)
                   in
                let uu____69289 =
                  let uu____69321 =
                    let uu____69351 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____69358 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____69376  ->
                           fun uu____69377  ->
                             match (uu____69376, uu____69377) with
                             | ((int_to_t1,x),(uu____69396,y)) ->
                                 let uu____69406 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____69406)
                       in
                    (uu____69351, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____69441  ->
                              fun uu____69442  ->
                                match (uu____69441, uu____69442) with
                                | ((int_to_t1,x),(uu____69461,y)) ->
                                    let uu____69471 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____69471)),
                      uu____69358)
                     in
                  let uu____69472 =
                    let uu____69504 =
                      let uu____69534 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____69541 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____69555  ->
                             match uu____69555 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____69534, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____69592  ->
                                match uu____69592 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____69541)
                       in
                    [uu____69504]  in
                  uu____69321 :: uu____69472  in
                uu____69138 :: uu____69289  in
              uu____68955 :: uu____69106))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____69845 =
                let uu____69875 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____69882 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69900  ->
                       fun uu____69901  ->
                         match (uu____69900, uu____69901) with
                         | ((int_to_t1,x),(uu____69920,y)) ->
                             let uu____69930 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69930)
                   in
                (uu____69875, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69965  ->
                          fun uu____69966  ->
                            match (uu____69965, uu____69966) with
                            | ((int_to_t1,x),(uu____69985,y)) ->
                                let uu____69995 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69995)),
                  uu____69882)
                 in
              let uu____69996 =
                let uu____70028 =
                  let uu____70058 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____70065 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____70083  ->
                         fun uu____70084  ->
                           match (uu____70083, uu____70084) with
                           | ((int_to_t1,x),(uu____70103,y)) ->
                               let uu____70113 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____70113)
                     in
                  (uu____70058, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____70148  ->
                            fun uu____70149  ->
                              match (uu____70148, uu____70149) with
                              | ((int_to_t1,x),(uu____70168,y)) ->
                                  let uu____70178 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____70178)),
                    uu____70065)
                   in
                [uu____70028]  in
              uu____69845 :: uu____69996))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____70284 ->
          let uu____70286 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____70286
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____70390 =
                let uu____70420 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____70427 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____70445  ->
                       fun uu____70446  ->
                         match (uu____70445, uu____70446) with
                         | ((int_to_t1,x),(uu____70465,y)) ->
                             let uu____70475 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____70475)
                   in
                (uu____70420, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____70510  ->
                          fun uu____70511  ->
                            match (uu____70510, uu____70511) with
                            | ((int_to_t1,x),(uu____70530,y)) ->
                                let uu____70540 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____70540)),
                  uu____70427)
                 in
              let uu____70541 =
                let uu____70573 =
                  let uu____70603 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____70610 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____70628  ->
                         fun uu____70629  ->
                           match (uu____70628, uu____70629) with
                           | ((int_to_t1,x),(uu____70648,y)) ->
                               let uu____70658 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____70658)
                     in
                  (uu____70603, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____70693  ->
                            fun uu____70694  ->
                              match (uu____70693, uu____70694) with
                              | ((int_to_t1,x),(uu____70713,y)) ->
                                  let uu____70723 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____70723)),
                    uu____70610)
                   in
                let uu____70724 =
                  let uu____70756 =
                    let uu____70786 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____70793 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____70811  ->
                           fun uu____70812  ->
                             match (uu____70811, uu____70812) with
                             | ((int_to_t1,x),(uu____70831,y)) ->
                                 let uu____70841 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70841)
                       in
                    (uu____70786, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____70876  ->
                              fun uu____70877  ->
                                match (uu____70876, uu____70877) with
                                | ((int_to_t1,x),(uu____70896,y)) ->
                                    let uu____70906 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____70906)),
                      uu____70793)
                     in
                  let uu____70907 =
                    let uu____70939 =
                      let uu____70969 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____70976 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____70991  ->
                             match uu____70991 with
                             | (int_to_t1,x) ->
                                 let uu____70998 =
                                   let uu____70999 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____71000 = mask m  in
                                   FStar_BigInt.logand_big_int uu____70999
                                     uu____71000
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70998)
                         in
                      (uu____70969, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____71032  ->
                                match uu____71032 with
                                | (int_to_t1,x) ->
                                    let uu____71039 =
                                      let uu____71040 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____71041 = mask m  in
                                      FStar_BigInt.logand_big_int uu____71040
                                        uu____71041
                                       in
                                    int_as_bounded1 r int_to_t1 uu____71039)),
                        uu____70976)
                       in
                    let uu____71042 =
                      let uu____71074 =
                        let uu____71104 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____71111 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____71129  ->
                               fun uu____71130  ->
                                 match (uu____71129, uu____71130) with
                                 | ((int_to_t1,x),(uu____71149,y)) ->
                                     let uu____71159 =
                                       let uu____71160 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____71161 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____71160 uu____71161
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____71159)
                           in
                        (uu____71104, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____71196  ->
                                  fun uu____71197  ->
                                    match (uu____71196, uu____71197) with
                                    | ((int_to_t1,x),(uu____71216,y)) ->
                                        let uu____71226 =
                                          let uu____71227 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____71228 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____71227 uu____71228
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____71226)), uu____71111)
                         in
                      let uu____71229 =
                        let uu____71261 =
                          let uu____71291 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____71298 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____71316  ->
                                 fun uu____71317  ->
                                   match (uu____71316, uu____71317) with
                                   | ((int_to_t1,x),(uu____71336,y)) ->
                                       let uu____71346 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____71346)
                             in
                          (uu____71291, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____71381  ->
                                    fun uu____71382  ->
                                      match (uu____71381, uu____71382) with
                                      | ((int_to_t1,x),(uu____71401,y)) ->
                                          let uu____71411 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____71411)), uu____71298)
                           in
                        [uu____71261]  in
                      uu____71074 :: uu____71229  in
                    uu____70939 :: uu____71042  in
                  uu____70756 :: uu____70907  in
                uu____70573 :: uu____70724  in
              uu____70390 :: uu____70541))
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
    | (_typ,uu____71803)::(a1,uu____71805)::(a2,uu____71807)::[] ->
        let uu____71864 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____71864 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1406_71868 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1406_71868.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1406_71868.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1409_71870 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1409_71870.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1409_71870.FStar_Syntax_Syntax.vars)
                })
         | uu____71871 -> FStar_Pervasives_Native.None)
    | uu____71872 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____71902)::(t2,uu____71904)::(a1,uu____71906)::(a2,uu____71908)::[]
        ->
        let uu____71981 =
          let uu____71982 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____71983 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____71982 uu____71983  in
        (match uu____71981 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1432_71987 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1432_71987.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1432_71987.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1435_71989 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1435_71989.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1435_71989.FStar_Syntax_Syntax.vars)
                })
         | uu____71990 -> FStar_Pervasives_Native.None)
    | uu____71991 -> failwith "Unexpected number of arguments"  in
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
  fun uu____72022  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____72039 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____72039 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____72068 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____72068 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____72079  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____72150  ->
           fun uu____72151  ->
             match (uu____72150, uu____72151) with
             | ((uu____72177,t1),(uu____72179,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____72213  ->
         fun rest  ->
           match uu____72213 with
           | (nm,ms) ->
               let uu____72229 =
                 let uu____72231 =
                   let uu____72233 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____72233  in
                 FStar_Util.format2 "%sms --- %s\n" uu____72231 nm  in
               FStar_String.op_Hat uu____72229 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____72264 =
      let uu____72267 = FStar_ST.op_Bang plugins  in p :: uu____72267  in
    FStar_ST.op_Colon_Equals plugins uu____72264  in
  let retrieve uu____72323 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____72376  ->
    let uu____72377 = FStar_Options.no_plugins ()  in
    if uu____72377 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____72398 = FStar_Options.use_nbe ()  in
    if uu____72398
    then
      let uu___1478_72401 = s  in
      {
        beta = (uu___1478_72401.beta);
        iota = (uu___1478_72401.iota);
        zeta = (uu___1478_72401.zeta);
        weak = (uu___1478_72401.weak);
        hnf = (uu___1478_72401.hnf);
        primops = (uu___1478_72401.primops);
        do_not_unfold_pure_lets = (uu___1478_72401.do_not_unfold_pure_lets);
        unfold_until = (uu___1478_72401.unfold_until);
        unfold_only = (uu___1478_72401.unfold_only);
        unfold_fully = (uu___1478_72401.unfold_fully);
        unfold_attr = (uu___1478_72401.unfold_attr);
        unfold_tac = (uu___1478_72401.unfold_tac);
        pure_subterms_within_computations =
          (uu___1478_72401.pure_subterms_within_computations);
        simplify = (uu___1478_72401.simplify);
        erase_universes = (uu___1478_72401.erase_universes);
        allow_unbound_universes = (uu___1478_72401.allow_unbound_universes);
        reify_ = (uu___1478_72401.reify_);
        compress_uvars = (uu___1478_72401.compress_uvars);
        no_full_norm = (uu___1478_72401.no_full_norm);
        check_no_uvars = (uu___1478_72401.check_no_uvars);
        unmeta = (uu___1478_72401.unmeta);
        unascribe = (uu___1478_72401.unascribe);
        in_full_norm_request = (uu___1478_72401.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1478_72401.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1478_72401.for_extraction)
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
               (fun uu___531_72438  ->
                  match uu___531_72438 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____72442 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____72448 -> d  in
        let uu____72451 =
          let uu____72452 = to_fsteps s  in
          FStar_All.pipe_right uu____72452 add_nbe  in
        let uu____72453 =
          let uu____72454 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____72457 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____72460 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____72463 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____72466 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____72469 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____72472 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____72475 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____72478 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____72454;
            top = uu____72457;
            cfg = uu____72460;
            primop = uu____72463;
            unfolding = uu____72466;
            b380 = uu____72469;
            wpe = uu____72472;
            norm_delayed = uu____72475;
            print_normalized = uu____72478
          }  in
        let uu____72481 =
          let uu____72484 =
            let uu____72487 = retrieve_plugins ()  in
            FStar_List.append uu____72487 psteps  in
          add_steps built_in_primitive_steps uu____72484  in
        let uu____72490 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____72493 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____72493)
           in
        {
          steps = uu____72451;
          tcenv = e;
          debug = uu____72453;
          delta_level = d1;
          primitive_steps = uu____72481;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____72490;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 