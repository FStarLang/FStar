open Prims
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun a  -> fun b  -> if a > b then a else b 
let map_rev : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____70 = let uu____73 = f x  in uu____73 :: acc  in
            aux xs uu____70
         in
      aux l []
  
let map_rev_append :
  'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list -> 'b Prims.list =
  fun f  ->
    fun l1  ->
      fun l2  ->
        let rec aux l acc =
          match l with
          | [] -> l2
          | x::xs ->
              let uu____143 = let uu____146 = f x  in uu____146 :: acc  in
              aux xs uu____143
           in
        aux l1 l2
  
let rec map_append :
  'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list -> 'b Prims.list =
  fun f  ->
    fun l1  ->
      fun l2  ->
        match l1 with
        | [] -> l2
        | x::xs ->
            let uu____195 = f x  in
            let uu____196 = map_append f xs l2  in uu____195 :: uu____196
  
let rec drop : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p  ->
    fun l  ->
      match l with
      | [] -> []
      | x::xs ->
          let uu____232 = p x  in if uu____232 then x :: xs else drop p xs
  
let (debug : FStar_TypeChecker_Cfg.cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____251 =
        let uu____252 = FStar_TypeChecker_Cfg.cfg_env cfg  in
        FStar_TypeChecker_Env.debug uu____252 (FStar_Options.Other "NBE")  in
      if uu____251 then f () else ()
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____259 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____259
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____276 = FStar_Syntax_Print.sigelt_to_string_short v1  in
             FStar_Util.print2 "%s -> %%s\n" k uu____276) ()
  
let (pickBranch :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_Syntax_Syntax.branch Prims.list ->
        (FStar_Syntax_Syntax.term,FStar_TypeChecker_NBETerm.t Prims.list)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun scrut  ->
      fun branches  ->
        let rec pickBranch_aux scrut1 branches1 branches0 =
          let rec matches_pat scrutinee p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_var bv -> FStar_Util.Inl [scrutinee]
            | FStar_Syntax_Syntax.Pat_wild bv -> FStar_Util.Inl [scrutinee]
            | FStar_Syntax_Syntax.Pat_dot_term uu____381 -> FStar_Util.Inl []
            | FStar_Syntax_Syntax.Pat_constant s ->
                let matches_const c s1 =
                  debug cfg
                    (fun uu____406  ->
                       let uu____407 =
                         FStar_TypeChecker_NBETerm.t_to_string c  in
                       let uu____408 = FStar_Syntax_Print.const_to_string s1
                          in
                       FStar_Util.print2
                         "Testing term %s against pattern %s\n" uu____407
                         uu____408);
                  (match c with
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Unit ) ->
                       s1 = FStar_Const.Const_unit
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Bool b) ->
                       (match s1 with
                        | FStar_Const.Const_bool p1 -> b = p1
                        | uu____411 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Int i) ->
                       (match s1 with
                        | FStar_Const.Const_int
                            (p1,FStar_Pervasives_Native.None ) ->
                            let uu____424 = FStar_BigInt.big_int_of_string p1
                               in
                            i = uu____424
                        | uu____425 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.String (st,uu____427)) ->
                       (match s1 with
                        | FStar_Const.Const_string (p1,uu____429) -> st = p1
                        | uu____430 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Char c1) ->
                       (match s1 with
                        | FStar_Const.Const_char p1 -> c1 = p1
                        | uu____436 -> false)
                   | uu____437 -> false)
                   in
                let uu____438 = matches_const scrutinee s  in
                if uu____438 then FStar_Util.Inl [] else FStar_Util.Inr false
            | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                let rec matches_args out a p1 =
                  match (a, p1) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t,uu____559)::rest_a,(p2,uu____562)::rest_p) ->
                      let uu____596 = matches_pat t p2  in
                      (match uu____596 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____621 -> FStar_Util.Inr false  in
                (match scrutinee with
                 | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev) ->
                     let uu____669 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                     if uu____669
                     then matches_args [] (FStar_List.rev args_rev) arg_pats
                     else FStar_Util.Inr false
                 | uu____685 -> FStar_Util.Inr true)
             in
          match branches1 with
          | [] -> failwith "Branch not found"
          | (p,_wopt,e)::branches2 ->
              let uu____768 = matches_pat scrut1 p  in
              (match uu____768 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____791  ->
                         let uu____792 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____792);
                    FStar_Pervasives_Native.Some (e, matches))
               | FStar_Util.Inr (false ) ->
                   pickBranch_aux scrut1 branches2 branches0
               | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
           in
        pickBranch_aux scrut branches branches
  
let rec test_args :
  'Auu____818 .
    (FStar_TypeChecker_NBETerm.t,'Auu____818) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.int -> Prims.bool
  =
  fun ts  ->
    fun cnt  ->
      match ts with
      | [] -> cnt <= (Prims.parse_int "0")
      | t::ts1 ->
          (let uu____863 =
             FStar_TypeChecker_NBETerm.isAccu (FStar_Pervasives_Native.fst t)
              in
           Prims.op_Negation uu____863) &&
            (test_args ts1 (cnt - (Prims.parse_int "1")))
  
let rec (count_abstractions : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    let uu____869 =
      let uu____870 = FStar_Syntax_Subst.compress t  in
      uu____870.FStar_Syntax_Syntax.n  in
    match uu____869 with
    | FStar_Syntax_Syntax.Tm_delayed uu____873 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____896 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_name uu____897 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_fvar uu____898 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_constant uu____899 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_type uu____900 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_arrow uu____901 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uvar uu____916 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_refine uu____929 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_unknown  -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____937) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____948) ->
        let uu____973 = count_abstractions body  in
        (FStar_List.length xs) + uu____973
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1006 =
          let uu____1007 = count_abstractions head1  in
          uu____1007 - (FStar_List.length args)  in
        max uu____1006 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____1068,uu____1069,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____1118,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1137) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1143,uu____1144) ->
        count_abstractions t1
    | uu____1185 -> (Prims.parse_int "0")
  
let (find_sigelt_in_gamma :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.env ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lid  ->
        let mapper uu____1230 =
          match uu____1230 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1313  ->
                         let uu____1314 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1314);
                    FStar_Pervasives_Native.Some elt)
               | uu____1315 -> FStar_Pervasives_Native.None)
           in
        let uu____1330 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1330 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1374 -> true
    | uu____1375 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | uu____1382 -> failwith "Not a universe"
  
let (is_constr_fv : FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun fvar1  ->
    fvar1.FStar_Syntax_Syntax.fv_qual =
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (is_constr : FStar_TypeChecker_Env.qninfo -> Prims.bool) =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (uu____1395,uu____1396,uu____1397,uu____1398,uu____1399,uu____1400);
            FStar_Syntax_Syntax.sigrng = uu____1401;
            FStar_Syntax_Syntax.sigquals = uu____1402;
            FStar_Syntax_Syntax.sigmeta = uu____1403;
            FStar_Syntax_Syntax.sigattrs = uu____1404;_},uu____1405),uu____1406)
        -> true
    | uu____1491 -> false
  
let (translate_univ :
  FStar_TypeChecker_NBETerm.t Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_NBETerm.t)
  =
  fun bs  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar i ->
            let u' = FStar_List.nth bs i  in un_univ u'
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1516 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1516
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1520 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1520
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____1523 -> u2
        | FStar_Syntax_Syntax.U_unif uu____1524 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2  in
      let uu____1533 = aux u  in FStar_TypeChecker_NBETerm.Univ uu____1533
  
let (make_rec_env :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_TypeChecker_NBETerm.t Prims.list)
  =
  fun lbs  ->
    fun bs  ->
      let rec aux lbs1 lbs0 bs1 bs0 =
        match lbs1 with
        | [] -> bs1
        | lb::lbs' ->
            let uu____1601 =
              let uu____1604 =
                FStar_TypeChecker_NBETerm.mkAccuRec lb lbs0 bs0  in
              uu____1604 :: bs1  in
            aux lbs' lbs0 uu____1601 bs0
         in
      aux lbs lbs bs bs
  
let (find_let :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.letbinding FStar_Pervasives_Native.option)
  =
  fun lbs  ->
    fun fvar1  ->
      FStar_Util.find_map lbs
        (fun lb  ->
           match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inl uu____1626 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1630 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1630
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
  
let rec (iapp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun f  ->
      fun args  ->
        debug cfg
          (fun uu____1653  ->
             let uu____1654 = FStar_TypeChecker_NBETerm.t_to_string f  in
             let uu____1655 = FStar_TypeChecker_NBETerm.args_to_string args
                in
             FStar_Util.print2 "App : %s @ %s\n" uu____1654 uu____1655);
        (match f with
         | FStar_TypeChecker_NBETerm.Lam (f1,targs,n1) ->
             let m = FStar_List.length args  in
             if m < n1
             then
               let uu____1702 = FStar_List.splitAt m targs  in
               (match uu____1702 with
                | (uu____1742,targs') ->
                    FStar_TypeChecker_NBETerm.Lam
                      (((fun l  ->
                           let uu____1807 =
                             map_append FStar_Pervasives_Native.fst args l
                              in
                           f1 uu____1807)), targs', (n1 - m)))
             else
               if m = n1
               then
                 (let uu____1823 =
                    FStar_List.map FStar_Pervasives_Native.fst args  in
                  f1 uu____1823)
               else
                 (let uu____1831 = FStar_List.splitAt n1 args  in
                  match uu____1831 with
                  | (args1,args') ->
                      let uu____1886 =
                        let uu____1887 =
                          FStar_List.map FStar_Pervasives_Native.fst args1
                           in
                        f1 uu____1887  in
                      iapp cfg uu____1886 args')
         | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
             FStar_TypeChecker_NBETerm.Accu
               (a, (FStar_List.rev_append args ts))
         | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
             let rec aux args1 us1 ts1 =
               match args1 with
               | (FStar_TypeChecker_NBETerm.Univ u,uu____2018)::args2 ->
                   aux args2 (u :: us1) ts1
               | a::args2 -> aux args2 us1 (a :: ts1)
               | [] -> (us1, ts1)  in
             let uu____2062 = aux args us ts  in
             (match uu____2062 with
              | (us',ts') ->
                  FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
         | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
             let rec aux args1 us1 ts1 =
               match args1 with
               | (FStar_TypeChecker_NBETerm.Univ u,uu____2197)::args2 ->
                   aux args2 (u :: us1) ts1
               | a::args2 -> aux args2 us1 (a :: ts1)
               | [] -> (us1, ts1)  in
             let uu____2241 = aux args us ts  in
             (match uu____2241 with
              | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
         | FStar_TypeChecker_NBETerm.Constant uu____2284 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Univ uu____2285 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Type_t uu____2286 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Unknown  ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Refinement uu____2287 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Arrow uu____2302 ->
             failwith "Ill-typed application")
  
let (app :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.t ->
        FStar_Syntax_Syntax.aqual -> FStar_TypeChecker_NBETerm.t)
  = fun cfg  -> fun f  -> fun x  -> fun q  -> iapp cfg f [(x, q)] 
let rec tabulate : 'a . Prims.int -> (Prims.int -> 'a) -> 'a Prims.list =
  fun n1  ->
    fun f  ->
      let rec aux i =
        if i < n1
        then
          let uu____2383 = f i  in
          let uu____2384 = aux (i + (Prims.parse_int "1"))  in uu____2383 ::
            uu____2384
        else []  in
      aux (Prims.parse_int "0")
  
let rec (translate_fv :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.fv -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun fvar1  ->
        let debug1 = debug cfg  in
        let qninfo =
          let uu____2518 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2519 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2518 uu____2519  in
        let uu____2520 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2520
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2526 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2528  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2526 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2534  ->
                     let uu____2535 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2535);
                (let uu____2536 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____2536 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     let uu____2541 =
                       let uu____2562 =
                         let f uu____2585 uu____2586 =
                           ((FStar_TypeChecker_NBETerm.Constant
                               FStar_TypeChecker_NBETerm.Unit),
                             FStar_Pervasives_Native.None)
                            in
                         tabulate arity f  in
                       ((fun args  ->
                           let args' =
                             FStar_List.map FStar_TypeChecker_NBETerm.as_arg
                               args
                              in
                           let uu____2631 =
                             prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                               args'
                              in
                           match uu____2631 with
                           | FStar_Pervasives_Native.Some x ->
                               (debug1
                                  (fun uu____2642  ->
                                     let uu____2643 =
                                       FStar_Syntax_Print.fv_to_string fvar1
                                        in
                                     let uu____2644 =
                                       FStar_TypeChecker_NBETerm.t_to_string
                                         x
                                        in
                                     FStar_Util.print2
                                       "Primitive operator %s returned %s\n"
                                       uu____2643 uu____2644);
                                x)
                           | FStar_Pervasives_Native.None  ->
                               (debug1
                                  (fun uu____2650  ->
                                     let uu____2651 =
                                       FStar_Syntax_Print.fv_to_string fvar1
                                        in
                                     FStar_Util.print1
                                       "Primitive operator %s failed\n"
                                       uu____2651);
                                (let uu____2652 =
                                   FStar_TypeChecker_NBETerm.mkFV fvar1 [] []
                                    in
                                 iapp cfg uu____2652 args'))), uu____2562,
                         arity)
                        in
                     FStar_TypeChecker_NBETerm.Lam uu____2541
                 | uu____2657 ->
                     (debug1
                        (fun uu____2665  ->
                           let uu____2666 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____2666);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2674;
                        FStar_Syntax_Syntax.sigquals = uu____2675;
                        FStar_Syntax_Syntax.sigmeta = uu____2676;
                        FStar_Syntax_Syntax.sigattrs = uu____2677;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2774  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2782  ->
                                 let uu____2783 =
                                   let uu____2784 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2784
                                    in
                                 let uu____2785 =
                                   let uu____2786 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2786
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2783 uu____2785);
                            debug1
                              (fun uu____2794  ->
                                 let uu____2795 =
                                   let uu____2796 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2796
                                    in
                                 let uu____2797 =
                                   let uu____2798 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2798
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2795 uu____2797);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____2799 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2807;
                        FStar_Syntax_Syntax.sigquals = uu____2808;
                        FStar_Syntax_Syntax.sigmeta = uu____2809;
                        FStar_Syntax_Syntax.sigattrs = uu____2810;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2907  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2915  ->
                                 let uu____2916 =
                                   let uu____2917 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2917
                                    in
                                 let uu____2918 =
                                   let uu____2919 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2919
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2916 uu____2918);
                            debug1
                              (fun uu____2927  ->
                                 let uu____2928 =
                                   let uu____2929 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2929
                                    in
                                 let uu____2930 =
                                   let uu____2931 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2931
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2928 uu____2930);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____2932 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

and (translate_letbinding :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.letbinding -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun lb  ->
        let debug1 = debug cfg  in
        let us = lb.FStar_Syntax_Syntax.lbunivs  in
        let id1 x = x  in
        let uu____2977 =
          let uu____2998 =
            FStar_List.map
              (fun uu____3019  ->
                 fun uu____3020  ->
                   FStar_All.pipe_left id1
                     ((FStar_TypeChecker_NBETerm.Constant
                         FStar_TypeChecker_NBETerm.Unit),
                       FStar_Pervasives_Native.None)) us
             in
          ((fun us1  ->
              translate cfg (FStar_List.rev_append us1 bs)
                lb.FStar_Syntax_Syntax.lbdef), uu____2998,
            (FStar_List.length us))
           in
        FStar_TypeChecker_NBETerm.Lam uu____2977

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____3066 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____3066
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____3072 ->
        let uu____3073 =
          let uu____3074 =
            let uu____3075 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____3075 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____3074  in
        failwith uu____3073

and (translate_pat :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.pat -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun p  ->
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          let uu____3079 = translate_constant c  in
          FStar_TypeChecker_NBETerm.Constant uu____3079
      | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
          let uu____3098 = FStar_TypeChecker_NBETerm.mkConstruct cfv [] []
             in
          let uu____3103 =
            FStar_List.map
              (fun uu____3118  ->
                 match uu____3118 with
                 | (p1,uu____3130) ->
                     let uu____3131 = translate_pat cfg p1  in
                     (uu____3131, FStar_Pervasives_Native.None)) pats
             in
          iapp cfg uu____3098 uu____3103
      | FStar_Syntax_Syntax.Pat_var bvar ->
          FStar_TypeChecker_NBETerm.mkAccuVar bvar
      | FStar_Syntax_Syntax.Pat_wild bvar ->
          FStar_TypeChecker_NBETerm.mkAccuVar bvar
      | FStar_Syntax_Syntax.Pat_dot_term (bvar,t) ->
          failwith "Pat_dot_term not implemented"

and (translate :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun e  ->
        let debug1 = debug cfg  in
        debug1
          (fun uu____3162  ->
             let uu____3163 =
               let uu____3164 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____3164  in
             let uu____3165 =
               let uu____3166 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____3166  in
             FStar_Util.print2 "Term: %s - %s\n" uu____3163 uu____3165);
        debug1
          (fun uu____3172  ->
             let uu____3173 =
               let uu____3174 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____3174  in
             FStar_Util.print1 "BS list: %s\n" uu____3173);
        (let uu____3179 =
           let uu____3180 = FStar_Syntax_Subst.compress e  in
           uu____3180.FStar_Syntax_Syntax.n  in
         match uu____3179 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____3183,uu____3184) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3304 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3304
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3323  ->
                   let uu____3324 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3325 =
                     let uu____3326 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3326
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____3324 uu____3325);
              (let uu____3331 = translate cfg bs t  in
               let uu____3332 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3336 = translate_univ bs x  in
                      FStar_TypeChecker_NBETerm.as_arg uu____3336) us
                  in
               iapp cfg uu____3331 uu____3332))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3338 =
               let uu____3339 = translate_univ bs u  in un_univ uu____3339
                in
             FStar_TypeChecker_NBETerm.Type_t uu____3338
         | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
             (debug_term e; failwith "Tm_arrow: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____3383  ->
                     let uu____3384 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____3384)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3386,uu____3387) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____3448,uu____3449) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____3474) ->
             let uu____3499 =
               let uu____3520 =
                 FStar_List.map
                   (fun x  ->
                      fun uu____3555  ->
                        let uu____3556 =
                          translate cfg bs
                            (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                           in
                        (uu____3556, (FStar_Pervasives_Native.snd x))) xs
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____3520, (FStar_List.length xs))
                in
             FStar_TypeChecker_NBETerm.Lam uu____3499
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3588;
                FStar_Syntax_Syntax.vars = uu____3589;_},arg::more::args)
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let uu____3649 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3649 with
              | (reifyh,uu____3667) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app reifyh [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3711 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3711)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3720;
                FStar_Syntax_Syntax.vars = uu____3721;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___246_3763 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___246_3763.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___246_3763.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___246_3763.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___246_3763.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___246_3763.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___246_3763.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___246_3763.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___246_3763.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____3801  ->
                   let uu____3802 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3803 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3802
                     uu____3803);
              (let uu____3804 = translate cfg bs head1  in
               let uu____3805 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3827 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3827, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3804 uu____3805))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3916  ->
                         let uu____3917 =
                           let uu____3918 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3941  ->
                                     match uu____3941 with
                                     | (x,q) ->
                                         let uu____3954 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3954))
                              in
                           FStar_All.pipe_right uu____3918
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3917);
                    (let uu____3958 = pickBranch cfg scrut1 branches  in
                     match uu____3958 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____3985 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____3985 branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   let uu____4005 = pickBranch cfg scrut1 branches  in
                   (match uu____4005 with
                    | FStar_Pervasives_Native.Some (branch1,[]) ->
                        translate cfg bs branch1
                    | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                        translate cfg (arg :: bs) branch1
                    | FStar_Pervasives_Native.None  ->
                        FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                          make_branches
                    | FStar_Pervasives_Native.Some (uu____4053,hd1::tl1) ->
                        failwith
                          "Impossible: Matching on constants cannot bind more than one variable")
               | uu____4072 ->
                   FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                     make_branches
             
             and make_branches readback1 =
               let rec process_pattern bs1 p =
                 let uu____4105 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____4139 =
                         FStar_List.fold_left
                           (fun uu____4181  ->
                              fun uu____4182  ->
                                match (uu____4181, uu____4182) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____4275 = process_pattern bs2 arg
                                       in
                                    (match uu____4275 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____4139 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____4386 =
                           let uu____4387 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4387  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4386
                          in
                       let uu____4388 =
                         let uu____4391 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4391 :: bs1  in
                       (uu____4388, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____4396 =
                           let uu____4397 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4397  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4396
                          in
                       let uu____4398 =
                         let uu____4401 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4401 :: bs1  in
                       (uu____4398, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____4411 =
                           let uu____4412 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4412  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4411
                          in
                       let uu____4413 =
                         let uu____4416 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4416 :: bs1  in
                       let uu____4417 =
                         let uu____4418 =
                           let uu____4425 =
                             let uu____4428 = translate cfg bs1 tm  in
                             readback1 uu____4428  in
                           (x, uu____4425)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____4418  in
                       (uu____4413, uu____4417)
                    in
                 match uu____4105 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___247_4448 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___247_4448.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____4467  ->
                    match uu____4467 with
                    | (pat,when_clause,e1) ->
                        let uu____4489 = process_pattern bs pat  in
                        (match uu____4489 with
                         | (bs',pat') ->
                             let uu____4506 =
                               let uu____4507 =
                                 let uu____4510 = translate cfg bs' e1  in
                                 readback1 uu____4510  in
                               (pat', when_clause, uu____4507)  in
                             FStar_Syntax_Util.branch uu____4506)) branches
              in let uu____4519 = translate cfg bs scrut  in case uu____4519
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic (m,t)) when
             cfg.FStar_TypeChecker_Cfg.reifying ->
             translate_monadic (m, t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t)) when
             cfg.FStar_TypeChecker_Cfg.reifying ->
             translate_monadic_lift (m, m', t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_let ((false ,lbs),body) ->
             let bs' =
               FStar_List.fold_left
                 (fun bs'  ->
                    fun lb  ->
                      let b = translate_letbinding cfg bs lb  in b :: bs') bs
                 lbs
                in
             translate cfg bs' body
         | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) ->
             let uu____4592 = make_rec_env lbs bs  in
             translate cfg uu____4592 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4596) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (uu____4601,uu____4602) ->
             let uu____4607 =
               let uu____4608 =
                 let uu____4609 = FStar_Syntax_Subst.compress e  in
                 FStar_Syntax_Print.tag_of_term uu____4609  in
               Prims.strcat "Not yet handled: " uu____4608  in
             failwith uu____4607
         | FStar_Syntax_Syntax.Tm_lazy uu____4610 ->
             let uu____4611 =
               let uu____4612 =
                 let uu____4613 = FStar_Syntax_Subst.compress e  in
                 FStar_Syntax_Print.tag_of_term uu____4613  in
               Prims.strcat "Not yet handled: " uu____4612  in
             failwith uu____4611)

and (translate_monadic :
  (FStar_Ident.lident,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____4614  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____4614 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____4649 =
                     let uu____4658 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____4658
                      in
                   (match uu____4649 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____4665 =
                          let uu____4666 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____4666
                           in
                        failwith uu____4665
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___248_4680 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___248_4680.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___248_4680.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___248_4680.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___248_4680.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___248_4680.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___248_4680.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___248_4680.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___248_4680.FStar_TypeChecker_Cfg.normalize_pure_lets);
                            FStar_TypeChecker_Cfg.reifying = false
                          }  in
                        let body_lam =
                          let body_rc =
                            {
                              FStar_Syntax_Syntax.residual_effect = m;
                              FStar_Syntax_Syntax.residual_typ =
                                (FStar_Pervasives_Native.Some ty);
                              FStar_Syntax_Syntax.residual_flags = []
                            }  in
                          let uu____4687 =
                            let uu____4694 =
                              let uu____4695 =
                                let uu____4714 =
                                  let uu____4723 =
                                    let uu____4730 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____4730,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____4723]  in
                                (uu____4714, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____4695  in
                            FStar_Syntax_Syntax.mk uu____4694  in
                          uu____4687 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____4767 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____4767
                          then
                            let uu____4774 =
                              let uu____4779 =
                                let uu____4780 =
                                  FStar_Syntax_Embeddings.embed
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____4780  in
                              (uu____4779, FStar_Pervasives_Native.None)  in
                            let uu____4781 =
                              let uu____4788 =
                                let uu____4793 =
                                  let uu____4794 =
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____4794  in
                                (uu____4793, FStar_Pervasives_Native.None)
                                 in
                              [uu____4788]  in
                            uu____4774 :: uu____4781
                          else []  in
                        let uu____4812 =
                          let uu____4813 =
                            let uu____4814 =
                              FStar_Syntax_Util.un_uinst
                                (FStar_Pervasives_Native.snd
                                   ed.FStar_Syntax_Syntax.bind_repr)
                               in
                            translate cfg' [] uu____4814  in
                          iapp cfg uu____4813
                            [((FStar_TypeChecker_NBETerm.Univ
                                 FStar_Syntax_Syntax.U_unknown),
                               FStar_Pervasives_Native.None);
                            ((FStar_TypeChecker_NBETerm.Univ
                                FStar_Syntax_Syntax.U_unknown),
                              FStar_Pervasives_Native.None)]
                           in
                        let uu____4831 =
                          let uu____4832 =
                            let uu____4839 =
                              let uu____4844 =
                                translate cfg' bs
                                  lb.FStar_Syntax_Syntax.lbtyp
                                 in
                              (uu____4844, FStar_Pervasives_Native.None)  in
                            let uu____4845 =
                              let uu____4852 =
                                let uu____4857 = translate cfg' bs ty  in
                                (uu____4857, FStar_Pervasives_Native.None)
                                 in
                              [uu____4852]  in
                            uu____4839 :: uu____4845  in
                          let uu____4870 =
                            let uu____4877 =
                              let uu____4884 =
                                let uu____4891 =
                                  let uu____4896 =
                                    translate cfg bs
                                      lb.FStar_Syntax_Syntax.lbdef
                                     in
                                  (uu____4896, FStar_Pervasives_Native.None)
                                   in
                                let uu____4897 =
                                  let uu____4904 =
                                    let uu____4911 =
                                      let uu____4916 =
                                        translate cfg bs body_lam  in
                                      (uu____4916,
                                        FStar_Pervasives_Native.None)
                                       in
                                    [uu____4911]  in
                                  (FStar_TypeChecker_NBETerm.Unknown,
                                    FStar_Pervasives_Native.None) ::
                                    uu____4904
                                   in
                                uu____4891 :: uu____4897  in
                              (FStar_TypeChecker_NBETerm.Unknown,
                                FStar_Pervasives_Native.None) :: uu____4884
                               in
                            FStar_List.append maybe_range_arg uu____4877  in
                          FStar_List.append uu____4832 uu____4870  in
                        iapp cfg uu____4812 uu____4831)
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____4945);
                      FStar_Syntax_Syntax.pos = uu____4946;
                      FStar_Syntax_Syntax.vars = uu____4947;_},(e2,uu____4949)::[])
                   ->
                   translate
                     (let uu___249_4990 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___249_4990.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___249_4990.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___249_4990.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___249_4990.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___249_4990.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___249_4990.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___249_4990.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___249_4990.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app uu____4991 -> translate cfg bs e1
               | uu____5008 ->
                   let uu____5009 =
                     let uu____5010 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____5010
                      in
                   failwith uu____5009)

and (translate_monadic_lift :
  (FStar_Ident.lident,FStar_Ident.lident,FStar_Syntax_Syntax.term'
                                           FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____5011  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____5011 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____5035 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____5035
              then
                let ed =
                  let uu____5037 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____5037
                   in
                let cfg' =
                  let uu___250_5039 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___250_5039.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___250_5039.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___250_5039.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___250_5039.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___250_5039.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___250_5039.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___250_5039.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___250_5039.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let uu____5040 =
                  let uu____5041 =
                    let uu____5042 =
                      FStar_Syntax_Util.un_uinst
                        (FStar_Pervasives_Native.snd
                           ed.FStar_Syntax_Syntax.return_repr)
                       in
                    translate cfg' [] uu____5042  in
                  iapp cfg uu____5041
                    [((FStar_TypeChecker_NBETerm.Univ
                         FStar_Syntax_Syntax.U_unknown),
                       FStar_Pervasives_Native.None)]
                   in
                let uu____5055 =
                  let uu____5056 =
                    let uu____5061 = translate cfg' bs ty  in
                    (uu____5061, FStar_Pervasives_Native.None)  in
                  let uu____5062 =
                    let uu____5069 =
                      let uu____5074 = translate cfg' bs e1  in
                      (uu____5074, FStar_Pervasives_Native.None)  in
                    [uu____5069]  in
                  uu____5056 :: uu____5062  in
                iapp cfg uu____5040 uu____5055
              else
                (let uu____5088 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____5088 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____5091 =
                       let uu____5092 = FStar_Ident.text_of_lid msrc  in
                       let uu____5093 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____5092 uu____5093
                        in
                     failwith uu____5091
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____5094;
                       FStar_TypeChecker_Env.mtarget = uu____5095;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____5096;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____5126 =
                       let uu____5127 = FStar_Ident.text_of_lid msrc  in
                       let uu____5128 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____5127 uu____5128
                        in
                     failwith uu____5126
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____5129;
                       FStar_TypeChecker_Env.mtarget = uu____5130;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____5131;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____5186 =
                         let uu____5189 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____5189
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____5186
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___251_5207 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___251_5207.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___251_5207.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___251_5207.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___251_5207.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___251_5207.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___251_5207.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___251_5207.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___251_5207.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let uu____5208 = translate cfg' [] lift_lam  in
                     let uu____5209 =
                       let uu____5210 =
                         let uu____5215 = translate cfg bs e1  in
                         (uu____5215, FStar_Pervasives_Native.None)  in
                       [uu____5210]  in
                     iapp cfg uu____5208 uu____5209)

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____5239  ->
           let uu____5240 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____5240);
      (match x with
       | FStar_TypeChecker_NBETerm.Univ u ->
           failwith "Readback of universes should not occur"
       | FStar_TypeChecker_NBETerm.Unknown  ->
           FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit )
           -> FStar_Syntax_Syntax.unit_const
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (true )) -> FStar_Syntax_Util.exp_true_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (false )) -> FStar_Syntax_Util.exp_false_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int i)
           ->
           let uu____5243 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____5243 FStar_Syntax_Util.exp_int
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String
           (s,r)) ->
           FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, r)))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char
           c) -> FStar_Syntax_Util.exp_char c
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Range
           r) ->
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range r
             FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Type_t u ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lam (f,targs,arity) ->
           let uu____5285 =
             FStar_List.fold_left
               (fun uu____5332  ->
                  fun tf  ->
                    match uu____5332 with
                    | (args,accus) ->
                        let uu____5392 = tf ()  in
                        (match uu____5392 with
                         | (xt,q) ->
                             let x1 =
                               let uu____5420 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____5420
                                in
                             let uu____5421 =
                               let uu____5424 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____5424 :: accus  in
                             (((x1, q) :: args), uu____5421))) ([], []) targs
              in
           (match uu____5285 with
            | (args,accus) ->
                let body =
                  let uu____5482 = f accus  in readback cfg uu____5482  in
                FStar_Syntax_Util.abs args body FStar_Pervasives_Native.None)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____5510 =
               let uu____5511 =
                 let uu____5512 = targ ()  in
                 FStar_Pervasives_Native.fst uu____5512  in
               readback cfg uu____5511  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____5510
              in
           let body =
             let uu____5522 =
               let uu____5523 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____5523  in
             readback cfg uu____5522  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____5572  ->
                  match uu____5572 with
                  | (x1,q) ->
                      let uu____5591 = readback cfg x1  in (uu____5591, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____5616 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____5625::uu____5626 ->
                let uu____5629 =
                  let uu____5632 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____5632
                    (FStar_List.rev us)
                   in
                apply uu____5629
            | [] ->
                let uu____5633 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____5633)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____5684  ->
                  match uu____5684 with
                  | (x1,q) ->
                      let uu____5703 = readback cfg x1  in (uu____5703, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____5728 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____5737::uu____5738 ->
                let uu____5741 =
                  let uu____5744 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____5744
                    (FStar_List.rev us)
                   in
                apply uu____5741
            | [] ->
                let uu____5745 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____5745)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____5806  ->
                  match uu____5806 with
                  | (x1,q) ->
                      let uu____5825 = readback cfg x1  in (uu____5825, q))
               ts
              in
           let uu____5828 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____5828 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____5930  ->
                  match uu____5930 with
                  | (x1,q) ->
                      let uu____5949 = readback cfg x1  in (uu____5949, q))
               ts
              in
           let head1 =
             let scrut_new = readback cfg scrut  in
             let branches_new = make_branches (readback cfg)  in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_match (scrut_new, branches_new))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           (match ts with
            | [] -> head1
            | uu____5997 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app cfg hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____6090 = curry hd1 args1  in
                 app cfg uu____6090 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
              in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef  in
           let uu____6092 = test_args ts args_no  in
           if uu____6092
           then
             let uu____6095 =
               let uu____6096 =
                 let uu____6097 = make_rec_env lbs bs  in
                 translate_letbinding cfg uu____6097 lb  in
               curry uu____6096 ts  in
             readback cfg uu____6095
           else
             (let head1 =
                let f =
                  match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inl bv -> FStar_Syntax_Syntax.bv_to_name bv
                  | FStar_Util.Inr fv -> failwith "Not yet implemented"  in
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((true, lbs), f))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              let args =
                map_rev
                  (fun uu____6148  ->
                     match uu____6148 with
                     | (x1,q) ->
                         let uu____6167 = readback cfg x1  in (uu____6167, q))
                  ts
                 in
              match ts with
              | [] -> head1
              | uu____6176 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Arrow uu____6185 ->
           failwith "Arrows not yet handled")

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____6226 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____6233 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____6249 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____6269 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____6282 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____6288 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___245_6293  ->
    match uu___245_6293 with
    | Primops  -> FStar_TypeChecker_Env.Primops
    | UnfoldUntil d -> FStar_TypeChecker_Env.UnfoldUntil d
    | UnfoldOnly lids -> FStar_TypeChecker_Env.UnfoldOnly lids
    | UnfoldAttr attr -> FStar_TypeChecker_Env.UnfoldAttr attr
    | UnfoldTac  -> FStar_TypeChecker_Env.UnfoldTac
    | Reify  -> FStar_TypeChecker_Env.Reify
  
let (normalize' :
  FStar_TypeChecker_Env.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg = FStar_TypeChecker_Cfg.config steps env  in
        let cfg1 =
          let uu___252_6320 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___253_6323 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___253_6323.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___253_6323.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___253_6323.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___253_6323.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___253_6323.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___253_6323.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___253_6323.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___253_6323.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___253_6323.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___253_6323.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___253_6323.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___253_6323.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___253_6323.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___253_6323.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___253_6323.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___253_6323.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___253_6323.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___253_6323.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___253_6323.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___253_6323.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___253_6323.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___253_6323.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___253_6323.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___253_6323.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___252_6320.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___252_6320.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___252_6320.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___252_6320.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___252_6320.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___252_6320.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___252_6320.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___252_6320.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____6327  ->
             let uu____6328 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____6328);
        (let uu____6329 = translate cfg1 [] e  in readback cfg1 uu____6329)
  
let (test_normalize :
  step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg =
          let uu____6350 = FStar_List.map step_as_normalizer_step steps  in
          FStar_TypeChecker_Cfg.config uu____6350 env  in
        let cfg1 =
          let uu___254_6354 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___255_6357 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___255_6357.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___255_6357.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___255_6357.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___255_6357.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___255_6357.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___255_6357.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___255_6357.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___255_6357.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___255_6357.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___255_6357.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___255_6357.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___255_6357.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___255_6357.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___255_6357.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___255_6357.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___255_6357.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___255_6357.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___255_6357.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___255_6357.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___255_6357.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___255_6357.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___255_6357.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___255_6357.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___255_6357.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___254_6354.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___254_6354.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___254_6354.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___254_6354.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___254_6354.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___254_6354.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___254_6354.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___254_6354.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____6361  ->
             let uu____6362 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____6362);
        (let r =
           let uu____6364 = translate cfg1 [] e  in readback cfg1 uu____6364
            in
         debug cfg1
           (fun uu____6368  ->
              let uu____6369 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "NBE returned %s" uu____6369);
         r)
  