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
                     let uu____665 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                     if uu____665
                     then matches_args [] (FStar_List.rev args_rev) arg_pats
                     else FStar_Util.Inr false
                 | uu____679 -> FStar_Util.Inr true)
             in
          match branches1 with
          | [] -> failwith "Branch not found"
          | (p,_wopt,e)::branches2 ->
              let uu____720 = matches_pat scrut1 p  in
              (match uu____720 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____743  ->
                         let uu____744 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____744);
                    FStar_Pervasives_Native.Some (e, matches))
               | FStar_Util.Inr (false ) ->
                   pickBranch_aux scrut1 branches2 branches0
               | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
           in
        pickBranch_aux scrut branches branches
  
let rec test_args :
  'Auu____770 .
    (FStar_TypeChecker_NBETerm.t,'Auu____770) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.int -> Prims.bool
  =
  fun ts  ->
    fun cnt  ->
      match ts with
      | [] -> cnt <= (Prims.parse_int "0")
      | t::ts1 ->
          (let uu____815 =
             FStar_TypeChecker_NBETerm.isAccu (FStar_Pervasives_Native.fst t)
              in
           Prims.op_Negation uu____815) &&
            (test_args ts1 (cnt - (Prims.parse_int "1")))
  
let rec (count_abstractions : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    let uu____821 =
      let uu____822 = FStar_Syntax_Subst.compress t  in
      uu____822.FStar_Syntax_Syntax.n  in
    match uu____821 with
    | FStar_Syntax_Syntax.Tm_delayed uu____825 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____848 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_name uu____849 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_fvar uu____850 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_constant uu____851 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_type uu____852 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_arrow uu____853 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uvar uu____868 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_refine uu____881 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_unknown  -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____889) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____896) ->
        let uu____921 = count_abstractions body  in
        (FStar_List.length xs) + uu____921
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____954 =
          let uu____955 = count_abstractions head1  in
          uu____955 - (FStar_List.length args)  in
        max uu____954 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____1016,uu____1017,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____1066,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1085) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1091,uu____1092) ->
        count_abstractions t1
    | uu____1133 -> (Prims.parse_int "0")
  
let (find_sigelt_in_gamma :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.env ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lid  ->
        let mapper uu____1178 =
          match uu____1178 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1261  ->
                         let uu____1262 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1262);
                    FStar_Pervasives_Native.Some elt)
               | uu____1263 -> FStar_Pervasives_Native.None)
           in
        let uu____1278 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1278 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1322 -> true
    | uu____1323 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | uu____1330 -> failwith "Not a universe"
  
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
              (uu____1343,uu____1344,uu____1345,uu____1346,uu____1347,uu____1348);
            FStar_Syntax_Syntax.sigrng = uu____1349;
            FStar_Syntax_Syntax.sigquals = uu____1350;
            FStar_Syntax_Syntax.sigmeta = uu____1351;
            FStar_Syntax_Syntax.sigattrs = uu____1352;_},uu____1353),uu____1354)
        -> true
    | uu____1409 -> false
  
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
            let uu____1434 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1434
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1438 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1438
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____1441 -> u2
        | FStar_Syntax_Syntax.U_unif uu____1442 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2  in
      let uu____1451 = aux u  in FStar_TypeChecker_NBETerm.Univ uu____1451
  
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
            let uu____1519 =
              let uu____1522 =
                FStar_TypeChecker_NBETerm.mkAccuRec lb lbs0 bs0  in
              uu____1522 :: bs1  in
            aux lbs' lbs0 uu____1519 bs0
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
           | FStar_Util.Inl uu____1544 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1548 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1548
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
          (fun uu____1571  ->
             let uu____1572 = FStar_TypeChecker_NBETerm.t_to_string f  in
             let uu____1573 = FStar_TypeChecker_NBETerm.args_to_string args
                in
             FStar_Util.print2 "App : %s @ %s\n" uu____1572 uu____1573);
        (match f with
         | FStar_TypeChecker_NBETerm.Lam (f1,targs,n1) ->
             let m = FStar_List.length args  in
             if m < n1
             then
               let uu____1616 = FStar_List.splitAt m targs  in
               (match uu____1616 with
                | (uu____1650,targs') ->
                    FStar_TypeChecker_NBETerm.Lam
                      (((fun l  ->
                           let uu____1707 =
                             map_append FStar_Pervasives_Native.fst args l
                              in
                           f1 uu____1707)), targs', (n1 - m)))
             else
               if m = n1
               then
                 (let uu____1723 =
                    FStar_List.map FStar_Pervasives_Native.fst args  in
                  f1 uu____1723)
               else
                 (let uu____1731 = FStar_List.splitAt n1 args  in
                  match uu____1731 with
                  | (args1,args') ->
                      let uu____1778 =
                        let uu____1779 =
                          FStar_List.map FStar_Pervasives_Native.fst args1
                           in
                        f1 uu____1779  in
                      iapp cfg uu____1778 args')
         | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
             FStar_TypeChecker_NBETerm.Accu
               (a, (FStar_List.rev_append args ts))
         | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
             let rec aux args1 us1 ts1 =
               match args1 with
               | (FStar_TypeChecker_NBETerm.Univ u,uu____1898)::args2 ->
                   aux args2 (u :: us1) ts1
               | a::args2 -> aux args2 us1 (a :: ts1)
               | [] -> (us1, ts1)  in
             let uu____1942 = aux args us ts  in
             (match uu____1942 with
              | (us',ts') ->
                  FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
         | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
             let rec aux args1 us1 ts1 =
               match args1 with
               | (FStar_TypeChecker_NBETerm.Univ u,uu____2069)::args2 ->
                   aux args2 (u :: us1) ts1
               | a::args2 -> aux args2 us1 (a :: ts1)
               | [] -> (us1, ts1)  in
             let uu____2113 = aux args us ts  in
             (match uu____2113 with
              | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
         | FStar_TypeChecker_NBETerm.Constant uu____2152 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Univ uu____2153 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Type_t uu____2154 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Unknown  ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Refinement uu____2155 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Arrow uu____2170 ->
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
          let uu____2251 = f i  in
          let uu____2252 = aux (i + (Prims.parse_int "1"))  in uu____2251 ::
            uu____2252
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
          let uu____2386 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2387 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2386 uu____2387  in
        let uu____2388 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2388
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2394 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2396  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2394 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2402  ->
                     let uu____2403 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2403);
                (let uu____2404 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____2404 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     let uu____2409 =
                       let uu____2430 =
                         let f uu____2457 uu____2458 =
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
                           let uu____2505 =
                             prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                               args'
                              in
                           match uu____2505 with
                           | FStar_Pervasives_Native.Some x ->
                               (debug1
                                  (fun uu____2516  ->
                                     let uu____2517 =
                                       FStar_Syntax_Print.fv_to_string fvar1
                                        in
                                     let uu____2518 =
                                       FStar_TypeChecker_NBETerm.t_to_string
                                         x
                                        in
                                     FStar_Util.print2
                                       "Primitive operator %s returned %s\n"
                                       uu____2517 uu____2518);
                                x)
                           | FStar_Pervasives_Native.None  ->
                               (debug1
                                  (fun uu____2524  ->
                                     let uu____2525 =
                                       FStar_Syntax_Print.fv_to_string fvar1
                                        in
                                     FStar_Util.print1
                                       "Primitive operator %s failed\n"
                                       uu____2525);
                                (let uu____2526 =
                                   FStar_TypeChecker_NBETerm.mkFV fvar1 [] []
                                    in
                                 iapp cfg uu____2526 args'))), uu____2430,
                         arity)
                        in
                     FStar_TypeChecker_NBETerm.Lam uu____2409
                 | uu____2531 ->
                     (debug1
                        (fun uu____2539  ->
                           let uu____2540 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____2540);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2548;
                        FStar_Syntax_Syntax.sigquals = uu____2549;
                        FStar_Syntax_Syntax.sigmeta = uu____2550;
                        FStar_Syntax_Syntax.sigattrs = uu____2551;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2620  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2628  ->
                                 let uu____2629 =
                                   let uu____2630 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2630
                                    in
                                 let uu____2631 =
                                   let uu____2632 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2632
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2629 uu____2631);
                            debug1
                              (fun uu____2640  ->
                                 let uu____2641 =
                                   let uu____2642 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2642
                                    in
                                 let uu____2643 =
                                   let uu____2644 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2644
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2641 uu____2643);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____2645 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2653;
                        FStar_Syntax_Syntax.sigquals = uu____2654;
                        FStar_Syntax_Syntax.sigmeta = uu____2655;
                        FStar_Syntax_Syntax.sigattrs = uu____2656;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2725  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2733  ->
                                 let uu____2734 =
                                   let uu____2735 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2735
                                    in
                                 let uu____2736 =
                                   let uu____2737 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2737
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2734 uu____2736);
                            debug1
                              (fun uu____2745  ->
                                 let uu____2746 =
                                   let uu____2747 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2747
                                    in
                                 let uu____2748 =
                                   let uu____2749 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2749
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2746 uu____2748);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____2750 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        let uu____2795 =
          let uu____2816 =
            FStar_List.map
              (fun uu____2837  ->
                 fun uu____2838  ->
                   FStar_All.pipe_left id1
                     ((FStar_TypeChecker_NBETerm.Constant
                         FStar_TypeChecker_NBETerm.Unit),
                       FStar_Pervasives_Native.None)) us
             in
          ((fun us1  ->
              translate cfg (FStar_List.rev_append us1 bs)
                lb.FStar_Syntax_Syntax.lbdef), uu____2816,
            (FStar_List.length us))
           in
        FStar_TypeChecker_NBETerm.Lam uu____2795

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____2884 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____2884
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____2890 ->
        let uu____2891 =
          let uu____2892 =
            let uu____2893 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____2893 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____2892  in
        failwith uu____2891

and (translate_pat :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.pat -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun p  ->
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          let uu____2897 = translate_constant c  in
          FStar_TypeChecker_NBETerm.Constant uu____2897
      | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
          let uu____2916 = FStar_TypeChecker_NBETerm.mkConstruct cfv [] []
             in
          let uu____2921 =
            FStar_List.map
              (fun uu____2936  ->
                 match uu____2936 with
                 | (p1,uu____2948) ->
                     let uu____2949 = translate_pat cfg p1  in
                     (uu____2949, FStar_Pervasives_Native.None)) pats
             in
          iapp cfg uu____2916 uu____2921
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
          (fun uu____2980  ->
             let uu____2981 =
               let uu____2982 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2982  in
             let uu____2983 =
               let uu____2984 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2984  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2981 uu____2983);
        debug1
          (fun uu____2990  ->
             let uu____2991 =
               let uu____2992 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____2992  in
             FStar_Util.print1 "BS list: %s\n" uu____2991);
        (let uu____2997 =
           let uu____2998 = FStar_Syntax_Subst.compress e  in
           uu____2998.FStar_Syntax_Syntax.n  in
         match uu____2997 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____3001,uu____3002) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3040 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3040
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3055  ->
                   let uu____3056 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3057 =
                     let uu____3058 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3058
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____3056 uu____3057);
              (let uu____3063 = translate cfg bs t  in
               let uu____3064 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3068 = translate_univ bs x  in
                      FStar_TypeChecker_NBETerm.as_arg uu____3068) us
                  in
               iapp cfg uu____3063 uu____3064))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3070 =
               let uu____3071 = translate_univ bs u  in un_univ uu____3071
                in
             FStar_TypeChecker_NBETerm.Type_t uu____3070
         | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
             (debug_term e; failwith "Tm_arrow: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____3115  ->
                     let uu____3116 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____3116)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3118,uu____3119) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____3180,uu____3181) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____3206) ->
             let uu____3231 =
               let uu____3252 =
                 FStar_List.map
                   (fun x  ->
                      fun uu____3287  ->
                        let uu____3288 =
                          translate cfg bs
                            (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                           in
                        (uu____3288, (FStar_Pervasives_Native.snd x))) xs
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____3252, (FStar_List.length xs))
                in
             FStar_TypeChecker_NBETerm.Lam uu____3231
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3320;
                FStar_Syntax_Syntax.vars = uu____3321;_},arg::more::args)
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let uu____3381 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3381 with
              | (reifyh,uu____3399) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app reifyh [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3443 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3443)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3452;
                FStar_Syntax_Syntax.vars = uu____3453;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___245_3495 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___245_3495.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___245_3495.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___245_3495.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___245_3495.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___245_3495.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___245_3495.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___245_3495.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___245_3495.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____3533  ->
                   let uu____3534 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3535 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3534
                     uu____3535);
              (let uu____3536 = translate cfg bs head1  in
               let uu____3537 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3559 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3559, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3536 uu____3537))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3644  ->
                         let uu____3645 =
                           let uu____3646 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3669  ->
                                     match uu____3669 with
                                     | (x,q) ->
                                         let uu____3682 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3682))
                              in
                           FStar_All.pipe_right uu____3646
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3645);
                    (let uu____3686 = pickBranch cfg scrut1 branches  in
                     match uu____3686 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____3707 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____3707 branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   let uu____3725 = pickBranch cfg scrut1 branches  in
                   (match uu____3725 with
                    | FStar_Pervasives_Native.Some (branch1,[]) ->
                        translate cfg bs branch1
                    | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                        translate cfg (arg :: bs) branch1
                    | FStar_Pervasives_Native.None  ->
                        FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                          make_branches
                    | FStar_Pervasives_Native.Some (uu____3759,hd1::tl1) ->
                        failwith
                          "Impossible: Matching on constants cannot bind more than one variable")
               | uu____3772 ->
                   FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                     make_branches
             
             and make_branches readback1 =
               let rec process_pattern bs1 p =
                 let uu____3805 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____3839 =
                         FStar_List.fold_left
                           (fun uu____3877  ->
                              fun uu____3878  ->
                                match (uu____3877, uu____3878) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3959 = process_pattern bs2 arg
                                       in
                                    (match uu____3959 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3839 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____4048 =
                           let uu____4049 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4049  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4048
                          in
                       let uu____4050 =
                         let uu____4053 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4053 :: bs1  in
                       (uu____4050, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____4058 =
                           let uu____4059 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4059  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4058
                          in
                       let uu____4060 =
                         let uu____4063 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4063 :: bs1  in
                       (uu____4060, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____4073 =
                           let uu____4074 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4074  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4073
                          in
                       let uu____4075 =
                         let uu____4078 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4078 :: bs1  in
                       let uu____4079 =
                         let uu____4080 =
                           let uu____4087 =
                             let uu____4090 = translate cfg bs1 tm  in
                             readback1 uu____4090  in
                           (x, uu____4087)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____4080  in
                       (uu____4075, uu____4079)
                    in
                 match uu____3805 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___246_4110 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___246_4110.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____4129  ->
                    match uu____4129 with
                    | (pat,when_clause,e1) ->
                        let uu____4151 = process_pattern bs pat  in
                        (match uu____4151 with
                         | (bs',pat') ->
                             let uu____4164 =
                               let uu____4165 =
                                 let uu____4168 = translate cfg bs' e1  in
                                 readback1 uu____4168  in
                               (pat', when_clause, uu____4165)  in
                             FStar_Syntax_Util.branch uu____4164)) branches
              in let uu____4177 = translate cfg bs scrut  in case uu____4177
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
             let uu____4250 = make_rec_env lbs bs  in
             translate cfg uu____4250 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4254) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (uu____4259,uu____4260) ->
             let uu____4265 =
               let uu____4266 =
                 let uu____4267 = FStar_Syntax_Subst.compress e  in
                 FStar_Syntax_Print.tag_of_term uu____4267  in
               Prims.strcat "Not yet handled: " uu____4266  in
             failwith uu____4265
         | FStar_Syntax_Syntax.Tm_lazy uu____4268 ->
             let uu____4269 =
               let uu____4270 =
                 let uu____4271 = FStar_Syntax_Subst.compress e  in
                 FStar_Syntax_Print.tag_of_term uu____4271  in
               Prims.strcat "Not yet handled: " uu____4270  in
             failwith uu____4269)

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____4272  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____4272 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____4307 =
                     let uu____4316 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____4316
                      in
                   (match uu____4307 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____4323 =
                          let uu____4324 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____4324
                           in
                        failwith uu____4323
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___247_4338 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___247_4338.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___247_4338.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___247_4338.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___247_4338.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___247_4338.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___247_4338.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___247_4338.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___247_4338.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____4345 =
                            let uu____4352 =
                              let uu____4353 =
                                let uu____4372 =
                                  let uu____4381 =
                                    let uu____4388 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____4388,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____4381]  in
                                (uu____4372, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____4353  in
                            FStar_Syntax_Syntax.mk uu____4352  in
                          uu____4345 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____4425 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____4425
                          then
                            let uu____4432 =
                              let uu____4437 =
                                let uu____4438 =
                                  FStar_Syntax_Embeddings.embed
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____4438  in
                              (uu____4437, FStar_Pervasives_Native.None)  in
                            let uu____4439 =
                              let uu____4446 =
                                let uu____4451 =
                                  let uu____4452 =
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____4452  in
                                (uu____4451, FStar_Pervasives_Native.None)
                                 in
                              [uu____4446]  in
                            uu____4432 :: uu____4439
                          else []  in
                        let uu____4470 =
                          let uu____4471 =
                            let uu____4472 =
                              FStar_Syntax_Util.un_uinst
                                (FStar_Pervasives_Native.snd
                                   ed.FStar_Syntax_Syntax.bind_repr)
                               in
                            translate cfg' [] uu____4472  in
                          iapp cfg uu____4471
                            [((FStar_TypeChecker_NBETerm.Univ
                                 FStar_Syntax_Syntax.U_unknown),
                               FStar_Pervasives_Native.None);
                            ((FStar_TypeChecker_NBETerm.Univ
                                FStar_Syntax_Syntax.U_unknown),
                              FStar_Pervasives_Native.None)]
                           in
                        let uu____4489 =
                          let uu____4490 =
                            let uu____4497 =
                              let uu____4502 =
                                translate cfg' bs
                                  lb.FStar_Syntax_Syntax.lbtyp
                                 in
                              (uu____4502, FStar_Pervasives_Native.None)  in
                            let uu____4503 =
                              let uu____4510 =
                                let uu____4515 = translate cfg' bs ty  in
                                (uu____4515, FStar_Pervasives_Native.None)
                                 in
                              [uu____4510]  in
                            uu____4497 :: uu____4503  in
                          let uu____4528 =
                            let uu____4535 =
                              let uu____4542 =
                                let uu____4549 =
                                  let uu____4554 =
                                    translate cfg bs
                                      lb.FStar_Syntax_Syntax.lbdef
                                     in
                                  (uu____4554, FStar_Pervasives_Native.None)
                                   in
                                let uu____4555 =
                                  let uu____4562 =
                                    let uu____4569 =
                                      let uu____4574 =
                                        translate cfg bs body_lam  in
                                      (uu____4574,
                                        FStar_Pervasives_Native.None)
                                       in
                                    [uu____4569]  in
                                  (FStar_TypeChecker_NBETerm.Unknown,
                                    FStar_Pervasives_Native.None) ::
                                    uu____4562
                                   in
                                uu____4549 :: uu____4555  in
                              (FStar_TypeChecker_NBETerm.Unknown,
                                FStar_Pervasives_Native.None) :: uu____4542
                               in
                            FStar_List.append maybe_range_arg uu____4535  in
                          FStar_List.append uu____4490 uu____4528  in
                        iapp cfg uu____4470 uu____4489)
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____4603);
                      FStar_Syntax_Syntax.pos = uu____4604;
                      FStar_Syntax_Syntax.vars = uu____4605;_},(e2,uu____4607)::[])
                   ->
                   translate
                     (let uu___248_4648 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___248_4648.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___248_4648.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___248_4648.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___248_4648.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___248_4648.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___248_4648.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___248_4648.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___248_4648.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app uu____4649 -> translate cfg bs e1
               | uu____4666 ->
                   let uu____4667 =
                     let uu____4668 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____4668
                      in
                   failwith uu____4667)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____4669  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____4669 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____4693 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____4693
              then
                let ed =
                  let uu____4695 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____4695
                   in
                let cfg' =
                  let uu___249_4697 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___249_4697.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___249_4697.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___249_4697.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___249_4697.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___249_4697.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___249_4697.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___249_4697.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___249_4697.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let uu____4698 =
                  let uu____4699 =
                    let uu____4700 =
                      FStar_Syntax_Util.un_uinst
                        (FStar_Pervasives_Native.snd
                           ed.FStar_Syntax_Syntax.return_repr)
                       in
                    translate cfg' [] uu____4700  in
                  iapp cfg uu____4699
                    [((FStar_TypeChecker_NBETerm.Univ
                         FStar_Syntax_Syntax.U_unknown),
                       FStar_Pervasives_Native.None)]
                   in
                let uu____4713 =
                  let uu____4714 =
                    let uu____4719 = translate cfg' bs ty  in
                    (uu____4719, FStar_Pervasives_Native.None)  in
                  let uu____4720 =
                    let uu____4727 =
                      let uu____4732 = translate cfg' bs e1  in
                      (uu____4732, FStar_Pervasives_Native.None)  in
                    [uu____4727]  in
                  uu____4714 :: uu____4720  in
                iapp cfg uu____4698 uu____4713
              else
                (let uu____4746 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____4746 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____4749 =
                       let uu____4750 = FStar_Ident.text_of_lid msrc  in
                       let uu____4751 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____4750 uu____4751
                        in
                     failwith uu____4749
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____4752;
                       FStar_TypeChecker_Env.mtarget = uu____4753;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____4754;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____4776 =
                       let uu____4777 = FStar_Ident.text_of_lid msrc  in
                       let uu____4778 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____4777 uu____4778
                        in
                     failwith uu____4776
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____4779;
                       FStar_TypeChecker_Env.mtarget = uu____4780;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____4781;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____4820 =
                         let uu____4823 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____4823
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____4820
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___250_4839 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___250_4839.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___250_4839.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___250_4839.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___250_4839.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___250_4839.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___250_4839.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___250_4839.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___250_4839.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let uu____4840 = translate cfg' [] lift_lam  in
                     let uu____4841 =
                       let uu____4842 =
                         let uu____4847 = translate cfg bs e1  in
                         (uu____4847, FStar_Pervasives_Native.None)  in
                       [uu____4842]  in
                     iapp cfg uu____4840 uu____4841)

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____4871  ->
           let uu____4872 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____4872);
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
           let uu____4875 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____4875 FStar_Syntax_Util.exp_int
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
           let uu____4913 =
             FStar_List.fold_left
               (fun uu____4954  ->
                  fun tf  ->
                    match uu____4954 with
                    | (args,accus) ->
                        let uu____5004 = tf ()  in
                        (match uu____5004 with
                         | (xt,q) ->
                             let x1 =
                               let uu____5024 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____5024
                                in
                             let uu____5025 =
                               let uu____5028 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____5028 :: accus  in
                             (((x1, q) :: args), uu____5025))) ([], []) targs
              in
           (match uu____4913 with
            | (args,accus) ->
                let body =
                  let uu____5072 = f accus  in readback cfg uu____5072  in
                FStar_Syntax_Util.abs args body FStar_Pervasives_Native.None)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____5096 =
               let uu____5097 =
                 let uu____5098 = targ ()  in
                 FStar_Pervasives_Native.fst uu____5098  in
               readback cfg uu____5097  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____5096
              in
           let body =
             let uu____5104 =
               let uu____5105 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____5105  in
             readback cfg uu____5104  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____5144  ->
                  match uu____5144 with
                  | (x1,q) ->
                      let uu____5155 = readback cfg x1  in (uu____5155, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____5174 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____5181::uu____5182 ->
                let uu____5185 =
                  let uu____5188 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____5188
                    (FStar_List.rev us)
                   in
                apply uu____5185
            | [] ->
                let uu____5189 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____5189)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____5230  ->
                  match uu____5230 with
                  | (x1,q) ->
                      let uu____5241 = readback cfg x1  in (uu____5241, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____5260 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____5267::uu____5268 ->
                let uu____5271 =
                  let uu____5274 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____5274
                    (FStar_List.rev us)
                   in
                apply uu____5271
            | [] ->
                let uu____5275 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____5275)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____5322  ->
                  match uu____5322 with
                  | (x1,q) ->
                      let uu____5333 = readback cfg x1  in (uu____5333, q))
               ts
              in
           let uu____5334 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____5334 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____5394  ->
                  match uu____5394 with
                  | (x1,q) ->
                      let uu____5405 = readback cfg x1  in (uu____5405, q))
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
            | uu____5435 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app cfg hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____5522 = curry hd1 args1  in
                 app cfg uu____5522 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
              in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef  in
           let uu____5524 = test_args ts args_no  in
           if uu____5524
           then
             let uu____5525 =
               let uu____5526 =
                 let uu____5527 = make_rec_env lbs bs  in
                 translate_letbinding cfg uu____5527 lb  in
               curry uu____5526 ts  in
             readback cfg uu____5525
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
                  (fun uu____5572  ->
                     match uu____5572 with
                     | (x1,q) ->
                         let uu____5583 = readback cfg x1  in (uu____5583, q))
                  ts
                 in
              match ts with
              | [] -> head1
              | uu____5588 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Arrow uu____5595 ->
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
    match projectee with | Primops  -> true | uu____5636 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____5643 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5659 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5679 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____5692 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____5698 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___244_5703  ->
    match uu___244_5703 with
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
          let uu___251_5730 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___252_5733 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___252_5733.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___252_5733.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___252_5733.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___252_5733.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___252_5733.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___252_5733.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___252_5733.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___252_5733.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___252_5733.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___252_5733.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___252_5733.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___252_5733.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___252_5733.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___252_5733.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___252_5733.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___252_5733.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___252_5733.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___252_5733.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___252_5733.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___252_5733.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___252_5733.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___252_5733.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___252_5733.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___252_5733.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___251_5730.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___251_5730.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___251_5730.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___251_5730.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___251_5730.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___251_5730.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___251_5730.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___251_5730.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____5737  ->
             let uu____5738 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____5738);
        (let uu____5739 = translate cfg1 [] e  in readback cfg1 uu____5739)
  
let (test_normalize :
  step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg =
          let uu____5760 = FStar_List.map step_as_normalizer_step steps  in
          FStar_TypeChecker_Cfg.config uu____5760 env  in
        let cfg1 =
          let uu___253_5764 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___254_5767 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___254_5767.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___254_5767.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___254_5767.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___254_5767.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___254_5767.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___254_5767.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___254_5767.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___254_5767.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___254_5767.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___254_5767.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___254_5767.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___254_5767.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___254_5767.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___254_5767.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___254_5767.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___254_5767.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___254_5767.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___254_5767.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___254_5767.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___254_5767.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___254_5767.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___254_5767.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___254_5767.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___254_5767.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___253_5764.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___253_5764.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___253_5764.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___253_5764.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___253_5764.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___253_5764.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___253_5764.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___253_5764.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____5771  ->
             let uu____5772 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____5772);
        (let uu____5773 = translate cfg1 [] e  in readback cfg1 uu____5773)
  