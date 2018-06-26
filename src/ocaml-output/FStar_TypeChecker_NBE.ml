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
  
let (app :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.t ->
        FStar_Syntax_Syntax.aqual -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun f  ->
      fun x  ->
        fun q  ->
          debug cfg
            (fun uu____1576  ->
               let uu____1577 = FStar_TypeChecker_NBETerm.t_to_string f  in
               let uu____1578 = FStar_TypeChecker_NBETerm.t_to_string x  in
               FStar_Util.print2 "When creating app: %s applied to %s\n"
                 uu____1577 uu____1578);
          (match f with
           | FStar_TypeChecker_NBETerm.Lam (f1,uu____1580,uu____1581) ->
               f1 [x]
           | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
               FStar_TypeChecker_NBETerm.Accu (a, ((x, q) :: ts))
           | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
               (match x with
                | FStar_TypeChecker_NBETerm.Univ u ->
                    FStar_TypeChecker_NBETerm.Construct (i, (u :: us), ts)
                | uu____1662 ->
                    FStar_TypeChecker_NBETerm.Construct
                      (i, us, ((x, q) :: ts)))
           | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
               (match x with
                | FStar_TypeChecker_NBETerm.Univ u ->
                    FStar_TypeChecker_NBETerm.FV (i, (u :: us), ts)
                | uu____1703 ->
                    FStar_TypeChecker_NBETerm.FV (i, us, ((x, q) :: ts)))
           | FStar_TypeChecker_NBETerm.Constant uu____1716 ->
               failwith "Ill-typed application"
           | FStar_TypeChecker_NBETerm.Univ uu____1717 ->
               failwith "Ill-typed application"
           | FStar_TypeChecker_NBETerm.Type_t uu____1718 ->
               failwith "Ill-typed application"
           | FStar_TypeChecker_NBETerm.Unknown  ->
               failwith "Ill-typed application"
           | FStar_TypeChecker_NBETerm.Arrow uu____1719 ->
               failwith "Ill-typed application")
  
let rec (iapp :
  FStar_TypeChecker_NBETerm.t ->
    FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun f  ->
    fun args  ->
      match f with
      | FStar_TypeChecker_NBETerm.Lam (f1,targs,n1) ->
          let m = FStar_List.length args  in
          if m < n1
          then
            let uu____1902 = FStar_List.splitAt m targs  in
            (match uu____1902 with
             | (uu____1936,targs') ->
                 FStar_TypeChecker_NBETerm.Lam
                   (((fun l  ->
                        let uu____1993 =
                          map_append FStar_Pervasives_Native.fst args l  in
                        f1 uu____1993)), targs', (n1 - m)))
          else
            if m = n1
            then
              (let uu____2009 =
                 FStar_List.map FStar_Pervasives_Native.fst args  in
               f1 uu____2009)
            else
              (let uu____2017 = FStar_List.splitAt n1 args  in
               match uu____2017 with
               | (args1,args') ->
                   let uu____2064 =
                     let uu____2065 =
                       FStar_List.map FStar_Pervasives_Native.fst args1  in
                     f1 uu____2065  in
                   iapp uu____2064 args')
      | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
          FStar_TypeChecker_NBETerm.Accu (a, (FStar_List.rev_append args ts))
      | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
          let rec aux args1 us1 ts1 =
            match args1 with
            | (FStar_TypeChecker_NBETerm.Univ u,uu____2184)::args2 ->
                aux args2 (u :: us1) ts1
            | a::args2 -> aux args2 us1 (a :: ts1)
            | [] -> (us1, ts1)  in
          let uu____2228 = aux args us ts  in
          (match uu____2228 with
           | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
      | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
          let rec aux args1 us1 ts1 =
            match args1 with
            | (FStar_TypeChecker_NBETerm.Univ u,uu____2355)::args2 ->
                aux args2 (u :: us1) ts1
            | a::args2 -> aux args2 us1 (a :: ts1)
            | [] -> (us1, ts1)  in
          let uu____2399 = aux args us ts  in
          (match uu____2399 with
           | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
      | FStar_TypeChecker_NBETerm.Constant uu____2438 ->
          failwith "Ill-typed application"
      | FStar_TypeChecker_NBETerm.Univ uu____2439 ->
          failwith "Ill-typed application"
      | FStar_TypeChecker_NBETerm.Type_t uu____2440 ->
          failwith "Ill-typed application"
      | FStar_TypeChecker_NBETerm.Unknown  ->
          failwith "Ill-typed application"
      | FStar_TypeChecker_NBETerm.Arrow uu____2441 ->
          failwith "Ill-typed application"

and (translate_fv :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.fv -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun fvar1  ->
        let debug1 = debug cfg  in
        let qninfo =
          let uu____2474 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2475 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2474 uu____2475  in
        let uu____2476 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2476
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2482 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2484  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2482 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2490  ->
                     let uu____2491 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2491);
                FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2499;
                        FStar_Syntax_Syntax.sigquals = uu____2500;
                        FStar_Syntax_Syntax.sigmeta = uu____2501;
                        FStar_Syntax_Syntax.sigattrs = uu____2502;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2571  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2579  ->
                                 let uu____2580 =
                                   let uu____2581 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2581
                                    in
                                 let uu____2582 =
                                   let uu____2583 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2583
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2580 uu____2582);
                            debug1
                              (fun uu____2591  ->
                                 let uu____2592 =
                                   let uu____2593 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2593
                                    in
                                 let uu____2594 =
                                   let uu____2595 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2595
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2592 uu____2594);
                            (let uu____2596 =
                               FStar_TypeChecker_Cfg.is_prim_step cfg fvar1
                                in
                             if uu____2596
                             then FStar_TypeChecker_NBETerm.mkFV fvar1 [] []
                             else translate_letbinding cfg [] lb))
                     | FStar_Pervasives_Native.None  ->
                         failwith
                           "Could not find mutually recursive definition")
                | uu____2602 ->
                    (debug1
                       (fun uu____2608  ->
                          let uu____2609 =
                            FStar_Syntax_Print.fv_to_string fvar1  in
                          FStar_Util.print1 "(2) Decided to not unfold %s\n"
                            uu____2609);
                     FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2617;
                        FStar_Syntax_Syntax.sigquals = uu____2618;
                        FStar_Syntax_Syntax.sigmeta = uu____2619;
                        FStar_Syntax_Syntax.sigattrs = uu____2620;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2689  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2697  ->
                                 let uu____2698 =
                                   let uu____2699 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2699
                                    in
                                 let uu____2700 =
                                   let uu____2701 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2701
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2698 uu____2700);
                            debug1
                              (fun uu____2709  ->
                                 let uu____2710 =
                                   let uu____2711 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2711
                                    in
                                 let uu____2712 =
                                   let uu____2713 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2713
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2710 uu____2712);
                            (let uu____2714 =
                               FStar_TypeChecker_Cfg.is_prim_step cfg fvar1
                                in
                             if uu____2714
                             then FStar_TypeChecker_NBETerm.mkFV fvar1 [] []
                             else translate_letbinding cfg [] lb))
                     | FStar_Pervasives_Native.None  ->
                         failwith
                           "Could not find mutually recursive definition")
                | uu____2720 ->
                    (debug1
                       (fun uu____2726  ->
                          let uu____2727 =
                            FStar_Syntax_Print.fv_to_string fvar1  in
                          FStar_Util.print1 "(2) Decided to not unfold %s\n"
                            uu____2727);
                     FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))

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
        match us with
        | [] -> translate cfg bs lb.FStar_Syntax_Syntax.lbdef
        | uu____2772 ->
            let uu____2775 =
              let uu____2796 =
                FStar_List.map
                  (fun uu____2817  ->
                     fun uu____2818  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____2796,
                (FStar_List.length us))
               in
            FStar_TypeChecker_NBETerm.Lam uu____2775

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____2864 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____2864
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____2870 ->
        let uu____2871 =
          let uu____2872 =
            let uu____2873 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____2873 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____2872  in
        failwith uu____2871

and (translate_pat : FStar_Syntax_Syntax.pat -> FStar_TypeChecker_NBETerm.t)
  =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2876 = translate_constant c  in
        FStar_TypeChecker_NBETerm.Constant uu____2876
    | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
        let uu____2895 = FStar_TypeChecker_NBETerm.mkConstruct cfv [] []  in
        let uu____2900 =
          FStar_List.map
            (fun uu____2915  ->
               match uu____2915 with
               | (p1,uu____2927) ->
                   let uu____2928 = translate_pat p1  in
                   (uu____2928, FStar_Pervasives_Native.None)) pats
           in
        iapp uu____2895 uu____2900
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
          (fun uu____2959  ->
             let uu____2960 =
               let uu____2961 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2961  in
             let uu____2962 =
               let uu____2963 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2963  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2960 uu____2962);
        debug1
          (fun uu____2969  ->
             let uu____2970 =
               let uu____2971 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____2971  in
             FStar_Util.print1 "BS list: %s\n" uu____2970);
        (let uu____2976 =
           let uu____2977 = FStar_Syntax_Subst.compress e  in
           uu____2977.FStar_Syntax_Syntax.n  in
         match uu____2976 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2980,uu____2981) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3019 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3019
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3036  ->
                   let uu____3037 = FStar_Syntax_Print.tag_of_term t  in
                   let uu____3038 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3039 =
                     let uu____3040 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3040
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print3 "Term with univs: %s - %s\nUniv %s\n"
                     uu____3037 uu____3038 uu____3039);
              (let uu____3045 = translate cfg bs t  in
               FStar_List.fold_left
                 (fun head1  ->
                    fun u  ->
                      let uu____3051 = translate_univ bs u  in
                      app cfg head1 uu____3051 FStar_Pervasives_Native.None)
                 uu____3045 us))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3053 =
               let uu____3054 = translate_univ bs u  in un_univ uu____3054
                in
             FStar_TypeChecker_NBETerm.Type_t uu____3053
         | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
             (debug_term e; failwith "Tm_arrow: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_refine (db,tm) ->
             failwith "Tm_refine: Not yet implemented"
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3085,uu____3086) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____3147,uu____3148) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____3173) ->
             let uu____3198 =
               let uu____3219 =
                 FStar_List.map
                   (fun x  ->
                      fun uu____3254  ->
                        let uu____3255 =
                          translate cfg bs
                            (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                           in
                        (uu____3255, (FStar_Pervasives_Native.snd x))) xs
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____3219, (FStar_List.length xs))
                in
             FStar_TypeChecker_NBETerm.Lam uu____3198
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3287;
                FStar_Syntax_Syntax.vars = uu____3288;_},arg::more::args)
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let uu____3348 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3348 with
              | (reifyh,uu____3366) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app reifyh [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3410 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3410)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3419;
                FStar_Syntax_Syntax.vars = uu____3420;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___405_3462 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___405_3462.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___405_3462.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___405_3462.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___405_3462.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___405_3462.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___405_3462.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___405_3462.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___405_3462.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____3500  ->
                   let uu____3501 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3502 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3501
                     uu____3502);
              (let uu____3503 = translate cfg bs head1  in
               let uu____3504 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3526 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3526, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp uu____3503 uu____3504))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3611  ->
                         let uu____3612 =
                           let uu____3613 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3636  ->
                                     match uu____3636 with
                                     | (x,q) ->
                                         let uu____3649 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3649))
                              in
                           FStar_All.pipe_right uu____3613
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3612);
                    (let uu____3653 = pickBranch cfg scrut1 branches  in
                     match uu____3653 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____3674 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____3674 branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   let uu____3692 = pickBranch cfg scrut1 branches  in
                   (match uu____3692 with
                    | FStar_Pervasives_Native.Some (branch1,[]) ->
                        translate cfg bs branch1
                    | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                        translate cfg (arg :: bs) branch1
                    | FStar_Pervasives_Native.None  ->
                        FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                          make_branches
                    | FStar_Pervasives_Native.Some (uu____3726,hd1::tl1) ->
                        failwith
                          "Impossible: Matching on constants cannot bind more than one variable")
               | uu____3739 ->
                   FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                     make_branches
             
             and make_branches readback1 =
               let rec process_pattern bs1 p =
                 let uu____3772 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____3806 =
                         FStar_List.fold_left
                           (fun uu____3844  ->
                              fun uu____3845  ->
                                match (uu____3844, uu____3845) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3926 = process_pattern bs2 arg
                                       in
                                    (match uu____3926 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3806 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____4015 =
                           let uu____4016 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4016  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4015
                          in
                       let uu____4017 =
                         let uu____4020 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4020 :: bs1  in
                       (uu____4017, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____4025 =
                           let uu____4026 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4026  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4025
                          in
                       let uu____4027 =
                         let uu____4030 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4030 :: bs1  in
                       (uu____4027, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____4040 =
                           let uu____4041 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4041  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4040
                          in
                       let uu____4042 =
                         let uu____4045 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4045 :: bs1  in
                       let uu____4046 =
                         let uu____4047 =
                           let uu____4054 =
                             let uu____4057 = translate cfg bs1 tm  in
                             readback1 uu____4057  in
                           (x, uu____4054)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____4047  in
                       (uu____4042, uu____4046)
                    in
                 match uu____3772 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___406_4077 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___406_4077.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____4096  ->
                    match uu____4096 with
                    | (pat,when_clause,e1) ->
                        let uu____4118 = process_pattern bs pat  in
                        (match uu____4118 with
                         | (bs',pat') ->
                             let uu____4131 =
                               let uu____4132 =
                                 let uu____4135 = translate cfg bs' e1  in
                                 readback1 uu____4135  in
                               (pat', when_clause, uu____4132)  in
                             FStar_Syntax_Util.branch uu____4131)) branches
              in let uu____4144 = translate cfg bs scrut  in case uu____4144
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
             let uu____4217 = make_rec_env lbs bs  in
             translate cfg uu____4217 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4221) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_lazy uu____4226 ->
             failwith "Not yet handled"
         | FStar_Syntax_Syntax.Tm_quoted (uu____4227,uu____4228) ->
             failwith "Not yet handled")

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____4233  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____4233 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____4268 =
                     let uu____4277 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____4277
                      in
                   (match uu____4268 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____4284 =
                          let uu____4285 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____4285
                           in
                        failwith uu____4284
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___407_4299 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___407_4299.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___407_4299.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___407_4299.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___407_4299.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___407_4299.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___407_4299.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___407_4299.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___407_4299.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____4306 =
                            let uu____4313 =
                              let uu____4314 =
                                let uu____4333 =
                                  let uu____4342 =
                                    let uu____4349 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____4349,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____4342]  in
                                (uu____4333, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____4314  in
                            FStar_Syntax_Syntax.mk uu____4313  in
                          uu____4306 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____4386 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____4386
                          then
                            let uu____4393 =
                              let uu____4398 =
                                let uu____4399 =
                                  FStar_Syntax_Embeddings.embed
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____4399  in
                              (uu____4398, FStar_Pervasives_Native.None)  in
                            let uu____4400 =
                              let uu____4407 =
                                let uu____4412 =
                                  let uu____4413 =
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____4413  in
                                (uu____4412, FStar_Pervasives_Native.None)
                                 in
                              [uu____4407]  in
                            uu____4393 :: uu____4400
                          else []  in
                        let uu____4431 =
                          let uu____4432 =
                            let uu____4433 =
                              FStar_Syntax_Util.un_uinst
                                (FStar_Pervasives_Native.snd
                                   ed.FStar_Syntax_Syntax.bind_repr)
                               in
                            translate cfg' [] uu____4433  in
                          iapp uu____4432
                            [((FStar_TypeChecker_NBETerm.Univ
                                 FStar_Syntax_Syntax.U_unknown),
                               FStar_Pervasives_Native.None);
                            ((FStar_TypeChecker_NBETerm.Univ
                                FStar_Syntax_Syntax.U_unknown),
                              FStar_Pervasives_Native.None)]
                           in
                        let uu____4450 =
                          let uu____4451 =
                            let uu____4458 =
                              let uu____4463 =
                                translate cfg' bs
                                  lb.FStar_Syntax_Syntax.lbtyp
                                 in
                              (uu____4463, FStar_Pervasives_Native.None)  in
                            let uu____4464 =
                              let uu____4471 =
                                let uu____4476 = translate cfg' bs ty  in
                                (uu____4476, FStar_Pervasives_Native.None)
                                 in
                              [uu____4471]  in
                            uu____4458 :: uu____4464  in
                          let uu____4489 =
                            let uu____4496 =
                              let uu____4503 =
                                let uu____4510 =
                                  let uu____4515 =
                                    translate cfg bs
                                      lb.FStar_Syntax_Syntax.lbdef
                                     in
                                  (uu____4515, FStar_Pervasives_Native.None)
                                   in
                                let uu____4516 =
                                  let uu____4523 =
                                    let uu____4530 =
                                      let uu____4535 =
                                        translate cfg bs body_lam  in
                                      (uu____4535,
                                        FStar_Pervasives_Native.None)
                                       in
                                    [uu____4530]  in
                                  (FStar_TypeChecker_NBETerm.Unknown,
                                    FStar_Pervasives_Native.None) ::
                                    uu____4523
                                   in
                                uu____4510 :: uu____4516  in
                              (FStar_TypeChecker_NBETerm.Unknown,
                                FStar_Pervasives_Native.None) :: uu____4503
                               in
                            FStar_List.append maybe_range_arg uu____4496  in
                          FStar_List.append uu____4451 uu____4489  in
                        iapp uu____4431 uu____4450)
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____4564);
                      FStar_Syntax_Syntax.pos = uu____4565;
                      FStar_Syntax_Syntax.vars = uu____4566;_},(e2,uu____4568)::[])
                   ->
                   translate
                     (let uu___408_4609 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___408_4609.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___408_4609.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___408_4609.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___408_4609.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___408_4609.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___408_4609.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___408_4609.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___408_4609.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | uu____4610 ->
                   let uu____4611 =
                     let uu____4612 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____4612
                      in
                   failwith uu____4611)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____4613  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____4613 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____4637 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____4637
              then
                let ed =
                  let uu____4639 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____4639
                   in
                let cfg' =
                  let uu___409_4641 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___409_4641.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___409_4641.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___409_4641.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___409_4641.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___409_4641.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___409_4641.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___409_4641.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___409_4641.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let uu____4642 =
                  let uu____4643 =
                    let uu____4644 =
                      FStar_Syntax_Util.un_uinst
                        (FStar_Pervasives_Native.snd
                           ed.FStar_Syntax_Syntax.return_repr)
                       in
                    translate cfg' [] uu____4644  in
                  iapp uu____4643
                    [((FStar_TypeChecker_NBETerm.Univ
                         FStar_Syntax_Syntax.U_unknown),
                       FStar_Pervasives_Native.None)]
                   in
                let uu____4657 =
                  let uu____4658 =
                    let uu____4663 = translate cfg' bs ty  in
                    (uu____4663, FStar_Pervasives_Native.None)  in
                  let uu____4664 =
                    let uu____4671 =
                      let uu____4676 = translate cfg' bs e1  in
                      (uu____4676, FStar_Pervasives_Native.None)  in
                    [uu____4671]  in
                  uu____4658 :: uu____4664  in
                iapp uu____4642 uu____4657
              else
                (let uu____4690 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____4690 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____4693 =
                       let uu____4694 = FStar_Ident.text_of_lid msrc  in
                       let uu____4695 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____4694 uu____4695
                        in
                     failwith uu____4693
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____4696;
                       FStar_TypeChecker_Env.mtarget = uu____4697;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____4698;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____4720 =
                       let uu____4721 = FStar_Ident.text_of_lid msrc  in
                       let uu____4722 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____4721 uu____4722
                        in
                     failwith uu____4720
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____4723;
                       FStar_TypeChecker_Env.mtarget = uu____4724;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____4725;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____4764 =
                         let uu____4767 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____4767
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____4764
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___410_4783 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___410_4783.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___410_4783.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___410_4783.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___410_4783.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___410_4783.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___410_4783.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___410_4783.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___410_4783.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let uu____4784 = translate cfg' [] lift_lam  in
                     let uu____4785 =
                       let uu____4786 =
                         let uu____4791 = translate cfg bs e1  in
                         (uu____4791, FStar_Pervasives_Native.None)  in
                       [uu____4786]  in
                     iapp uu____4784 uu____4785)

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____4815  ->
           let uu____4816 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____4816);
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
           let uu____4819 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____4819 FStar_Syntax_Util.exp_int
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
           let uu____4857 =
             FStar_List.fold_left
               (fun uu____4898  ->
                  fun tf  ->
                    match uu____4898 with
                    | (args,accus) ->
                        let uu____4948 = tf ()  in
                        (match uu____4948 with
                         | (xt,q) ->
                             let x1 =
                               let uu____4968 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____4968
                                in
                             let uu____4969 =
                               let uu____4972 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____4972 :: accus  in
                             (((x1, q) :: args), uu____4969))) ([], []) targs
              in
           (match uu____4857 with
            | (args,accus) ->
                let body =
                  let uu____5016 = f accus  in readback cfg uu____5016  in
                FStar_Syntax_Util.abs args body FStar_Pervasives_Native.None)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____5055  ->
                  match uu____5055 with
                  | (x1,q) ->
                      let uu____5066 = readback cfg x1  in (uu____5066, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____5085 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____5092::uu____5093 ->
                let uu____5096 =
                  let uu____5099 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____5099
                    (FStar_List.rev us)
                   in
                apply uu____5096
            | [] ->
                let uu____5100 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____5100)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____5141  ->
                  match uu____5141 with
                  | (x1,q) ->
                      let uu____5152 = readback cfg x1  in (uu____5152, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____5171 -> FStar_Syntax_Util.mk_app tm args1  in
           let tm uu____5185 =
             match us with
             | uu____5188::uu____5189 ->
                 let uu____5192 =
                   let uu____5195 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                       FStar_Pervasives_Native.None FStar_Range.dummyRange
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____5195
                     (FStar_List.rev us)
                    in
                 apply uu____5192
             | [] ->
                 let uu____5196 =
                   FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 apply uu____5196
              in
           let uu____5199 = FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
           (match uu____5199 with
            | FStar_Pervasives_Native.Some prim_step when
                prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                let l = FStar_List.length args1  in
                let uu____5208 =
                  if l = prim_step.FStar_TypeChecker_Cfg.arity
                  then (args1, [])
                  else
                    FStar_List.splitAt prim_step.FStar_TypeChecker_Cfg.arity
                      args1
                   in
                (match uu____5208 with
                 | (args_1,args_2) ->
                     let psc =
                       {
                         FStar_TypeChecker_Cfg.psc_range =
                           FStar_Range.dummyRange;
                         FStar_TypeChecker_Cfg.psc_subst =
                           (fun uu____5294  ->
                              if
                                prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                              then
                                failwith
                                  "Cannot handle primops that require substitution"
                              else [])
                       }  in
                     let uu____5296 =
                       prim_step.FStar_TypeChecker_Cfg.interpretation psc
                         args_1
                        in
                     (match uu____5296 with
                      | FStar_Pervasives_Native.Some tm1 ->
                          FStar_Syntax_Util.mk_app tm1 args_2
                      | FStar_Pervasives_Native.None  -> tm ()))
            | uu____5300 -> tm ())
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____5347  ->
                  match uu____5347 with
                  | (x1,q) ->
                      let uu____5358 = readback cfg x1  in (uu____5358, q))
               ts
              in
           let uu____5359 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____5359 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____5419  ->
                  match uu____5419 with
                  | (x1,q) ->
                      let uu____5430 = readback cfg x1  in (uu____5430, q))
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
            | uu____5460 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app cfg hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____5547 = curry hd1 args1  in
                 app cfg uu____5547 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
              in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef  in
           let uu____5549 = test_args ts args_no  in
           if uu____5549
           then
             let uu____5550 =
               let uu____5551 =
                 let uu____5552 = make_rec_env lbs bs  in
                 translate_letbinding cfg uu____5552 lb  in
               curry uu____5551 ts  in
             readback cfg uu____5550
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
                  (fun uu____5597  ->
                     match uu____5597 with
                     | (x1,q) ->
                         let uu____5608 = readback cfg x1  in (uu____5608, q))
                  ts
                 in
              match ts with
              | [] -> head1
              | uu____5613 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Arrow uu____5620 ->
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
    match projectee with | Primops  -> true | uu____5661 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____5668 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5684 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5704 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____5717 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____5723 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___404_5728  ->
    match uu___404_5728 with
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
          let uu___411_5755 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___412_5758 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___412_5758.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___412_5758.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___412_5758.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___412_5758.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___412_5758.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___412_5758.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___412_5758.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___412_5758.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___412_5758.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___412_5758.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___412_5758.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___412_5758.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___412_5758.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___412_5758.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___412_5758.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___412_5758.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___412_5758.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___412_5758.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___412_5758.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___412_5758.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___412_5758.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___412_5758.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___412_5758.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___412_5758.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___411_5755.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___411_5755.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___411_5755.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___411_5755.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___411_5755.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___411_5755.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___411_5755.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___411_5755.FStar_TypeChecker_Cfg.reifying)
          }  in
        let uu____5759 = translate cfg1 [] e  in readback cfg1 uu____5759
  
let (test_normalize :
  step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg =
          let uu____5780 = FStar_List.map step_as_normalizer_step steps  in
          FStar_TypeChecker_Cfg.config uu____5780 env  in
        let cfg1 =
          let uu___413_5784 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___414_5787 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___414_5787.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___414_5787.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___414_5787.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___414_5787.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___414_5787.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___414_5787.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___414_5787.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___414_5787.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___414_5787.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___414_5787.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___414_5787.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___414_5787.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___414_5787.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___414_5787.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___414_5787.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___414_5787.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___414_5787.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___414_5787.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___414_5787.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___414_5787.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___414_5787.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___414_5787.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___414_5787.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___414_5787.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___413_5784.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___413_5784.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___413_5784.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___413_5784.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___413_5784.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___413_5784.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___413_5784.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___413_5784.FStar_TypeChecker_Cfg.reifying)
          }  in
        let uu____5788 = translate cfg1 [] e  in readback cfg1 uu____5788
  