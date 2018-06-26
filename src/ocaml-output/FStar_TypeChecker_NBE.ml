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
    | FStar_Syntax_Syntax.Tm_uvar uu____866 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_refine uu____879 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_unknown  -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____887) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____894) ->
        let uu____915 = count_abstractions body  in
        (FStar_List.length xs) + uu____915
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____942 =
          let uu____943 = count_abstractions head1  in
          uu____943 - (FStar_List.length args)  in
        max uu____942 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____1002,uu____1003,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____1052,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1071) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1077,uu____1078) ->
        count_abstractions t1
    | uu____1119 -> (Prims.parse_int "0")
  
let (find_sigelt_in_gamma :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.env ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lid  ->
        let mapper uu____1164 =
          match uu____1164 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1247  ->
                         let uu____1248 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1248);
                    FStar_Pervasives_Native.Some elt)
               | uu____1249 -> FStar_Pervasives_Native.None)
           in
        let uu____1264 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1264 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1308 -> true
    | uu____1309 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | uu____1316 -> failwith "Not a universe"
  
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
              (uu____1329,uu____1330,uu____1331,uu____1332,uu____1333,uu____1334);
            FStar_Syntax_Syntax.sigrng = uu____1335;
            FStar_Syntax_Syntax.sigquals = uu____1336;
            FStar_Syntax_Syntax.sigmeta = uu____1337;
            FStar_Syntax_Syntax.sigattrs = uu____1338;_},uu____1339),uu____1340)
        -> true
    | uu____1395 -> false
  
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
            let uu____1420 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1420
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1424 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1424
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____1427 -> u2
        | FStar_Syntax_Syntax.U_unif uu____1428 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2  in
      let uu____1437 = aux u  in FStar_TypeChecker_NBETerm.Univ uu____1437
  
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
            let uu____1505 =
              let uu____1508 =
                FStar_TypeChecker_NBETerm.mkAccuRec lb lbs0 bs0  in
              uu____1508 :: bs1  in
            aux lbs' lbs0 uu____1505 bs0
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
           | FStar_Util.Inl uu____1530 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1534 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1534
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
            (fun uu____1562  ->
               let uu____1563 = FStar_TypeChecker_NBETerm.t_to_string f  in
               let uu____1564 = FStar_TypeChecker_NBETerm.t_to_string x  in
               FStar_Util.print2 "When creating app: %s applied to %s\n"
                 uu____1563 uu____1564);
          (match f with
           | FStar_TypeChecker_NBETerm.Lam (f1,uu____1566,uu____1567) ->
               f1 [x]
           | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
               FStar_TypeChecker_NBETerm.Accu (a, ((x, q) :: ts))
           | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
               (match x with
                | FStar_TypeChecker_NBETerm.Univ u ->
                    FStar_TypeChecker_NBETerm.Construct (i, (u :: us), ts)
                | uu____1648 ->
                    FStar_TypeChecker_NBETerm.Construct
                      (i, us, ((x, q) :: ts)))
           | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
               (match x with
                | FStar_TypeChecker_NBETerm.Univ u ->
                    FStar_TypeChecker_NBETerm.FV (i, (u :: us), ts)
                | uu____1689 ->
                    FStar_TypeChecker_NBETerm.FV (i, us, ((x, q) :: ts)))
           | FStar_TypeChecker_NBETerm.Constant uu____1702 ->
               failwith "Ill-typed application"
           | FStar_TypeChecker_NBETerm.Univ uu____1703 ->
               failwith "Ill-typed application"
           | FStar_TypeChecker_NBETerm.Type_t uu____1704 ->
               failwith "Ill-typed application"
           | FStar_TypeChecker_NBETerm.Unknown  ->
               failwith "Ill-typed application"
           | FStar_TypeChecker_NBETerm.Arrow uu____1705 ->
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
            let uu____1888 = FStar_List.splitAt m targs  in
            (match uu____1888 with
             | (uu____1922,targs') ->
                 FStar_TypeChecker_NBETerm.Lam
                   (((fun l  ->
                        let uu____1979 =
                          map_append FStar_Pervasives_Native.fst args l  in
                        f1 uu____1979)), targs', (n1 - m)))
          else
            if m = n1
            then
              (let uu____1995 =
                 FStar_List.map FStar_Pervasives_Native.fst args  in
               f1 uu____1995)
            else
              (let uu____2003 = FStar_List.splitAt n1 args  in
               match uu____2003 with
               | (args1,args') ->
                   let uu____2050 =
                     let uu____2051 =
                       FStar_List.map FStar_Pervasives_Native.fst args1  in
                     f1 uu____2051  in
                   iapp uu____2050 args')
      | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
          FStar_TypeChecker_NBETerm.Accu (a, (FStar_List.rev_append args ts))
      | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
          let rec aux args1 us1 ts1 =
            match args1 with
            | (FStar_TypeChecker_NBETerm.Univ u,uu____2170)::args2 ->
                aux args2 (u :: us1) ts1
            | a::args2 -> aux args2 us1 (a :: ts1)
            | [] -> (us1, ts1)  in
          let uu____2214 = aux args us ts  in
          (match uu____2214 with
           | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
      | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
          let rec aux args1 us1 ts1 =
            match args1 with
            | (FStar_TypeChecker_NBETerm.Univ u,uu____2341)::args2 ->
                aux args2 (u :: us1) ts1
            | a::args2 -> aux args2 us1 (a :: ts1)
            | [] -> (us1, ts1)  in
          let uu____2385 = aux args us ts  in
          (match uu____2385 with
           | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
      | FStar_TypeChecker_NBETerm.Constant uu____2424 ->
          failwith "Ill-typed application"
      | FStar_TypeChecker_NBETerm.Univ uu____2425 ->
          failwith "Ill-typed application"
      | FStar_TypeChecker_NBETerm.Type_t uu____2426 ->
          failwith "Ill-typed application"
      | FStar_TypeChecker_NBETerm.Unknown  ->
          failwith "Ill-typed application"
      | FStar_TypeChecker_NBETerm.Arrow uu____2427 ->
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
          let uu____2460 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2461 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2460 uu____2461  in
        let uu____2462 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2462
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2468 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2470  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2468 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2476  ->
                     let uu____2477 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2477);
                FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2485;
                        FStar_Syntax_Syntax.sigquals = uu____2486;
                        FStar_Syntax_Syntax.sigmeta = uu____2487;
                        FStar_Syntax_Syntax.sigattrs = uu____2488;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2557  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2565  ->
                                 let uu____2566 =
                                   let uu____2567 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2567
                                    in
                                 let uu____2568 =
                                   let uu____2569 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2569
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2566 uu____2568);
                            debug1
                              (fun uu____2577  ->
                                 let uu____2578 =
                                   let uu____2579 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2579
                                    in
                                 let uu____2580 =
                                   let uu____2581 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2581
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2578 uu____2580);
                            (let uu____2582 =
                               FStar_TypeChecker_Cfg.is_prim_step cfg fvar1
                                in
                             if uu____2582
                             then FStar_TypeChecker_NBETerm.mkFV fvar1 [] []
                             else translate_letbinding cfg [] lb))
                     | FStar_Pervasives_Native.None  ->
                         failwith
                           "Could not find mutually recursive definition")
                | uu____2588 ->
                    (debug1
                       (fun uu____2594  ->
                          let uu____2595 =
                            FStar_Syntax_Print.fv_to_string fvar1  in
                          FStar_Util.print1 "(2) Decided to not unfold %s\n"
                            uu____2595);
                     FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2603;
                        FStar_Syntax_Syntax.sigquals = uu____2604;
                        FStar_Syntax_Syntax.sigmeta = uu____2605;
                        FStar_Syntax_Syntax.sigattrs = uu____2606;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2675  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2683  ->
                                 let uu____2684 =
                                   let uu____2685 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2685
                                    in
                                 let uu____2686 =
                                   let uu____2687 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2687
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2684 uu____2686);
                            debug1
                              (fun uu____2695  ->
                                 let uu____2696 =
                                   let uu____2697 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2697
                                    in
                                 let uu____2698 =
                                   let uu____2699 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2699
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2696 uu____2698);
                            (let uu____2700 =
                               FStar_TypeChecker_Cfg.is_prim_step cfg fvar1
                                in
                             if uu____2700
                             then FStar_TypeChecker_NBETerm.mkFV fvar1 [] []
                             else translate_letbinding cfg [] lb))
                     | FStar_Pervasives_Native.None  ->
                         failwith
                           "Could not find mutually recursive definition")
                | uu____2706 ->
                    (debug1
                       (fun uu____2712  ->
                          let uu____2713 =
                            FStar_Syntax_Print.fv_to_string fvar1  in
                          FStar_Util.print1 "(2) Decided to not unfold %s\n"
                            uu____2713);
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
        let uu____2758 =
          let uu____2779 =
            FStar_List.map
              (fun uu____2800  ->
                 fun uu____2801  ->
                   FStar_All.pipe_left id1
                     ((FStar_TypeChecker_NBETerm.Constant
                         FStar_TypeChecker_NBETerm.Unit),
                       FStar_Pervasives_Native.None)) us
             in
          ((fun us1  ->
              translate cfg (FStar_List.rev_append us1 bs)
                lb.FStar_Syntax_Syntax.lbdef), uu____2779,
            (FStar_List.length us))
           in
        FStar_TypeChecker_NBETerm.Lam uu____2758

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____2847 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____2847
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____2853 ->
        let uu____2854 =
          let uu____2855 =
            let uu____2856 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____2856 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____2855  in
        failwith uu____2854

and (translate_pat : FStar_Syntax_Syntax.pat -> FStar_TypeChecker_NBETerm.t)
  =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2859 = translate_constant c  in
        FStar_TypeChecker_NBETerm.Constant uu____2859
    | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
        let uu____2878 = FStar_TypeChecker_NBETerm.mkConstruct cfv [] []  in
        let uu____2883 =
          FStar_List.map
            (fun uu____2898  ->
               match uu____2898 with
               | (p1,uu____2910) ->
                   let uu____2911 = translate_pat p1  in
                   (uu____2911, FStar_Pervasives_Native.None)) pats
           in
        iapp uu____2878 uu____2883
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
          (fun uu____2942  ->
             let uu____2943 =
               let uu____2944 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2944  in
             let uu____2945 =
               let uu____2946 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2946  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2943 uu____2945);
        debug1
          (fun uu____2952  ->
             let uu____2953 =
               let uu____2954 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____2954  in
             FStar_Util.print1 "BS list: %s\n" uu____2953);
        (let uu____2959 =
           let uu____2960 = FStar_Syntax_Subst.compress e  in
           uu____2960.FStar_Syntax_Syntax.n  in
         match uu____2959 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2963,uu____2964) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3002 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3002
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3019  ->
                   let uu____3020 = FStar_Syntax_Print.tag_of_term t  in
                   let uu____3021 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3022 =
                     let uu____3023 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3023
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print3 "Term with univs: %s - %s\nUniv %s\n"
                     uu____3020 uu____3021 uu____3022);
              (let uu____3028 = translate cfg bs t  in
               FStar_List.fold_left
                 (fun head1  ->
                    fun u  ->
                      let uu____3034 = translate_univ bs u  in
                      app cfg head1 uu____3034 FStar_Pervasives_Native.None)
                 uu____3028 us))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3036 =
               let uu____3037 = translate_univ bs u  in un_univ uu____3037
                in
             FStar_TypeChecker_NBETerm.Type_t uu____3036
         | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
             (debug_term e; failwith "Tm_arrow: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_refine (db,tm) ->
             failwith "Tm_refine: Not yet implemented"
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3064,uu____3065) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____3126,uu____3127) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____3148) ->
             let uu____3169 =
               let uu____3190 =
                 FStar_List.map
                   (fun x  ->
                      fun uu____3219  ->
                        let uu____3220 =
                          translate cfg bs
                            (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                           in
                        (uu____3220, (FStar_Pervasives_Native.snd x))) xs
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____3190, (FStar_List.length xs))
                in
             FStar_TypeChecker_NBETerm.Lam uu____3169
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3244;
                FStar_Syntax_Syntax.vars = uu____3245;_},arg::more::args)
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let uu____3293 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3293 with
              | (reifyh,uu____3309) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app reifyh [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3345 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3345)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3352;
                FStar_Syntax_Syntax.vars = uu____3353;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___241_3387 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___241_3387.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___241_3387.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___241_3387.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___241_3387.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___241_3387.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___241_3387.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___241_3387.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___241_3387.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____3419  ->
                   let uu____3420 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3421 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3420
                     uu____3421);
              (let uu____3422 = translate cfg bs head1  in
               let uu____3423 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3439 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3439, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp uu____3422 uu____3423))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3518  ->
                         let uu____3519 =
                           let uu____3520 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3543  ->
                                     match uu____3543 with
                                     | (x,q) ->
                                         let uu____3556 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3556))
                              in
                           FStar_All.pipe_right uu____3520
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3519);
                    (let uu____3560 = pickBranch cfg scrut1 branches  in
                     match uu____3560 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____3581 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____3581 branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   let uu____3599 = pickBranch cfg scrut1 branches  in
                   (match uu____3599 with
                    | FStar_Pervasives_Native.Some (branch1,[]) ->
                        translate cfg bs branch1
                    | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                        translate cfg (arg :: bs) branch1
                    | FStar_Pervasives_Native.None  ->
                        FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                          make_branches
                    | FStar_Pervasives_Native.Some (uu____3633,hd1::tl1) ->
                        failwith
                          "Impossible: Matching on constants cannot bind more than one variable")
               | uu____3646 ->
                   FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                     make_branches
             
             and make_branches readback1 =
               let rec process_pattern bs1 p =
                 let uu____3679 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____3713 =
                         FStar_List.fold_left
                           (fun uu____3751  ->
                              fun uu____3752  ->
                                match (uu____3751, uu____3752) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3833 = process_pattern bs2 arg
                                       in
                                    (match uu____3833 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3713 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____3922 =
                           let uu____3923 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3923  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3922
                          in
                       let uu____3924 =
                         let uu____3927 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3927 :: bs1  in
                       (uu____3924, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3932 =
                           let uu____3933 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3933  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3932
                          in
                       let uu____3934 =
                         let uu____3937 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3937 :: bs1  in
                       (uu____3934, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3947 =
                           let uu____3948 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3948  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3947
                          in
                       let uu____3949 =
                         let uu____3952 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3952 :: bs1  in
                       let uu____3953 =
                         let uu____3954 =
                           let uu____3961 =
                             let uu____3964 = translate cfg bs1 tm  in
                             readback1 uu____3964  in
                           (x, uu____3961)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3954  in
                       (uu____3949, uu____3953)
                    in
                 match uu____3679 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___242_3984 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___242_3984.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____4003  ->
                    match uu____4003 with
                    | (pat,when_clause,e1) ->
                        let uu____4025 = process_pattern bs pat  in
                        (match uu____4025 with
                         | (bs',pat') ->
                             let uu____4038 =
                               let uu____4039 =
                                 let uu____4042 = translate cfg bs' e1  in
                                 readback1 uu____4042  in
                               (pat', when_clause, uu____4039)  in
                             FStar_Syntax_Util.branch uu____4038)) branches
              in let uu____4051 = translate cfg bs scrut  in case uu____4051
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
             let uu____4124 = make_rec_env lbs bs  in
             translate cfg uu____4124 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4128) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_lazy uu____4133 ->
             failwith "Not yet handled"
         | FStar_Syntax_Syntax.Tm_quoted (uu____4134,uu____4135) ->
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
  fun uu____4140  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____4140 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____4175 =
                     let uu____4184 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____4184
                      in
                   (match uu____4175 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____4191 =
                          let uu____4192 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____4192
                           in
                        failwith uu____4191
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___243_4206 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___243_4206.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___243_4206.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___243_4206.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___243_4206.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___243_4206.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___243_4206.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___243_4206.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___243_4206.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____4213 =
                            let uu____4220 =
                              let uu____4221 =
                                let uu____4238 =
                                  let uu____4245 =
                                    let uu____4250 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____4250,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____4245]  in
                                (uu____4238, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____4221  in
                            FStar_Syntax_Syntax.mk uu____4220  in
                          uu____4213 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____4279 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____4279
                          then
                            let uu____4286 =
                              let uu____4291 =
                                let uu____4292 =
                                  FStar_Syntax_Embeddings.embed
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____4292  in
                              (uu____4291, FStar_Pervasives_Native.None)  in
                            let uu____4293 =
                              let uu____4300 =
                                let uu____4305 =
                                  let uu____4306 =
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____4306  in
                                (uu____4305, FStar_Pervasives_Native.None)
                                 in
                              [uu____4300]  in
                            uu____4286 :: uu____4293
                          else []  in
                        let uu____4324 =
                          let uu____4325 =
                            let uu____4326 =
                              FStar_Syntax_Util.un_uinst
                                (FStar_Pervasives_Native.snd
                                   ed.FStar_Syntax_Syntax.bind_repr)
                               in
                            translate cfg' [] uu____4326  in
                          iapp uu____4325
                            [((FStar_TypeChecker_NBETerm.Univ
                                 FStar_Syntax_Syntax.U_unknown),
                               FStar_Pervasives_Native.None);
                            ((FStar_TypeChecker_NBETerm.Univ
                                FStar_Syntax_Syntax.U_unknown),
                              FStar_Pervasives_Native.None)]
                           in
                        let uu____4343 =
                          let uu____4344 =
                            let uu____4351 =
                              let uu____4356 =
                                translate cfg' bs
                                  lb.FStar_Syntax_Syntax.lbtyp
                                 in
                              (uu____4356, FStar_Pervasives_Native.None)  in
                            let uu____4357 =
                              let uu____4364 =
                                let uu____4369 = translate cfg' bs ty  in
                                (uu____4369, FStar_Pervasives_Native.None)
                                 in
                              [uu____4364]  in
                            uu____4351 :: uu____4357  in
                          let uu____4382 =
                            let uu____4389 =
                              let uu____4396 =
                                let uu____4403 =
                                  let uu____4408 =
                                    translate cfg bs
                                      lb.FStar_Syntax_Syntax.lbdef
                                     in
                                  (uu____4408, FStar_Pervasives_Native.None)
                                   in
                                let uu____4409 =
                                  let uu____4416 =
                                    let uu____4423 =
                                      let uu____4428 =
                                        translate cfg bs body_lam  in
                                      (uu____4428,
                                        FStar_Pervasives_Native.None)
                                       in
                                    [uu____4423]  in
                                  (FStar_TypeChecker_NBETerm.Unknown,
                                    FStar_Pervasives_Native.None) ::
                                    uu____4416
                                   in
                                uu____4403 :: uu____4409  in
                              (FStar_TypeChecker_NBETerm.Unknown,
                                FStar_Pervasives_Native.None) :: uu____4396
                               in
                            FStar_List.append maybe_range_arg uu____4389  in
                          FStar_List.append uu____4344 uu____4382  in
                        iapp uu____4324 uu____4343)
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____4457);
                      FStar_Syntax_Syntax.pos = uu____4458;
                      FStar_Syntax_Syntax.vars = uu____4459;_},(e2,uu____4461)::[])
                   ->
                   translate
                     (let uu___244_4492 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___244_4492.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___244_4492.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___244_4492.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___244_4492.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___244_4492.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___244_4492.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___244_4492.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___244_4492.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | uu____4493 ->
                   let uu____4494 =
                     let uu____4495 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____4495
                      in
                   failwith uu____4494)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____4496  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____4496 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____4520 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____4520
              then
                let ed =
                  let uu____4522 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____4522
                   in
                let cfg' =
                  let uu___245_4524 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___245_4524.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___245_4524.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___245_4524.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___245_4524.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___245_4524.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___245_4524.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___245_4524.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___245_4524.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let uu____4525 =
                  let uu____4526 =
                    let uu____4527 =
                      FStar_Syntax_Util.un_uinst
                        (FStar_Pervasives_Native.snd
                           ed.FStar_Syntax_Syntax.return_repr)
                       in
                    translate cfg' [] uu____4527  in
                  iapp uu____4526
                    [((FStar_TypeChecker_NBETerm.Univ
                         FStar_Syntax_Syntax.U_unknown),
                       FStar_Pervasives_Native.None)]
                   in
                let uu____4540 =
                  let uu____4541 =
                    let uu____4546 = translate cfg' bs ty  in
                    (uu____4546, FStar_Pervasives_Native.None)  in
                  let uu____4547 =
                    let uu____4554 =
                      let uu____4559 = translate cfg' bs e1  in
                      (uu____4559, FStar_Pervasives_Native.None)  in
                    [uu____4554]  in
                  uu____4541 :: uu____4547  in
                iapp uu____4525 uu____4540
              else
                (let uu____4573 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____4573 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____4576 =
                       let uu____4577 = FStar_Ident.text_of_lid msrc  in
                       let uu____4578 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____4577 uu____4578
                        in
                     failwith uu____4576
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____4579;
                       FStar_TypeChecker_Env.mtarget = uu____4580;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____4581;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____4603 =
                       let uu____4604 = FStar_Ident.text_of_lid msrc  in
                       let uu____4605 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____4604 uu____4605
                        in
                     failwith uu____4603
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____4606;
                       FStar_TypeChecker_Env.mtarget = uu____4607;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____4608;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____4647 =
                         let uu____4650 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____4650
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____4647
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___246_4660 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___246_4660.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___246_4660.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___246_4660.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___246_4660.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___246_4660.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___246_4660.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___246_4660.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___246_4660.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let uu____4661 = translate cfg' [] lift_lam  in
                     let uu____4662 =
                       let uu____4663 =
                         let uu____4668 = translate cfg bs e1  in
                         (uu____4668, FStar_Pervasives_Native.None)  in
                       [uu____4663]  in
                     iapp uu____4661 uu____4662)

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____4692  ->
           let uu____4693 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____4693);
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
           let uu____4696 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____4696 FStar_Syntax_Util.exp_int
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
           let uu____4734 =
             FStar_List.fold_left
               (fun uu____4775  ->
                  fun tf  ->
                    match uu____4775 with
                    | (args,accus) ->
                        let uu____4825 = tf ()  in
                        (match uu____4825 with
                         | (xt,q) ->
                             let x1 =
                               let uu____4845 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____4845
                                in
                             let uu____4846 =
                               let uu____4849 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____4849 :: accus  in
                             (((x1, q) :: args), uu____4846))) ([], []) targs
              in
           (match uu____4734 with
            | (args,accus) ->
                let body =
                  let uu____4893 = f accus  in readback cfg uu____4893  in
                FStar_Syntax_Util.abs args body FStar_Pervasives_Native.None)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____4932  ->
                  match uu____4932 with
                  | (x1,q) ->
                      let uu____4943 = readback cfg x1  in (uu____4943, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____4962 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____4969::uu____4970 ->
                let uu____4973 =
                  let uu____4976 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____4976
                    (FStar_List.rev us)
                   in
                apply uu____4973
            | [] ->
                let uu____4977 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____4977)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____5018  ->
                  match uu____5018 with
                  | (x1,q) ->
                      let uu____5029 = readback cfg x1  in (uu____5029, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____5048 -> FStar_Syntax_Util.mk_app tm args1  in
           let tm uu____5062 =
             match us with
             | uu____5065::uu____5066 ->
                 let uu____5069 =
                   let uu____5072 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                       FStar_Pervasives_Native.None FStar_Range.dummyRange
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____5072
                     (FStar_List.rev us)
                    in
                 apply uu____5069
             | [] ->
                 let uu____5073 =
                   FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 apply uu____5073
              in
           let uu____5076 = FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
           (match uu____5076 with
            | FStar_Pervasives_Native.Some prim_step when
                prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                let l = FStar_List.length args1  in
                let uu____5085 =
                  if l = prim_step.FStar_TypeChecker_Cfg.arity
                  then (args1, [])
                  else
                    FStar_List.splitAt prim_step.FStar_TypeChecker_Cfg.arity
                      args1
                   in
                (match uu____5085 with
                 | (args_1,args_2) ->
                     let psc =
                       {
                         FStar_TypeChecker_Cfg.psc_range =
                           FStar_Range.dummyRange;
                         FStar_TypeChecker_Cfg.psc_subst =
                           (fun uu____5171  ->
                              if
                                prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                              then
                                failwith
                                  "Cannot handle primops that require substitution"
                              else [])
                       }  in
                     let uu____5173 =
                       prim_step.FStar_TypeChecker_Cfg.interpretation psc
                         args_1
                        in
                     (match uu____5173 with
                      | FStar_Pervasives_Native.Some tm1 ->
                          FStar_Syntax_Util.mk_app tm1 args_2
                      | FStar_Pervasives_Native.None  -> tm ()))
            | uu____5177 -> tm ())
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____5224  ->
                  match uu____5224 with
                  | (x1,q) ->
                      let uu____5235 = readback cfg x1  in (uu____5235, q))
               ts
              in
           let uu____5236 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____5236 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____5296  ->
                  match uu____5296 with
                  | (x1,q) ->
                      let uu____5307 = readback cfg x1  in (uu____5307, q))
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
            | uu____5337 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app cfg hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____5424 = curry hd1 args1  in
                 app cfg uu____5424 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
              in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef  in
           let uu____5426 = test_args ts args_no  in
           if uu____5426
           then
             let uu____5427 =
               let uu____5428 =
                 let uu____5429 = make_rec_env lbs bs  in
                 translate_letbinding cfg uu____5429 lb  in
               curry uu____5428 ts  in
             readback cfg uu____5427
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
                  (fun uu____5474  ->
                     match uu____5474 with
                     | (x1,q) ->
                         let uu____5485 = readback cfg x1  in (uu____5485, q))
                  ts
                 in
              match ts with
              | [] -> head1
              | uu____5490 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Arrow uu____5497 ->
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
    match projectee with | Primops  -> true | uu____5538 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____5545 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5561 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5581 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____5594 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____5600 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___240_5605  ->
    match uu___240_5605 with
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
          let uu___247_5632 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___248_5635 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___248_5635.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___248_5635.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___248_5635.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___248_5635.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___248_5635.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___248_5635.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___248_5635.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___248_5635.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___248_5635.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___248_5635.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___248_5635.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___248_5635.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___248_5635.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___248_5635.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___248_5635.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___248_5635.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___248_5635.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___248_5635.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___248_5635.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___248_5635.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___248_5635.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___248_5635.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___248_5635.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___248_5635.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___247_5632.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___247_5632.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___247_5632.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___247_5632.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___247_5632.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___247_5632.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___247_5632.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___247_5632.FStar_TypeChecker_Cfg.reifying)
          }  in
        let uu____5636 = translate cfg1 [] e  in readback cfg1 uu____5636
  
let (test_normalize :
  step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg =
          let uu____5657 = FStar_List.map step_as_normalizer_step steps  in
          FStar_TypeChecker_Cfg.config uu____5657 env  in
        let cfg1 =
          let uu___249_5661 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___250_5664 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___250_5664.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___250_5664.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___250_5664.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___250_5664.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___250_5664.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___250_5664.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___250_5664.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___250_5664.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___250_5664.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___250_5664.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___250_5664.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___250_5664.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___250_5664.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___250_5664.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___250_5664.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___250_5664.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___250_5664.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___250_5664.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___250_5664.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___250_5664.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___250_5664.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___250_5664.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___250_5664.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___250_5664.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___249_5661.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___249_5661.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___249_5661.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___249_5661.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___249_5661.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___249_5661.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___249_5661.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___249_5661.FStar_TypeChecker_Cfg.reifying)
          }  in
        let uu____5665 = translate cfg1 [] e  in readback cfg1 uu____5665
  