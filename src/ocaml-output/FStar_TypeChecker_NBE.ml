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
  
let fmap_opt :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun x  ->
      FStar_Util.bind_opt x
        (fun x1  ->
           let uu____270 = f x1  in FStar_Pervasives_Native.Some uu____270)
  
let (debug : FStar_TypeChecker_Cfg.cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____286 =
        let uu____287 = FStar_TypeChecker_Cfg.cfg_env cfg  in
        FStar_TypeChecker_Env.debug uu____287 (FStar_Options.Other "NBE")  in
      if uu____286 then f () else ()
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____294 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____294
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____311 = FStar_Syntax_Print.sigelt_to_string_short v1  in
             FStar_Util.print2 "%s -> %%s\n" k uu____311) ()
  
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____416 -> FStar_Util.Inl []
            | FStar_Syntax_Syntax.Pat_constant s ->
                let matches_const c s1 =
                  debug cfg
                    (fun uu____441  ->
                       let uu____442 =
                         FStar_TypeChecker_NBETerm.t_to_string c  in
                       let uu____443 = FStar_Syntax_Print.const_to_string s1
                          in
                       FStar_Util.print2
                         "Testing term %s against pattern %s\n" uu____442
                         uu____443);
                  (match c with
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Unit ) ->
                       s1 = FStar_Const.Const_unit
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Bool b) ->
                       (match s1 with
                        | FStar_Const.Const_bool p1 -> b = p1
                        | uu____446 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Int i) ->
                       (match s1 with
                        | FStar_Const.Const_int
                            (p1,FStar_Pervasives_Native.None ) ->
                            let uu____459 = FStar_BigInt.big_int_of_string p1
                               in
                            i = uu____459
                        | uu____460 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.String (st,uu____462)) ->
                       (match s1 with
                        | FStar_Const.Const_string (p1,uu____464) -> st = p1
                        | uu____465 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Char c1) ->
                       (match s1 with
                        | FStar_Const.Const_char p1 -> c1 = p1
                        | uu____471 -> false)
                   | uu____472 -> false)
                   in
                let uu____473 = matches_const scrutinee s  in
                if uu____473 then FStar_Util.Inl [] else FStar_Util.Inr false
            | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                let rec matches_args out a p1 =
                  match (a, p1) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t,uu____594)::rest_a,(p2,uu____597)::rest_p) ->
                      let uu____631 = matches_pat t p2  in
                      (match uu____631 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____656 -> FStar_Util.Inr false  in
                (match scrutinee with
                 | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev) ->
                     let uu____700 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                     if uu____700
                     then matches_args [] (FStar_List.rev args_rev) arg_pats
                     else FStar_Util.Inr false
                 | uu____714 -> FStar_Util.Inr true)
             in
          match branches1 with
          | [] -> failwith "Branch not found"
          | (p,_wopt,e)::branches2 ->
              let uu____755 = matches_pat scrut1 p  in
              (match uu____755 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____778  ->
                         let uu____779 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____779);
                    FStar_Pervasives_Native.Some (e, matches))
               | FStar_Util.Inr (false ) ->
                   pickBranch_aux scrut1 branches2 branches0
               | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
           in
        pickBranch_aux scrut branches branches
  
let rec test_args :
  'Auu____805 .
    (FStar_TypeChecker_NBETerm.t,'Auu____805) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.int -> Prims.bool
  =
  fun ts  ->
    fun cnt  ->
      match ts with
      | [] -> cnt <= (Prims.parse_int "0")
      | t::ts1 ->
          (let uu____850 =
             FStar_TypeChecker_NBETerm.isAccu (FStar_Pervasives_Native.fst t)
              in
           Prims.op_Negation uu____850) &&
            (test_args ts1 (cnt - (Prims.parse_int "1")))
  
let rec (count_abstractions : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    let uu____856 =
      let uu____857 = FStar_Syntax_Subst.compress t  in
      uu____857.FStar_Syntax_Syntax.n  in
    match uu____856 with
    | FStar_Syntax_Syntax.Tm_delayed uu____860 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____883 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_name uu____884 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_fvar uu____885 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_constant uu____886 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_type uu____887 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_arrow uu____888 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uvar uu____903 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_refine uu____916 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_unknown  -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____924) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____931) ->
        let uu____956 = count_abstractions body  in
        (FStar_List.length xs) + uu____956
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____989 =
          let uu____990 = count_abstractions head1  in
          uu____990 - (FStar_List.length args)  in
        max uu____989 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____1051,uu____1052,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____1101,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1120) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1126,uu____1127) ->
        count_abstractions t1
    | uu____1168 -> (Prims.parse_int "0")
  
let (find_sigelt_in_gamma :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.env ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lid  ->
        let mapper uu____1213 =
          match uu____1213 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1296  ->
                         let uu____1297 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1297);
                    FStar_Pervasives_Native.Some elt)
               | uu____1298 -> FStar_Pervasives_Native.None)
           in
        let uu____1313 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1313 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1357 -> true
    | uu____1358 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | uu____1365 -> failwith "Not a universe"
  
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
              (uu____1378,uu____1379,uu____1380,uu____1381,uu____1382,uu____1383);
            FStar_Syntax_Syntax.sigrng = uu____1384;
            FStar_Syntax_Syntax.sigquals = uu____1385;
            FStar_Syntax_Syntax.sigmeta = uu____1386;
            FStar_Syntax_Syntax.sigattrs = uu____1387;_},uu____1388),uu____1389)
        -> true
    | uu____1444 -> false
  
let (translate_univ :
  FStar_TypeChecker_NBETerm.t Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun bs  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar i ->
            if i < (FStar_List.length bs)
            then let u' = FStar_List.nth bs i  in un_univ u'
            else failwith "Universe index out of bounds"
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1470 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1470
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1474 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1474
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____1477 -> u2
        | FStar_Syntax_Syntax.U_unif uu____1478 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2  in
      aux u
  
let (mkRec :
  FStar_Syntax_Syntax.letbinding ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_TypeChecker_NBETerm.t Prims.list -> FStar_TypeChecker_NBETerm.t)
  =
  fun b  ->
    fun bs  ->
      fun env  ->
        let ar = count_abstractions b.FStar_Syntax_Syntax.lbdef  in
        FStar_TypeChecker_NBETerm.Rec (b, bs, env, [], ar)
  
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
            let uu____1592 =
              let uu____1595 = mkRec lb lbs0 bs0  in uu____1595 :: bs1  in
            aux lbs' lbs0 uu____1592 bs0
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
           | FStar_Util.Inl uu____1617 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1621 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1621
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
  
let tabulate : 'a . Prims.int -> (Prims.int -> 'a) -> 'a Prims.list =
  fun n1  ->
    fun f  ->
      let rec aux i =
        if i < n1
        then
          let uu____1659 = f i  in
          let uu____1660 = aux (i + (Prims.parse_int "1"))  in uu____1659 ::
            uu____1660
        else []  in
      aux (Prims.parse_int "0")
  
let rec (iapp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun f  ->
      fun args  ->
        debug cfg
          (fun uu____1859  ->
             let uu____1860 = FStar_TypeChecker_NBETerm.t_to_string f  in
             let uu____1861 = FStar_TypeChecker_NBETerm.args_to_string args
                in
             FStar_Util.print2 "App : %s @ %s\n" uu____1860 uu____1861);
        (match f with
         | FStar_TypeChecker_NBETerm.Lam (f1,targs,n1) ->
             let m = FStar_List.length args  in
             if m < n1
             then
               let uu____1908 = FStar_List.splitAt m targs  in
               (match uu____1908 with
                | (uu____1948,targs') ->
                    let targs'1 =
                      FStar_List.map
                        (fun targ  ->
                           fun l  ->
                             let uu____2039 =
                               let uu____2042 =
                                 map_append FStar_Pervasives_Native.fst args
                                   l
                                  in
                               FStar_List.rev uu____2042  in
                             targ uu____2039) targs'
                       in
                    FStar_TypeChecker_NBETerm.Lam
                      (((fun l  ->
                           let uu____2070 =
                             map_append FStar_Pervasives_Native.fst args l
                              in
                           f1 uu____2070)), targs'1, (n1 - m)))
             else
               if m = n1
               then
                 (let uu____2086 =
                    FStar_List.map FStar_Pervasives_Native.fst args  in
                  f1 uu____2086)
               else
                 (let uu____2094 = FStar_List.splitAt n1 args  in
                  match uu____2094 with
                  | (args1,args') ->
                      let uu____2141 =
                        let uu____2142 =
                          FStar_List.map FStar_Pervasives_Native.fst args1
                           in
                        f1 uu____2142  in
                      iapp cfg uu____2141 args')
         | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
             FStar_TypeChecker_NBETerm.Accu
               (a, (FStar_List.rev_append args ts))
         | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
             let rec aux args1 us1 ts1 =
               match args1 with
               | (FStar_TypeChecker_NBETerm.Univ u,uu____2261)::args2 ->
                   aux args2 (u :: us1) ts1
               | a::args2 -> aux args2 us1 (a :: ts1)
               | [] -> (us1, ts1)  in
             let uu____2305 = aux args us ts  in
             (match uu____2305 with
              | (us',ts') ->
                  FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
         | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
             let rec aux args1 us1 ts1 =
               match args1 with
               | (FStar_TypeChecker_NBETerm.Univ u,uu____2432)::args2 ->
                   aux args2 (u :: us1) ts1
               | a::args2 -> aux args2 us1 (a :: ts1)
               | [] -> (us1, ts1)  in
             let uu____2476 = aux args us ts  in
             (match uu____2476 with
              | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
         | FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs,acc,arity) ->
             let no_args = FStar_List.length args  in
             let no_acc = FStar_List.length acc  in
             let full_args = FStar_List.append acc args  in
             let uu____2561 = test_args full_args arity  in
             if uu____2561
             then
               (if (FStar_List.length full_args) > arity
                then
                  let uu____2566 = FStar_List.splitAt arity full_args  in
                  match uu____2566 with
                  | (rargs,res) ->
                      let t =
                        let uu____2614 =
                          let uu____2615 = make_rec_env lbs bs  in
                          translate_letbinding cfg uu____2615 lb  in
                        iapp cfg uu____2614 rargs  in
                      iapp cfg t res
                else
                  (let uu____2619 =
                     let uu____2620 = make_rec_env lbs bs  in
                     translate_letbinding cfg uu____2620 lb  in
                   iapp cfg uu____2619 full_args))
             else
               FStar_TypeChecker_NBETerm.Rec (lb, lbs, bs, full_args, arity)
         | FStar_TypeChecker_NBETerm.Quote uu____2634 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Lazy uu____2639 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Constant uu____2640 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Univ uu____2641 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Type_t uu____2642 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Unknown  ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Refinement uu____2643 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Arrow uu____2658 ->
             failwith "Ill-typed application")

and (app :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.t ->
        FStar_Syntax_Syntax.aqual -> FStar_TypeChecker_NBETerm.t)
  = fun cfg  -> fun f  -> fun x  -> fun q  -> iapp cfg f [(x, q)]

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
          let uu____2703 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2704 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2703 uu____2704  in
        let uu____2705 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2705
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2711 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2713  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2711 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2719  ->
                     let uu____2720 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2720);
                (let uu____2721 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____2721 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     let uu____2726 =
                       let uu____2749 =
                         let f uu____2776 uu____2777 =
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
                           let uu____2828 =
                             prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                               args'
                              in
                           match uu____2828 with
                           | FStar_Pervasives_Native.Some x ->
                               (debug1
                                  (fun uu____2839  ->
                                     let uu____2840 =
                                       FStar_Syntax_Print.fv_to_string fvar1
                                        in
                                     let uu____2841 =
                                       FStar_TypeChecker_NBETerm.t_to_string
                                         x
                                        in
                                     FStar_Util.print2
                                       "Primitive operator %s returned %s\n"
                                       uu____2840 uu____2841);
                                x)
                           | FStar_Pervasives_Native.None  ->
                               (debug1
                                  (fun uu____2847  ->
                                     let uu____2848 =
                                       FStar_Syntax_Print.fv_to_string fvar1
                                        in
                                     FStar_Util.print1
                                       "Primitive operator %s failed\n"
                                       uu____2848);
                                (let uu____2849 =
                                   FStar_TypeChecker_NBETerm.mkFV fvar1 [] []
                                    in
                                 iapp cfg uu____2849 args'))), uu____2749,
                         arity)
                        in
                     FStar_TypeChecker_NBETerm.Lam uu____2726
                 | uu____2854 ->
                     (debug1
                        (fun uu____2862  ->
                           let uu____2863 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____2863);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2871;
                        FStar_Syntax_Syntax.sigquals = uu____2872;
                        FStar_Syntax_Syntax.sigmeta = uu____2873;
                        FStar_Syntax_Syntax.sigattrs = uu____2874;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec lb [] []
                         else
                           (debug1
                              (fun uu____2943  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2951  ->
                                 let uu____2952 =
                                   let uu____2953 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2953
                                    in
                                 let uu____2954 =
                                   let uu____2955 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2955
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2952 uu____2954);
                            debug1
                              (fun uu____2963  ->
                                 let uu____2964 =
                                   let uu____2965 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2965
                                    in
                                 let uu____2966 =
                                   let uu____2967 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2967
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2964 uu____2966);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____2968 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2976;
                        FStar_Syntax_Syntax.sigquals = uu____2977;
                        FStar_Syntax_Syntax.sigmeta = uu____2978;
                        FStar_Syntax_Syntax.sigattrs = uu____2979;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec lb [] []
                         else
                           (debug1
                              (fun uu____3048  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____3056  ->
                                 let uu____3057 =
                                   let uu____3058 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3058
                                    in
                                 let uu____3059 =
                                   let uu____3060 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3060
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____3057 uu____3059);
                            debug1
                              (fun uu____3068  ->
                                 let uu____3069 =
                                   let uu____3070 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3070
                                    in
                                 let uu____3071 =
                                   let uu____3072 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3072
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____3069 uu____3071);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____3073 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        | uu____3118 ->
            let uu____3121 =
              let uu____3144 =
                FStar_List.map
                  (fun uu____3169  ->
                     fun _ts  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____3144,
                (FStar_List.length us))
               in
            FStar_TypeChecker_NBETerm.Lam uu____3121

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____3220 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____3220
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____3226 ->
        let uu____3227 =
          let uu____3228 =
            let uu____3229 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____3229 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____3228  in
        failwith uu____3227

and (translate_pat :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.pat -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun p  ->
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          let uu____3233 = translate_constant c  in
          FStar_TypeChecker_NBETerm.Constant uu____3233
      | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
          let uu____3252 = FStar_TypeChecker_NBETerm.mkConstruct cfv [] []
             in
          let uu____3257 =
            FStar_List.map
              (fun uu____3272  ->
                 match uu____3272 with
                 | (p1,uu____3284) ->
                     let uu____3285 = translate_pat cfg p1  in
                     (uu____3285, FStar_Pervasives_Native.None)) pats
             in
          iapp cfg uu____3252 uu____3257
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
          (fun uu____3316  ->
             let uu____3317 =
               let uu____3318 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____3318  in
             let uu____3319 =
               let uu____3320 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____3320  in
             FStar_Util.print2 "Term: %s - %s\n" uu____3317 uu____3319);
        debug1
          (fun uu____3326  ->
             let uu____3327 =
               let uu____3328 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____3328  in
             FStar_Util.print1 "BS list: %s\n" uu____3327);
        (let uu____3333 =
           let uu____3334 = FStar_Syntax_Subst.compress e  in
           uu____3334.FStar_Syntax_Syntax.n  in
         match uu____3333 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____3337,uu____3338) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3376 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3376
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then FStar_List.nth bs db.FStar_Syntax_Syntax.index
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3392  ->
                   let uu____3393 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3394 =
                     let uu____3395 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3395
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____3393 uu____3394);
              (let uu____3400 = translate cfg bs t  in
               let uu____3401 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3405 =
                        let uu____3406 = translate_univ bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____3406  in
                      FStar_TypeChecker_NBETerm.as_arg uu____3405) us
                  in
               iapp cfg uu____3400 uu____3401))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3408 = translate_univ bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____3408
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____3431 =
               let uu____3450 =
                 FStar_List.map
                   (fun x  ->
                      fun uu____3485  ->
                        let uu____3486 =
                          translate cfg bs
                            (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                           in
                        (uu____3486, (FStar_Pervasives_Native.snd x))) xs
                  in
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____3450)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____3431
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____3531  ->
                     let uu____3532 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____3532)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3534,uu____3535) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____3596,uu____3597) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____3622) ->
             let uu____3647 =
               let uu____3670 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____3740 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____3740, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____3670, (FStar_List.length xs))
                in
             FStar_TypeChecker_NBETerm.Lam uu____3647
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3796;
                FStar_Syntax_Syntax.vars = uu____3797;_},arg::more::args)
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let uu____3857 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3857 with
              | (reifyh,uu____3875) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app reifyh [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3919 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3919)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3928;
                FStar_Syntax_Syntax.vars = uu____3929;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___245_3971 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___245_3971.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___245_3971.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___245_3971.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___245_3971.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___245_3971.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___245_3971.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___245_3971.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___245_3971.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____4009  ->
                   let uu____4010 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____4011 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____4010
                     uu____4011);
              (let uu____4012 = translate cfg bs head1  in
               let uu____4013 =
                 FStar_List.map
                   (fun x  ->
                      let uu____4035 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____4035, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____4012 uu____4013))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____4120  ->
                         let uu____4121 =
                           let uu____4122 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____4145  ->
                                     match uu____4145 with
                                     | (x,q) ->
                                         let uu____4158 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____4158))
                              in
                           FStar_All.pipe_right uu____4122
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____4121);
                    (let uu____4162 = pickBranch cfg scrut1 branches  in
                     match uu____4162 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____4183 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____4183 branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   let uu____4201 = pickBranch cfg scrut1 branches  in
                   (match uu____4201 with
                    | FStar_Pervasives_Native.Some (branch1,[]) ->
                        translate cfg bs branch1
                    | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                        translate cfg (arg :: bs) branch1
                    | FStar_Pervasives_Native.None  ->
                        FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                          make_branches
                    | FStar_Pervasives_Native.Some (uu____4235,hd1::tl1) ->
                        failwith
                          "Impossible: Matching on constants cannot bind more than one variable")
               | uu____4248 ->
                   FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                     make_branches
             
             and make_branches readback1 =
               let rec process_pattern bs1 p =
                 let uu____4281 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____4315 =
                         FStar_List.fold_left
                           (fun uu____4353  ->
                              fun uu____4354  ->
                                match (uu____4353, uu____4354) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____4435 = process_pattern bs2 arg
                                       in
                                    (match uu____4435 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____4315 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____4524 =
                           let uu____4525 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4525  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4524
                          in
                       let uu____4526 =
                         let uu____4529 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4529 :: bs1  in
                       (uu____4526, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____4534 =
                           let uu____4535 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4535  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4534
                          in
                       let uu____4536 =
                         let uu____4539 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4539 :: bs1  in
                       (uu____4536, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____4549 =
                           let uu____4550 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4550  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4549
                          in
                       let uu____4551 =
                         let uu____4552 =
                           let uu____4559 =
                             let uu____4562 = translate cfg bs1 tm  in
                             readback1 uu____4562  in
                           (x, uu____4559)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____4552  in
                       (bs1, uu____4551)
                    in
                 match uu____4281 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___246_4582 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___246_4582.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____4601  ->
                    match uu____4601 with
                    | (pat,when_clause,e1) ->
                        let uu____4623 = process_pattern bs pat  in
                        (match uu____4623 with
                         | (bs',pat') ->
                             let uu____4636 =
                               let uu____4637 =
                                 let uu____4640 = translate cfg bs' e1  in
                                 readback1 uu____4640  in
                               (pat', when_clause, uu____4637)  in
                             FStar_Syntax_Util.branch uu____4636)) branches
              in let uu____4649 = translate cfg bs scrut  in case uu____4649
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
             let uu____4722 = make_rec_env lbs bs  in
             translate cfg uu____4722 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4726) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             FStar_TypeChecker_NBETerm.Quote (qt, qi)
         | FStar_Syntax_Syntax.Tm_lazy li ->
             FStar_TypeChecker_NBETerm.Lazy li)

and (translate_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_NBETerm.comp)
  =
  fun cfg  ->
    fun bs  ->
      fun c  ->
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (typ,u) ->
            let uu____4753 =
              let uu____4760 = translate cfg bs typ  in
              let uu____4761 = fmap_opt (translate_univ bs) u  in
              (uu____4760, uu____4761)  in
            FStar_TypeChecker_NBETerm.Tot uu____4753
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4776 =
              let uu____4783 = translate cfg bs typ  in
              let uu____4784 = fmap_opt (translate_univ bs) u  in
              (uu____4783, uu____4784)  in
            FStar_TypeChecker_NBETerm.GTot uu____4776
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4790 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4790

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____4800 =
              let uu____4809 = readback cfg typ  in (uu____4809, u)  in
            FStar_Syntax_Syntax.Total uu____4800
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____4822 =
              let uu____4831 = readback cfg typ  in (uu____4831, u)  in
            FStar_Syntax_Syntax.GTotal uu____4822
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____4839 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____4839
         in
      FStar_Syntax_Syntax.mk c' FStar_Pervasives_Native.None
        FStar_Range.dummyRange

and (translate_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.comp_typ -> FStar_TypeChecker_NBETerm.comp_typ)
  =
  fun cfg  ->
    fun bs  ->
      fun c  ->
        let uu____4845 = c  in
        match uu____4845 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags1;_} ->
            let uu____4865 = FStar_List.map (translate_univ bs) comp_univs
               in
            let uu____4866 = translate cfg bs result_typ  in
            let uu____4867 =
              FStar_List.map
                (fun x  ->
                   let uu____4895 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____4895, (FStar_Pervasives_Native.snd x))) effect_args
               in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____4865;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____4866;
              FStar_TypeChecker_NBETerm.effect_args = uu____4867;
              FStar_TypeChecker_NBETerm.flags = flags1
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____4904 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____4907 =
        FStar_List.map
          (fun x  ->
             let uu____4933 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____4933, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____4904;
        FStar_Syntax_Syntax.effect_args = uu____4907;
        FStar_Syntax_Syntax.flags = (c.FStar_TypeChecker_NBETerm.flags)
      }

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____4934  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____4934 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____4969 =
                     let uu____4978 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____4978
                      in
                   (match uu____4969 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____4985 =
                          let uu____4986 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____4986
                           in
                        failwith uu____4985
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___247_5000 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___247_5000.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___247_5000.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___247_5000.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___247_5000.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___247_5000.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___247_5000.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___247_5000.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___247_5000.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____5007 =
                            let uu____5014 =
                              let uu____5015 =
                                let uu____5034 =
                                  let uu____5043 =
                                    let uu____5050 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____5050,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____5043]  in
                                (uu____5034, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____5015  in
                            FStar_Syntax_Syntax.mk uu____5014  in
                          uu____5007 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____5087 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____5087
                          then
                            let uu____5094 =
                              let uu____5099 =
                                let uu____5100 =
                                  FStar_Syntax_Embeddings.embed
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____5100  in
                              (uu____5099, FStar_Pervasives_Native.None)  in
                            let uu____5101 =
                              let uu____5108 =
                                let uu____5113 =
                                  let uu____5114 =
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____5114  in
                                (uu____5113, FStar_Pervasives_Native.None)
                                 in
                              [uu____5108]  in
                            uu____5094 :: uu____5101
                          else []  in
                        let uu____5132 =
                          let uu____5133 =
                            let uu____5134 =
                              FStar_Syntax_Util.un_uinst
                                (FStar_Pervasives_Native.snd
                                   ed.FStar_Syntax_Syntax.bind_repr)
                               in
                            translate cfg' [] uu____5134  in
                          iapp cfg uu____5133
                            [((FStar_TypeChecker_NBETerm.Univ
                                 FStar_Syntax_Syntax.U_unknown),
                               FStar_Pervasives_Native.None);
                            ((FStar_TypeChecker_NBETerm.Univ
                                FStar_Syntax_Syntax.U_unknown),
                              FStar_Pervasives_Native.None)]
                           in
                        let uu____5151 =
                          let uu____5152 =
                            let uu____5159 =
                              let uu____5164 =
                                translate cfg' bs
                                  lb.FStar_Syntax_Syntax.lbtyp
                                 in
                              (uu____5164, FStar_Pervasives_Native.None)  in
                            let uu____5165 =
                              let uu____5172 =
                                let uu____5177 = translate cfg' bs ty  in
                                (uu____5177, FStar_Pervasives_Native.None)
                                 in
                              [uu____5172]  in
                            uu____5159 :: uu____5165  in
                          let uu____5190 =
                            let uu____5197 =
                              let uu____5204 =
                                let uu____5211 =
                                  let uu____5216 =
                                    translate cfg bs
                                      lb.FStar_Syntax_Syntax.lbdef
                                     in
                                  (uu____5216, FStar_Pervasives_Native.None)
                                   in
                                let uu____5217 =
                                  let uu____5224 =
                                    let uu____5231 =
                                      let uu____5236 =
                                        translate cfg bs body_lam  in
                                      (uu____5236,
                                        FStar_Pervasives_Native.None)
                                       in
                                    [uu____5231]  in
                                  (FStar_TypeChecker_NBETerm.Unknown,
                                    FStar_Pervasives_Native.None) ::
                                    uu____5224
                                   in
                                uu____5211 :: uu____5217  in
                              (FStar_TypeChecker_NBETerm.Unknown,
                                FStar_Pervasives_Native.None) :: uu____5204
                               in
                            FStar_List.append maybe_range_arg uu____5197  in
                          FStar_List.append uu____5152 uu____5190  in
                        iapp cfg uu____5132 uu____5151)
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____5265);
                      FStar_Syntax_Syntax.pos = uu____5266;
                      FStar_Syntax_Syntax.vars = uu____5267;_},(e2,uu____5269)::[])
                   ->
                   translate
                     (let uu___248_5310 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___248_5310.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___248_5310.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___248_5310.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___248_5310.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___248_5310.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___248_5310.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___248_5310.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___248_5310.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app uu____5311 -> translate cfg bs e1
               | uu____5328 ->
                   let uu____5329 =
                     let uu____5330 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____5330
                      in
                   failwith uu____5329)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____5331  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____5331 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____5355 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____5355
              then
                let ed =
                  let uu____5357 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____5357
                   in
                let cfg' =
                  let uu___249_5359 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___249_5359.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___249_5359.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___249_5359.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___249_5359.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___249_5359.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___249_5359.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___249_5359.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___249_5359.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let uu____5360 =
                  let uu____5361 =
                    let uu____5362 =
                      FStar_Syntax_Util.un_uinst
                        (FStar_Pervasives_Native.snd
                           ed.FStar_Syntax_Syntax.return_repr)
                       in
                    translate cfg' [] uu____5362  in
                  iapp cfg uu____5361
                    [((FStar_TypeChecker_NBETerm.Univ
                         FStar_Syntax_Syntax.U_unknown),
                       FStar_Pervasives_Native.None)]
                   in
                let uu____5375 =
                  let uu____5376 =
                    let uu____5381 = translate cfg' bs ty  in
                    (uu____5381, FStar_Pervasives_Native.None)  in
                  let uu____5382 =
                    let uu____5389 =
                      let uu____5394 = translate cfg' bs e1  in
                      (uu____5394, FStar_Pervasives_Native.None)  in
                    [uu____5389]  in
                  uu____5376 :: uu____5382  in
                iapp cfg uu____5360 uu____5375
              else
                (let uu____5408 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____5408 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____5411 =
                       let uu____5412 = FStar_Ident.text_of_lid msrc  in
                       let uu____5413 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____5412 uu____5413
                        in
                     failwith uu____5411
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____5414;
                       FStar_TypeChecker_Env.mtarget = uu____5415;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____5416;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____5438 =
                       let uu____5439 = FStar_Ident.text_of_lid msrc  in
                       let uu____5440 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____5439 uu____5440
                        in
                     failwith uu____5438
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____5441;
                       FStar_TypeChecker_Env.mtarget = uu____5442;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____5443;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____5482 =
                         let uu____5485 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____5485
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____5482
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___250_5501 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___250_5501.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___250_5501.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___250_5501.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___250_5501.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___250_5501.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___250_5501.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___250_5501.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___250_5501.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let uu____5502 = translate cfg' [] lift_lam  in
                     let uu____5503 =
                       let uu____5504 =
                         let uu____5509 = translate cfg bs e1  in
                         (uu____5509, FStar_Pervasives_Native.None)  in
                       [uu____5504]  in
                     iapp cfg uu____5502 uu____5503)

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____5533  ->
           let uu____5534 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____5534);
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
           let uu____5537 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____5537 FStar_Syntax_Util.exp_int
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
           let uu____5579 =
             FStar_List.fold_left
               (fun uu____5622  ->
                  fun tf  ->
                    match uu____5622 with
                    | (args_rev,accus_rev) ->
                        let uu____5674 = tf accus_rev  in
                        (match uu____5674 with
                         | (xt,q) ->
                             let x1 =
                               let uu____5694 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____5694
                                in
                             let uu____5695 =
                               let uu____5698 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____5698 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____5695))) ([], [])
               targs
              in
           (match uu____5579 with
            | (args_rev,accus_rev) ->
                let body =
                  let uu____5742 = f (FStar_List.rev accus_rev)  in
                  readback cfg uu____5742  in
                FStar_Syntax_Util.abs (FStar_List.rev args_rev) body
                  FStar_Pervasives_Native.None)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____5770 =
               let uu____5771 =
                 let uu____5772 = targ ()  in
                 FStar_Pervasives_Native.fst uu____5772  in
               readback cfg uu____5771  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____5770
              in
           let body =
             let uu____5778 =
               let uu____5779 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____5779  in
             readback cfg uu____5778  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____5810 =
             FStar_List.fold_left
               (fun uu____5851  ->
                  fun tf  ->
                    match uu____5851 with
                    | (args,accus) ->
                        let uu____5901 = tf ()  in
                        (match uu____5901 with
                         | (xt,q) ->
                             let x1 =
                               let uu____5921 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____5921
                                in
                             let uu____5922 =
                               let uu____5925 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____5925 :: accus  in
                             (((x1, q) :: args), uu____5922))) ([], []) targs
              in
           (match uu____5810 with
            | (args,accus) ->
                let cmp =
                  let uu____5969 = f accus  in readback_comp cfg uu____5969
                   in
                FStar_Syntax_Util.arrow args cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____6008  ->
                  match uu____6008 with
                  | (x1,q) ->
                      let uu____6019 = readback cfg x1  in (uu____6019, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____6038 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____6045::uu____6046 ->
                let uu____6049 =
                  let uu____6052 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____6052
                    (FStar_List.rev us)
                   in
                apply uu____6049
            | [] ->
                let uu____6053 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____6053)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____6094  ->
                  match uu____6094 with
                  | (x1,q) ->
                      let uu____6105 = readback cfg x1  in (uu____6105, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____6124 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____6131::uu____6132 ->
                let uu____6135 =
                  let uu____6138 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____6138
                    (FStar_List.rev us)
                   in
                apply uu____6135
            | [] ->
                let uu____6139 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____6139)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____6186  ->
                  match uu____6186 with
                  | (x1,q) ->
                      let uu____6197 = readback cfg x1  in (uu____6197, q))
               ts
              in
           let uu____6198 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____6198 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____6258  ->
                  match uu____6258 with
                  | (x1,q) ->
                      let uu____6269 = readback cfg x1  in (uu____6269, q))
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
            | uu____6299 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs,args,arity) ->
           let head1 =
             match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inl bv ->
                 let uu____6337 =
                   let uu____6344 =
                     let uu____6345 =
                       let uu____6358 = FStar_Syntax_Syntax.bv_to_name bv  in
                       ((true, lbs), uu____6358)  in
                     FStar_Syntax_Syntax.Tm_let uu____6345  in
                   FStar_Syntax_Syntax.mk uu____6344  in
                 uu____6337 FStar_Pervasives_Native.None
                   FStar_Range.dummyRange
             | FStar_Util.Inr fv ->
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                   FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 =
             map_rev
               (fun uu____6394  ->
                  match uu____6394 with
                  | (x1,q) ->
                      let uu____6405 = readback cfg x1  in (uu____6405, q))
               args
              in
           (match args1 with
            | [] -> head1
            | uu____6410 -> FStar_Syntax_Util.mk_app head1 args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy li ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____6444 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____6451 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____6467 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____6487 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____6500 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____6506 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___244_6511  ->
    match uu___244_6511 with
    | Primops  -> FStar_TypeChecker_Env.Primops
    | UnfoldUntil d -> FStar_TypeChecker_Env.UnfoldUntil d
    | UnfoldOnly lids -> FStar_TypeChecker_Env.UnfoldOnly lids
    | UnfoldAttr attr -> FStar_TypeChecker_Env.UnfoldAttr attr
    | UnfoldTac  -> FStar_TypeChecker_Env.UnfoldTac
    | Reify  -> FStar_TypeChecker_Env.Reify
  
let (normalize :
  FStar_TypeChecker_Cfg.primitive_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun psteps  ->
    fun steps  ->
      fun env  ->
        fun e  ->
          let cfg = FStar_TypeChecker_Cfg.config' psteps steps env  in
          let cfg1 =
            let uu___251_6547 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___252_6550 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___252_6550.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___252_6550.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___252_6550.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___252_6550.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___252_6550.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___252_6550.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___252_6550.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___252_6550.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___252_6550.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___252_6550.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___252_6550.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___252_6550.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___252_6550.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___252_6550.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___252_6550.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___252_6550.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___252_6550.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___252_6550.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___252_6550.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___252_6550.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___252_6550.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___252_6550.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___252_6550.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___252_6550.FStar_TypeChecker_Cfg.nbe_step)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___251_6547.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___251_6547.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___251_6547.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___251_6547.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___251_6547.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___251_6547.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___251_6547.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___251_6547.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____6554  ->
               let uu____6555 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with %s" uu____6555);
          (let uu____6556 = translate cfg1 [] e  in readback cfg1 uu____6556)
  
let (normalize_for_unit_test :
  FStar_TypeChecker_Env.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg = FStar_TypeChecker_Cfg.config steps env  in
        let cfg1 =
          let uu___253_6578 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___254_6581 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___254_6581.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___254_6581.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___254_6581.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___254_6581.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___254_6581.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___254_6581.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___254_6581.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___254_6581.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___254_6581.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___254_6581.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___254_6581.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___254_6581.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___254_6581.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___254_6581.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___254_6581.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___254_6581.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___254_6581.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___254_6581.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___254_6581.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___254_6581.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___254_6581.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___254_6581.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___254_6581.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___254_6581.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___253_6578.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___253_6578.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___253_6578.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___253_6578.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___253_6578.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___253_6578.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___253_6578.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___253_6578.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____6585  ->
             let uu____6586 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____6586);
        (let uu____6587 = translate cfg1 [] e  in readback cfg1 uu____6587)
  