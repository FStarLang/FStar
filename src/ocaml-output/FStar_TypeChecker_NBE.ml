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
            let u' = FStar_List.nth bs i  in un_univ u'
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1469 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1469
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1473 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1473
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____1476 -> u2
        | FStar_Syntax_Syntax.U_unif uu____1477 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2  in
      aux u
  
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
            let uu____1553 =
              let uu____1556 =
                FStar_TypeChecker_NBETerm.mkAccuRec lb lbs0 bs0  in
              uu____1556 :: bs1  in
            aux lbs' lbs0 uu____1553 bs0
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
           | FStar_Util.Inl uu____1578 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1582 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1582
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
          (fun uu____1605  ->
             let uu____1606 = FStar_TypeChecker_NBETerm.t_to_string f  in
             let uu____1607 = FStar_TypeChecker_NBETerm.args_to_string args
                in
             FStar_Util.print2 "App : %s @ (%s)\n" uu____1606 uu____1607);
        (match f with
         | FStar_TypeChecker_NBETerm.Lam (f1,targs,n1) ->
             let m = FStar_List.length args  in
             if m < n1
             then
               let uu____1650 = FStar_List.splitAt m targs  in
               (match uu____1650 with
                | (uu____1684,targs') ->
                    FStar_TypeChecker_NBETerm.Lam
                      (((fun l  ->
                           let uu____1741 =
                             map_append FStar_Pervasives_Native.fst args l
                              in
                           f1 uu____1741)), targs', (n1 - m)))
             else
               if m = n1
               then
                 (let uu____1757 =
                    FStar_List.map FStar_Pervasives_Native.fst args  in
                  f1 uu____1757)
               else
                 (let uu____1765 = FStar_List.splitAt n1 args  in
                  match uu____1765 with
                  | (args1,args') ->
                      let uu____1812 =
                        let uu____1813 =
                          FStar_List.map FStar_Pervasives_Native.fst args1
                           in
                        f1 uu____1813  in
                      iapp cfg uu____1812 args')
         | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
             FStar_TypeChecker_NBETerm.Accu
               (a, (FStar_List.rev_append args ts))
         | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
             let rec aux args1 us1 ts1 =
               match args1 with
               | (FStar_TypeChecker_NBETerm.Univ u,uu____1932)::args2 ->
                   aux args2 (u :: us1) ts1
               | a::args2 -> aux args2 us1 (a :: ts1)
               | [] -> (us1, ts1)  in
             let uu____1976 = aux args us ts  in
             (match uu____1976 with
              | (us',ts') ->
                  FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
         | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
             let rec aux args1 us1 ts1 =
               match args1 with
               | (FStar_TypeChecker_NBETerm.Univ u,uu____2103)::args2 ->
                   aux args2 (u :: us1) ts1
               | a::args2 -> aux args2 us1 (a :: ts1)
               | [] -> (us1, ts1)  in
             let uu____2147 = aux args us ts  in
             (match uu____2147 with
              | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
         | FStar_TypeChecker_NBETerm.Quote uu____2186 ->
             let uu____2191 =
               let uu____2192 = FStar_TypeChecker_NBETerm.t_to_string f  in
               Prims.strcat "NBE ill-typed application: " uu____2192  in
             failwith uu____2191
         | FStar_TypeChecker_NBETerm.Lazy uu____2193 ->
             let uu____2194 =
               let uu____2195 = FStar_TypeChecker_NBETerm.t_to_string f  in
               Prims.strcat "NBE ill-typed application: " uu____2195  in
             failwith uu____2194
         | FStar_TypeChecker_NBETerm.Constant uu____2196 ->
             let uu____2197 =
               let uu____2198 = FStar_TypeChecker_NBETerm.t_to_string f  in
               Prims.strcat "NBE ill-typed application: " uu____2198  in
             failwith uu____2197
         | FStar_TypeChecker_NBETerm.Univ uu____2199 ->
             let uu____2200 =
               let uu____2201 = FStar_TypeChecker_NBETerm.t_to_string f  in
               Prims.strcat "NBE ill-typed application: " uu____2201  in
             failwith uu____2200
         | FStar_TypeChecker_NBETerm.Type_t uu____2202 ->
             let uu____2203 =
               let uu____2204 = FStar_TypeChecker_NBETerm.t_to_string f  in
               Prims.strcat "NBE ill-typed application: " uu____2204  in
             failwith uu____2203
         | FStar_TypeChecker_NBETerm.Unknown  ->
             let uu____2205 =
               let uu____2206 = FStar_TypeChecker_NBETerm.t_to_string f  in
               Prims.strcat "NBE ill-typed application: " uu____2206  in
             failwith uu____2205
         | FStar_TypeChecker_NBETerm.Refinement uu____2207 ->
             let uu____2222 =
               let uu____2223 = FStar_TypeChecker_NBETerm.t_to_string f  in
               Prims.strcat "NBE ill-typed application: " uu____2223  in
             failwith uu____2222
         | FStar_TypeChecker_NBETerm.Arrow uu____2224 ->
             let uu____2243 =
               let uu____2244 = FStar_TypeChecker_NBETerm.t_to_string f  in
               Prims.strcat "NBE ill-typed application: " uu____2244  in
             failwith uu____2243)
  
let (app :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.t ->
        FStar_Syntax_Syntax.aqual -> FStar_TypeChecker_NBETerm.t)
  = fun cfg  -> fun f  -> fun x  -> fun q  -> iapp cfg f [(x, q)] 
let tabulate : 'a . Prims.int -> (Prims.int -> 'a) -> 'a Prims.list =
  fun n1  ->
    fun f  ->
      let rec aux i =
        if i < n1
        then
          let uu____2307 = f i  in
          let uu____2308 = aux (i + (Prims.parse_int "1"))  in uu____2307 ::
            uu____2308
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
          let uu____2486 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2487 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2486 uu____2487  in
        let uu____2488 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2488
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2494 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2496  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2494 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2502  ->
                     let uu____2503 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2503);
                (let uu____2504 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____2504 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____2514  ->
                           let uu____2515 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n" uu____2515);
                      (let uu____2516 =
                         let uu____2537 =
                           let f uu____2560 uu____2561 =
                             ((FStar_TypeChecker_NBETerm.Constant
                                 FStar_TypeChecker_NBETerm.Unit),
                               FStar_Pervasives_Native.None)
                              in
                           tabulate arity f  in
                         ((fun args  ->
                             let args' =
                               FStar_List.map
                                 FStar_TypeChecker_NBETerm.as_arg args
                                in
                             let uu____2606 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 args'
                                in
                             match uu____2606 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____2617  ->
                                       let uu____2618 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____2619 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____2618 uu____2619);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____2625  ->
                                       let uu____2626 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____2626);
                                  (let uu____2627 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp cfg uu____2627 args'))), uu____2537,
                           arity)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____2516))
                 | FStar_Pervasives_Native.Some uu____2632 ->
                     (debug1
                        (fun uu____2638  ->
                           let uu____2639 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____2639);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____2644 ->
                     (debug1
                        (fun uu____2652  ->
                           let uu____2653 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____2653);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2661;
                        FStar_Syntax_Syntax.sigquals = uu____2662;
                        FStar_Syntax_Syntax.sigmeta = uu____2663;
                        FStar_Syntax_Syntax.sigattrs = uu____2664;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2733  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2741  ->
                                 let uu____2742 =
                                   let uu____2743 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2743
                                    in
                                 let uu____2744 =
                                   let uu____2745 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2745
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2742 uu____2744);
                            debug1
                              (fun uu____2753  ->
                                 let uu____2754 =
                                   let uu____2755 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2755
                                    in
                                 let uu____2756 =
                                   let uu____2757 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2757
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2754 uu____2756);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____2758 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2766;
                        FStar_Syntax_Syntax.sigquals = uu____2767;
                        FStar_Syntax_Syntax.sigmeta = uu____2768;
                        FStar_Syntax_Syntax.sigattrs = uu____2769;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2838  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2846  ->
                                 let uu____2847 =
                                   let uu____2848 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2848
                                    in
                                 let uu____2849 =
                                   let uu____2850 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2850
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2847 uu____2849);
                            debug1
                              (fun uu____2858  ->
                                 let uu____2859 =
                                   let uu____2860 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2860
                                    in
                                 let uu____2861 =
                                   let uu____2862 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2862
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2859 uu____2861);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____2863 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        | uu____2908 ->
            let uu____2911 =
              let uu____2932 =
                FStar_List.map
                  (fun uu____2953  ->
                     fun uu____2954  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____2932,
                (FStar_List.length us))
               in
            FStar_TypeChecker_NBETerm.Lam uu____2911

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____3000 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____3000
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____3006 ->
        let uu____3007 =
          let uu____3008 =
            let uu____3009 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____3009 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____3008  in
        failwith uu____3007

and (translate_pat :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.pat -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun p  ->
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          let uu____3013 = translate_constant c  in
          FStar_TypeChecker_NBETerm.Constant uu____3013
      | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
          let uu____3032 = FStar_TypeChecker_NBETerm.mkConstruct cfv [] []
             in
          let uu____3037 =
            FStar_List.map
              (fun uu____3052  ->
                 match uu____3052 with
                 | (p1,uu____3064) ->
                     let uu____3065 = translate_pat cfg p1  in
                     (uu____3065, FStar_Pervasives_Native.None)) pats
             in
          iapp cfg uu____3032 uu____3037
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
          (fun uu____3096  ->
             let uu____3097 =
               let uu____3098 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____3098  in
             let uu____3099 =
               let uu____3100 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____3100  in
             FStar_Util.print2 "Term: %s - %s\n" uu____3097 uu____3099);
        debug1
          (fun uu____3106  ->
             let uu____3107 =
               let uu____3108 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____3108  in
             FStar_Util.print1 "BS list: %s\n" uu____3107);
        (let uu____3113 =
           let uu____3114 = FStar_Syntax_Subst.compress e  in
           uu____3114.FStar_Syntax_Syntax.n  in
         match uu____3113 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____3117,uu____3118) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3156 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3156
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3171  ->
                   let uu____3172 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3173 =
                     let uu____3174 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3174
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____3172 uu____3173);
              (let uu____3179 = translate cfg bs t  in
               let uu____3180 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3184 =
                        let uu____3185 = translate_univ bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____3185  in
                      FStar_TypeChecker_NBETerm.as_arg uu____3184) us
                  in
               iapp cfg uu____3179 uu____3180))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3187 = translate_univ bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____3187
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____3210 =
               let uu____3229 =
                 FStar_List.map
                   (fun x  ->
                      fun uu____3264  ->
                        let uu____3265 =
                          translate cfg bs
                            (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                           in
                        (uu____3265, (FStar_Pervasives_Native.snd x))) xs
                  in
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____3229)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____3210
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____3310  ->
                     let uu____3311 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____3311)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3313,uu____3314) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____3375,uu____3376) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____3401) ->
             let uu____3426 =
               let uu____3447 =
                 FStar_List.map
                   (fun x  ->
                      fun uu____3482  ->
                        let uu____3483 =
                          translate cfg bs
                            (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                           in
                        (uu____3483, (FStar_Pervasives_Native.snd x))) xs
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____3447, (FStar_List.length xs))
                in
             FStar_TypeChecker_NBETerm.Lam uu____3426
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3515;
                FStar_Syntax_Syntax.vars = uu____3516;_},arg::more::args)
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let uu____3576 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3576 with
              | (reifyh,uu____3594) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app reifyh [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3638 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3638)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3647;
                FStar_Syntax_Syntax.vars = uu____3648;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___245_3690 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___245_3690.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___245_3690.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___245_3690.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___245_3690.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___245_3690.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___245_3690.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___245_3690.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___245_3690.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____3728  ->
                   let uu____3729 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3730 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ (%s)\n" uu____3729
                     uu____3730);
              (let uu____3731 = translate cfg bs head1  in
               let uu____3732 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3754 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3754, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3731 uu____3732))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               debug1
                 (fun uu____3820  ->
                    let uu____3821 =
                      let uu____3822 = readback cfg scrut1  in
                      FStar_Syntax_Print.term_to_string uu____3822  in
                    FStar_Util.print1 "Match case: (%s)\n" uu____3821);
               (match scrut1 with
                | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                    (debug1
                       (fun uu____3847  ->
                          let uu____3848 =
                            let uu____3849 =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3872  ->
                                      match uu____3872 with
                                      | (x,q) ->
                                          let uu____3885 =
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              x
                                             in
                                          Prims.strcat
                                            (if FStar_Util.is_some q
                                             then "#"
                                             else "") uu____3885))
                               in
                            FStar_All.pipe_right uu____3849
                              (FStar_String.concat "; ")
                             in
                          FStar_Util.print1 "Match args: %s\n" uu____3848);
                     (let uu____3889 = pickBranch cfg scrut1 branches  in
                      match uu____3889 with
                      | FStar_Pervasives_Native.Some (branch1,args1) ->
                          let uu____3910 =
                            FStar_List.fold_left
                              (fun bs1  -> fun x  -> x :: bs1) bs args1
                             in
                          translate cfg uu____3910 branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                            make_branches))
                | FStar_TypeChecker_NBETerm.Constant c ->
                    (debug1
                       (fun uu____3933  ->
                          let uu____3934 =
                            FStar_TypeChecker_NBETerm.t_to_string scrut1  in
                          FStar_Util.print1 "Match constant : %s\n"
                            uu____3934);
                     (let uu____3935 = pickBranch cfg scrut1 branches  in
                      match uu____3935 with
                      | FStar_Pervasives_Native.Some (branch1,[]) ->
                          translate cfg bs branch1
                      | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                          translate cfg (arg :: bs) branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                            make_branches
                      | FStar_Pervasives_Native.Some (uu____3969,hd1::tl1) ->
                          failwith
                            "Impossible: Matching on constants cannot bind more than one variable"))
                | uu____3982 ->
                    FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                      make_branches)
             
             and make_branches readback1 =
               let rec process_pattern bs1 p =
                 let uu____4015 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____4049 =
                         FStar_List.fold_left
                           (fun uu____4087  ->
                              fun uu____4088  ->
                                match (uu____4087, uu____4088) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____4169 = process_pattern bs2 arg
                                       in
                                    (match uu____4169 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____4049 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____4258 =
                           let uu____4259 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4259  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4258
                          in
                       let uu____4260 =
                         let uu____4263 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4263 :: bs1  in
                       (uu____4260, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____4268 =
                           let uu____4269 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4269  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4268
                          in
                       let uu____4270 =
                         let uu____4273 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4273 :: bs1  in
                       (uu____4270, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____4283 =
                           let uu____4284 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4284  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4283
                          in
                       let uu____4285 =
                         let uu____4286 =
                           let uu____4293 =
                             let uu____4296 = translate cfg bs1 tm  in
                             readback1 uu____4296  in
                           (x, uu____4293)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____4286  in
                       (bs1, uu____4285)
                    in
                 match uu____4015 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___246_4316 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___246_4316.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____4335  ->
                    match uu____4335 with
                    | (pat,when_clause,e1) ->
                        let uu____4357 = process_pattern bs pat  in
                        (match uu____4357 with
                         | (bs',pat') ->
                             let uu____4370 =
                               let uu____4371 =
                                 let uu____4374 = translate cfg bs' e1  in
                                 readback1 uu____4374  in
                               (pat', when_clause, uu____4371)  in
                             FStar_Syntax_Util.branch uu____4370)) branches
              in let uu____4383 = translate cfg bs scrut  in case uu____4383
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
             let uu____4456 = make_rec_env lbs bs  in
             translate cfg uu____4456 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4460) -> translate cfg bs e1
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
            let uu____4487 =
              let uu____4494 = translate cfg bs typ  in
              let uu____4495 = fmap_opt (translate_univ bs) u  in
              (uu____4494, uu____4495)  in
            FStar_TypeChecker_NBETerm.Tot uu____4487
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4510 =
              let uu____4517 = translate cfg bs typ  in
              let uu____4518 = fmap_opt (translate_univ bs) u  in
              (uu____4517, uu____4518)  in
            FStar_TypeChecker_NBETerm.GTot uu____4510
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4524 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4524

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____4534 =
              let uu____4543 = readback cfg typ  in (uu____4543, u)  in
            FStar_Syntax_Syntax.Total uu____4534
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____4556 =
              let uu____4565 = readback cfg typ  in (uu____4565, u)  in
            FStar_Syntax_Syntax.GTotal uu____4556
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____4573 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____4573
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
        let uu____4579 = c  in
        match uu____4579 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags1;_} ->
            let uu____4599 = FStar_List.map (translate_univ bs) comp_univs
               in
            let uu____4600 = translate cfg bs result_typ  in
            let uu____4601 =
              FStar_List.map
                (fun x  ->
                   let uu____4629 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____4629, (FStar_Pervasives_Native.snd x))) effect_args
               in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____4599;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____4600;
              FStar_TypeChecker_NBETerm.effect_args = uu____4601;
              FStar_TypeChecker_NBETerm.flags = flags1
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____4638 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____4641 =
        FStar_List.map
          (fun x  ->
             let uu____4667 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____4667, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____4638;
        FStar_Syntax_Syntax.effect_args = uu____4641;
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
  fun uu____4668  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____4668 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____4703 =
                     let uu____4712 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____4712
                      in
                   (match uu____4703 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____4719 =
                          let uu____4720 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____4720
                           in
                        failwith uu____4719
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___247_4734 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___247_4734.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___247_4734.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___247_4734.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___247_4734.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___247_4734.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___247_4734.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___247_4734.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___247_4734.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____4741 =
                            let uu____4748 =
                              let uu____4749 =
                                let uu____4768 =
                                  let uu____4777 =
                                    let uu____4784 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____4784,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____4777]  in
                                (uu____4768, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____4749  in
                            FStar_Syntax_Syntax.mk uu____4748  in
                          uu____4741 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____4821 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____4821
                          then
                            let uu____4828 =
                              let uu____4833 =
                                let uu____4834 =
                                  FStar_Syntax_Embeddings.embed
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____4834  in
                              (uu____4833, FStar_Pervasives_Native.None)  in
                            let uu____4835 =
                              let uu____4842 =
                                let uu____4847 =
                                  let uu____4848 =
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____4848  in
                                (uu____4847, FStar_Pervasives_Native.None)
                                 in
                              [uu____4842]  in
                            uu____4828 :: uu____4835
                          else []  in
                        let t =
                          let uu____4867 =
                            let uu____4868 =
                              let uu____4869 =
                                FStar_Syntax_Util.un_uinst
                                  (FStar_Pervasives_Native.snd
                                     ed.FStar_Syntax_Syntax.bind_repr)
                                 in
                              translate cfg' [] uu____4869  in
                            iapp cfg uu____4868
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____4886 =
                            let uu____4887 =
                              let uu____4894 =
                                let uu____4899 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____4899, FStar_Pervasives_Native.None)
                                 in
                              let uu____4900 =
                                let uu____4907 =
                                  let uu____4912 = translate cfg' bs ty  in
                                  (uu____4912, FStar_Pervasives_Native.None)
                                   in
                                [uu____4907]  in
                              uu____4894 :: uu____4900  in
                            let uu____4925 =
                              let uu____4932 =
                                let uu____4939 =
                                  let uu____4946 =
                                    let uu____4951 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____4951,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____4952 =
                                    let uu____4959 =
                                      let uu____4966 =
                                        let uu____4971 =
                                          translate cfg bs body_lam  in
                                        (uu____4971,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____4966]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____4959
                                     in
                                  uu____4946 :: uu____4952  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____4939
                                 in
                              FStar_List.append maybe_range_arg uu____4932
                               in
                            FStar_List.append uu____4887 uu____4925  in
                          iapp cfg uu____4867 uu____4886  in
                        (debug cfg
                           (fun uu____5003  ->
                              let uu____5004 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____5004);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____5005);
                      FStar_Syntax_Syntax.pos = uu____5006;
                      FStar_Syntax_Syntax.vars = uu____5007;_},(e2,uu____5009)::[])
                   ->
                   translate
                     (let uu___248_5050 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___248_5050.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___248_5050.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___248_5050.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___248_5050.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___248_5050.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___248_5050.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___248_5050.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___248_5050.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app uu____5051 -> translate cfg bs e1
               | uu____5068 ->
                   let uu____5069 =
                     let uu____5070 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____5070
                      in
                   failwith uu____5069)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____5071  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____5071 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____5095 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____5095
              then
                let ed =
                  let uu____5097 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____5097
                   in
                let cfg' =
                  let uu___249_5099 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___249_5099.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___249_5099.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___249_5099.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___249_5099.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___249_5099.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___249_5099.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___249_5099.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___249_5099.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let t =
                  let uu____5101 =
                    let uu____5102 =
                      let uu____5103 =
                        FStar_Syntax_Util.un_uinst
                          (FStar_Pervasives_Native.snd
                             ed.FStar_Syntax_Syntax.return_repr)
                         in
                      translate cfg' [] uu____5103  in
                    iapp cfg uu____5102
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____5116 =
                    let uu____5117 =
                      let uu____5122 = translate cfg' bs ty  in
                      (uu____5122, FStar_Pervasives_Native.None)  in
                    let uu____5123 =
                      let uu____5130 =
                        let uu____5135 = translate cfg' bs e1  in
                        (uu____5135, FStar_Pervasives_Native.None)  in
                      [uu____5130]  in
                    uu____5117 :: uu____5123  in
                  iapp cfg uu____5101 uu____5116  in
                (debug cfg
                   (fun uu____5151  ->
                      let uu____5152 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____5152);
                 t)
              else
                (let uu____5154 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____5154 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____5157 =
                       let uu____5158 = FStar_Ident.text_of_lid msrc  in
                       let uu____5159 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____5158 uu____5159
                        in
                     failwith uu____5157
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____5160;
                       FStar_TypeChecker_Env.mtarget = uu____5161;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____5162;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____5184 =
                       let uu____5185 = FStar_Ident.text_of_lid msrc  in
                       let uu____5186 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____5185 uu____5186
                        in
                     failwith uu____5184
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____5187;
                       FStar_TypeChecker_Env.mtarget = uu____5188;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____5189;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____5228 =
                         let uu____5231 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____5231
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____5228
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___250_5247 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___250_5247.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___250_5247.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___250_5247.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___250_5247.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___250_5247.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___250_5247.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___250_5247.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___250_5247.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let t =
                       let uu____5249 = translate cfg' [] lift_lam  in
                       let uu____5250 =
                         let uu____5251 =
                           let uu____5256 = translate cfg bs e1  in
                           (uu____5256, FStar_Pervasives_Native.None)  in
                         [uu____5251]  in
                       iapp cfg uu____5249 uu____5250  in
                     (debug cfg
                        (fun uu____5268  ->
                           let uu____5269 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____5269);
                      t))

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____5285  ->
           let uu____5286 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____5286);
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
           let uu____5289 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____5289 FStar_Syntax_Util.exp_int
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
           let uu____5327 =
             FStar_List.fold_left
               (fun uu____5368  ->
                  fun tf  ->
                    match uu____5368 with
                    | (args,accus) ->
                        let uu____5418 = tf ()  in
                        (match uu____5418 with
                         | (xt,q) ->
                             let x1 =
                               let uu____5438 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____5438
                                in
                             let uu____5439 =
                               let uu____5442 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____5442 :: accus  in
                             (((x1, q) :: args), uu____5439))) ([], []) targs
              in
           (match uu____5327 with
            | (args,accus) ->
                let body =
                  let uu____5486 = f accus  in readback cfg uu____5486  in
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
             let uu____5518 =
               let uu____5519 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____5519  in
             readback cfg uu____5518  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____5550 =
             FStar_List.fold_left
               (fun uu____5591  ->
                  fun tf  ->
                    match uu____5591 with
                    | (args,accus) ->
                        let uu____5641 = tf ()  in
                        (match uu____5641 with
                         | (xt,q) ->
                             let x1 =
                               let uu____5661 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____5661
                                in
                             let uu____5662 =
                               let uu____5665 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____5665 :: accus  in
                             (((x1, q) :: args), uu____5662))) ([], []) targs
              in
           (match uu____5550 with
            | (args,accus) ->
                let cmp =
                  let uu____5709 = f accus  in readback_comp cfg uu____5709
                   in
                FStar_Syntax_Util.arrow args cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____5748  ->
                  match uu____5748 with
                  | (x1,q) ->
                      let uu____5759 = readback cfg x1  in (uu____5759, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____5778 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____5785::uu____5786 ->
                let uu____5789 =
                  let uu____5792 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____5792
                    (FStar_List.rev us)
                   in
                apply uu____5789
            | [] ->
                let uu____5793 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____5793)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____5834  ->
                  match uu____5834 with
                  | (x1,q) ->
                      let uu____5845 = readback cfg x1  in (uu____5845, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____5864 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____5871::uu____5872 ->
                let uu____5875 =
                  let uu____5878 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____5878
                    (FStar_List.rev us)
                   in
                apply uu____5875
            | [] ->
                let uu____5879 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____5879)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____5926  ->
                  match uu____5926 with
                  | (x1,q) ->
                      let uu____5937 = readback cfg x1  in (uu____5937, q))
               ts
              in
           let uu____5938 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____5938 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____5998  ->
                  match uu____5998 with
                  | (x1,q) ->
                      let uu____6009 = readback cfg x1  in (uu____6009, q))
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
            | uu____6039 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app cfg hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____6126 = curry hd1 args1  in
                 app cfg uu____6126 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
              in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef  in
           let uu____6128 = test_args ts args_no  in
           if uu____6128
           then
             let uu____6129 =
               let uu____6130 =
                 let uu____6131 = make_rec_env lbs bs  in
                 translate_letbinding cfg uu____6131 lb  in
               curry uu____6130 ts  in
             readback cfg uu____6129
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
                  (fun uu____6176  ->
                     match uu____6176 with
                     | (x1,q) ->
                         let uu____6187 = readback cfg x1  in (uu____6187, q))
                  ts
                 in
              match ts with
              | [] -> head1
              | uu____6192 -> FStar_Syntax_Util.mk_app head1 args)
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
  fun uu___244_6293  ->
    match uu___244_6293 with
    | Primops  -> FStar_TypeChecker_Env.Primops
    | UnfoldUntil d -> FStar_TypeChecker_Env.UnfoldUntil d
    | UnfoldOnly lids -> FStar_TypeChecker_Env.UnfoldOnly lids
    | UnfoldAttr attr -> FStar_TypeChecker_Env.UnfoldAttr attr
    | UnfoldTac  -> FStar_TypeChecker_Env.UnfoldTac
    | Reify  -> FStar_TypeChecker_Env.Reify
  
let (normalize_with_primitive_steps :
  FStar_TypeChecker_Cfg.primitive_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps  ->
    fun steps  ->
      fun env  ->
        fun e  ->
          let cfg = FStar_TypeChecker_Cfg.config' ps steps env  in
          let cfg1 =
            let uu___251_6329 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___252_6332 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___252_6332.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___252_6332.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___252_6332.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___252_6332.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___252_6332.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___252_6332.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___252_6332.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___252_6332.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___252_6332.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___252_6332.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___252_6332.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___252_6332.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___252_6332.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___252_6332.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___252_6332.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___252_6332.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___252_6332.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___252_6332.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___252_6332.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___252_6332.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___252_6332.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___252_6332.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___252_6332.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___252_6332.FStar_TypeChecker_Cfg.nbe_step)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___251_6329.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___251_6329.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___251_6329.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___251_6329.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___251_6329.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___251_6329.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___251_6329.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___251_6329.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____6336  ->
               let uu____6337 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with %s" uu____6337);
          (let uu____6338 = translate cfg1 [] e  in readback cfg1 uu____6338)
  
let (normalize' :
  FStar_TypeChecker_Env.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  -> fun e  -> normalize_with_primitive_steps [] steps env e
  
let (test_normalize :
  step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg =
          let uu____6378 = FStar_List.map step_as_normalizer_step steps  in
          FStar_TypeChecker_Cfg.config uu____6378 env  in
        let cfg1 =
          let uu___253_6382 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___254_6385 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___254_6385.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___254_6385.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___254_6385.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___254_6385.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___254_6385.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___254_6385.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___254_6385.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___254_6385.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___254_6385.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___254_6385.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___254_6385.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___254_6385.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___254_6385.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___254_6385.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___254_6385.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___254_6385.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___254_6385.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___254_6385.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___254_6385.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___254_6385.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___254_6385.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___254_6385.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___254_6385.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___254_6385.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___253_6382.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___253_6382.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___253_6382.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___253_6382.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___253_6382.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___253_6382.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___253_6382.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___253_6382.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____6389  ->
             let uu____6390 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____6390);
        (let r =
           let uu____6392 = translate cfg1 [] e  in readback cfg1 uu____6392
            in
         debug cfg1
           (fun uu____6396  ->
              let uu____6397 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "NBE returned %s" uu____6397);
         r)
  