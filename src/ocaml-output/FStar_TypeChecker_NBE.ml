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
           | FStar_Util.Inl uu____1508 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1512 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1512
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
  
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
            let uu____1802 = FStar_List.splitAt m targs  in
            (match uu____1802 with
             | (uu____1842,targs') ->
                 let targs'1 =
                   FStar_List.map
                     (fun targ  ->
                        fun l  ->
                          let uu____1933 =
                            let uu____1936 =
                              map_append FStar_Pervasives_Native.fst args l
                               in
                            FStar_List.rev uu____1936  in
                          targ uu____1933) targs'
                    in
                 FStar_TypeChecker_NBETerm.Lam
                   (((fun l  ->
                        let uu____1964 =
                          map_append FStar_Pervasives_Native.fst args l  in
                        f1 uu____1964)), targs'1, (n1 - m)))
          else
            if m = n1
            then
              (let uu____1980 =
                 FStar_List.map FStar_Pervasives_Native.fst args  in
               f1 uu____1980)
            else
              (let uu____1988 = FStar_List.splitAt n1 args  in
               match uu____1988 with
               | (args1,args') ->
                   let uu____2035 =
                     let uu____2036 =
                       FStar_List.map FStar_Pervasives_Native.fst args1  in
                     f1 uu____2036  in
                   iapp uu____2035 args')
      | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
          FStar_TypeChecker_NBETerm.Accu (a, (FStar_List.rev_append args ts))
      | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
          let rec aux args1 us1 ts1 =
            match args1 with
            | (FStar_TypeChecker_NBETerm.Univ u,uu____2155)::args2 ->
                aux args2 (u :: us1) ts1
            | a::args2 -> aux args2 us1 (a :: ts1)
            | [] -> (us1, ts1)  in
          let uu____2199 = aux args us ts  in
          (match uu____2199 with
           | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
      | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
          let rec aux args1 us1 ts1 =
            match args1 with
            | (FStar_TypeChecker_NBETerm.Univ u,uu____2326)::args2 ->
                aux args2 (u :: us1) ts1
            | a::args2 -> aux args2 us1 (a :: ts1)
            | [] -> (us1, ts1)  in
          let uu____2370 = aux args us ts  in
          (match uu____2370 with
           | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
      | FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs,acc,arity,tr_lb) ->
          let no_args = FStar_List.length args  in
          let no_acc = FStar_List.length acc  in
          let full_args = FStar_List.append acc args  in
          let uu____2472 = test_args full_args arity  in
          if uu____2472
          then
            (if (FStar_List.length full_args) > arity
             then
               let uu____2477 = FStar_List.splitAt arity full_args  in
               match uu____2477 with
               | (rargs,res) ->
                   let t =
                     let uu____2525 =
                       let uu____2526 = make_rec_env tr_lb lbs bs  in
                       tr_lb uu____2526 lb  in
                     iapp uu____2525 rargs  in
                   iapp t res
             else
               (let uu____2530 =
                  let uu____2531 = make_rec_env tr_lb lbs bs  in
                  tr_lb uu____2531 lb  in
                iapp uu____2530 full_args))
          else
            FStar_TypeChecker_NBETerm.Rec
              (lb, lbs, bs, full_args, arity, tr_lb)
      | FStar_TypeChecker_NBETerm.Quote uu____2553 ->
          let uu____2558 =
            let uu____2559 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2559  in
          failwith uu____2558
      | FStar_TypeChecker_NBETerm.Lazy uu____2560 ->
          let uu____2561 =
            let uu____2562 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2562  in
          failwith uu____2561
      | FStar_TypeChecker_NBETerm.Constant uu____2563 ->
          let uu____2564 =
            let uu____2565 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2565  in
          failwith uu____2564
      | FStar_TypeChecker_NBETerm.Univ uu____2566 ->
          let uu____2567 =
            let uu____2568 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2568  in
          failwith uu____2567
      | FStar_TypeChecker_NBETerm.Type_t uu____2569 ->
          let uu____2570 =
            let uu____2571 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2571  in
          failwith uu____2570
      | FStar_TypeChecker_NBETerm.Unknown  ->
          let uu____2572 =
            let uu____2573 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2573  in
          failwith uu____2572
      | FStar_TypeChecker_NBETerm.Refinement uu____2574 ->
          let uu____2589 =
            let uu____2590 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2590  in
          failwith uu____2589
      | FStar_TypeChecker_NBETerm.Arrow uu____2591 ->
          let uu____2612 =
            let uu____2613 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2613  in
          failwith uu____2612

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
          let uu____2628 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2629 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2628 uu____2629  in
        let uu____2630 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2630
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2636 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2638  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2636 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2644  ->
                     let uu____2645 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2645);
                (let uu____2646 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____2646 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____2656  ->
                           let uu____2657 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n" uu____2657);
                      (let uu____2658 =
                         let uu____2681 =
                           let f uu____2708 uu____2709 =
                             ((FStar_TypeChecker_NBETerm.Constant
                                 FStar_TypeChecker_NBETerm.Unit),
                               FStar_Pervasives_Native.None)
                              in
                           FStar_Common.tabulate arity f  in
                         ((fun args  ->
                             let args' =
                               FStar_List.map
                                 FStar_TypeChecker_NBETerm.as_arg args
                                in
                             let uu____2760 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 args'
                                in
                             match uu____2760 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____2771  ->
                                       let uu____2772 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____2773 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____2772 uu____2773);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____2779  ->
                                       let uu____2780 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____2780);
                                  (let uu____2781 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp uu____2781 args'))), uu____2681,
                           arity)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____2658))
                 | FStar_Pervasives_Native.Some uu____2786 ->
                     (debug1
                        (fun uu____2792  ->
                           let uu____2793 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____2793);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____2798 ->
                     (debug1
                        (fun uu____2806  ->
                           let uu____2807 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____2807);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2815;
                        FStar_Syntax_Syntax.sigquals = uu____2816;
                        FStar_Syntax_Syntax.sigmeta = uu____2817;
                        FStar_Syntax_Syntax.sigattrs = uu____2818;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____2887  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2895  ->
                                 let uu____2896 =
                                   let uu____2897 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2897
                                    in
                                 let uu____2898 =
                                   let uu____2899 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2899
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2896 uu____2898);
                            debug1
                              (fun uu____2907  ->
                                 let uu____2908 =
                                   let uu____2909 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2909
                                    in
                                 let uu____2910 =
                                   let uu____2911 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2911
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2908 uu____2910);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____2912 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2920;
                        FStar_Syntax_Syntax.sigquals = uu____2921;
                        FStar_Syntax_Syntax.sigmeta = uu____2922;
                        FStar_Syntax_Syntax.sigattrs = uu____2923;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____2992  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____3000  ->
                                 let uu____3001 =
                                   let uu____3002 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3002
                                    in
                                 let uu____3003 =
                                   let uu____3004 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3004
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____3001 uu____3003);
                            debug1
                              (fun uu____3012  ->
                                 let uu____3013 =
                                   let uu____3014 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3014
                                    in
                                 let uu____3015 =
                                   let uu____3016 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3016
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____3013 uu____3015);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____3017 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        | uu____3062 ->
            let uu____3065 =
              let uu____3088 =
                FStar_List.map
                  (fun uu____3113  ->
                     fun _ts  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____3088,
                (FStar_List.length us))
               in
            FStar_TypeChecker_NBETerm.Lam uu____3065

and (mkRec' :
  (FStar_TypeChecker_NBETerm.t Prims.list ->
     FStar_Syntax_Syntax.letbinding -> FStar_TypeChecker_NBETerm.t)
    ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        FStar_TypeChecker_NBETerm.t Prims.list -> FStar_TypeChecker_NBETerm.t)
  =
  fun callback  ->
    fun b  ->
      fun bs  ->
        fun env  ->
          let ar = count_abstractions b.FStar_Syntax_Syntax.lbdef  in
          FStar_TypeChecker_NBETerm.Rec (b, bs, env, [], ar, callback)

and (mkRec :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        FStar_TypeChecker_NBETerm.t Prims.list -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun b  ->
      fun bs  -> fun env  -> mkRec' (translate_letbinding cfg) b bs env

and (make_rec_env :
  (FStar_TypeChecker_NBETerm.t Prims.list ->
     FStar_Syntax_Syntax.letbinding -> FStar_TypeChecker_NBETerm.t)
    ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_TypeChecker_NBETerm.t Prims.list)
  =
  fun callback  ->
    fun lbs  ->
      fun bs  ->
        let rec aux lbs1 lbs0 bs1 bs0 =
          match lbs1 with
          | [] -> bs1
          | lb::lbs' ->
              let uu____3256 =
                let uu____3259 = mkRec' callback lb lbs0 bs0  in uu____3259
                  :: bs1
                 in
              aux lbs' lbs0 uu____3256 bs0
           in
        aux lbs lbs bs bs

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____3273 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____3273
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____3279 ->
        let uu____3280 =
          let uu____3281 =
            let uu____3282 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____3282 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____3281  in
        failwith uu____3280

and (translate_pat : FStar_Syntax_Syntax.pat -> FStar_TypeChecker_NBETerm.t)
  =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3285 = translate_constant c  in
        FStar_TypeChecker_NBETerm.Constant uu____3285
    | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
        let uu____3304 = FStar_TypeChecker_NBETerm.mkConstruct cfv [] []  in
        let uu____3309 =
          FStar_List.map
            (fun uu____3324  ->
               match uu____3324 with
               | (p1,uu____3336) ->
                   let uu____3337 = translate_pat p1  in
                   (uu____3337, FStar_Pervasives_Native.None)) pats
           in
        iapp uu____3304 uu____3309
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
          (fun uu____3368  ->
             let uu____3369 =
               let uu____3370 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____3370  in
             let uu____3371 =
               let uu____3372 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____3372  in
             FStar_Util.print2 "Term: %s - %s\n" uu____3369 uu____3371);
        debug1
          (fun uu____3378  ->
             let uu____3379 =
               let uu____3380 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____3380  in
             FStar_Util.print1 "BS list: %s\n" uu____3379);
        (let uu____3385 =
           let uu____3386 = FStar_Syntax_Subst.compress e  in
           uu____3386.FStar_Syntax_Syntax.n  in
         match uu____3385 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____3389,uu____3390) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3428 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3428
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then FStar_List.nth bs db.FStar_Syntax_Syntax.index
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3444  ->
                   let uu____3445 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3446 =
                     let uu____3447 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3447
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____3445 uu____3446);
              (let uu____3452 = translate cfg bs t  in
               let uu____3453 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3457 =
                        let uu____3458 = translate_univ bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____3458  in
                      FStar_TypeChecker_NBETerm.as_arg uu____3457) us
                  in
               iapp uu____3452 uu____3453))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3460 = translate_univ bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____3460
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____3483 =
               let uu____3504 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____3574 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____3574, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____3504)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____3483
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____3643  ->
                     let uu____3644 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____3644)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3646,uu____3647) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____3708,uu____3709) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____3734) ->
             let uu____3759 =
               let uu____3782 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____3852 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____3852, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____3782, (FStar_List.length xs))
                in
             FStar_TypeChecker_NBETerm.Lam uu____3759
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3908;
                FStar_Syntax_Syntax.vars = uu____3909;_},arg::more::args)
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let uu____3969 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3969 with
              | (reifyh,uu____3987) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app reifyh [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____4031 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____4031)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____4040;
                FStar_Syntax_Syntax.vars = uu____4041;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___250_4083 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___250_4083.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___250_4083.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___250_4083.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___250_4083.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___250_4083.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___250_4083.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___250_4083.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___250_4083.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____4121  ->
                   let uu____4122 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____4123 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ (%s)\n" uu____4122
                     uu____4123);
              (let uu____4124 = translate cfg bs head1  in
               let uu____4125 =
                 FStar_List.map
                   (fun x  ->
                      let uu____4147 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____4147, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp uu____4124 uu____4125))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               debug1
                 (fun uu____4213  ->
                    let uu____4214 =
                      let uu____4215 = readback cfg scrut1  in
                      FStar_Syntax_Print.term_to_string uu____4215  in
                    FStar_Util.print1 "Match case: (%s)\n" uu____4214);
               (match scrut1 with
                | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                    (debug1
                       (fun uu____4240  ->
                          let uu____4241 =
                            let uu____4242 =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____4265  ->
                                      match uu____4265 with
                                      | (x,q) ->
                                          let uu____4278 =
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              x
                                             in
                                          Prims.strcat
                                            (if FStar_Util.is_some q
                                             then "#"
                                             else "") uu____4278))
                               in
                            FStar_All.pipe_right uu____4242
                              (FStar_String.concat "; ")
                             in
                          FStar_Util.print1 "Match args: %s\n" uu____4241);
                     (let uu____4282 = pickBranch cfg scrut1 branches  in
                      match uu____4282 with
                      | FStar_Pervasives_Native.Some (branch1,args1) ->
                          let uu____4303 =
                            FStar_List.fold_left
                              (fun bs1  -> fun x  -> x :: bs1) bs args1
                             in
                          translate cfg uu____4303 branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                            make_branches))
                | FStar_TypeChecker_NBETerm.Constant c ->
                    (debug1
                       (fun uu____4326  ->
                          let uu____4327 =
                            FStar_TypeChecker_NBETerm.t_to_string scrut1  in
                          FStar_Util.print1 "Match constant : %s\n"
                            uu____4327);
                     (let uu____4328 = pickBranch cfg scrut1 branches  in
                      match uu____4328 with
                      | FStar_Pervasives_Native.Some (branch1,[]) ->
                          translate cfg bs branch1
                      | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                          translate cfg (arg :: bs) branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                            make_branches
                      | FStar_Pervasives_Native.Some (uu____4362,hd1::tl1) ->
                          failwith
                            "Impossible: Matching on constants cannot bind more than one variable"))
                | uu____4375 ->
                    FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                      make_branches)
             
             and make_branches readback1 =
               let rec process_pattern bs1 p =
                 let uu____4408 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____4442 =
                         FStar_List.fold_left
                           (fun uu____4480  ->
                              fun uu____4481  ->
                                match (uu____4480, uu____4481) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____4562 = process_pattern bs2 arg
                                       in
                                    (match uu____4562 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____4442 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____4651 =
                           let uu____4652 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4652  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4651
                          in
                       let uu____4653 =
                         let uu____4656 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4656 :: bs1  in
                       (uu____4653, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____4661 =
                           let uu____4662 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4662  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4661
                          in
                       let uu____4663 =
                         let uu____4666 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4666 :: bs1  in
                       (uu____4663, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____4676 =
                           let uu____4677 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4677  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4676
                          in
                       let uu____4678 =
                         let uu____4679 =
                           let uu____4686 =
                             let uu____4689 = translate cfg bs1 tm  in
                             readback1 uu____4689  in
                           (x, uu____4686)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____4679  in
                       (bs1, uu____4678)
                    in
                 match uu____4408 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___251_4709 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___251_4709.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____4728  ->
                    match uu____4728 with
                    | (pat,when_clause,e1) ->
                        let uu____4750 = process_pattern bs pat  in
                        (match uu____4750 with
                         | (bs',pat') ->
                             let uu____4763 =
                               let uu____4764 =
                                 let uu____4767 = translate cfg bs' e1  in
                                 readback1 uu____4767  in
                               (pat', when_clause, uu____4764)  in
                             FStar_Syntax_Util.branch uu____4763)) branches
              in let uu____4776 = translate cfg bs scrut  in case uu____4776
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
             let uu____4849 = make_rec_env (translate_letbinding cfg) lbs bs
                in
             translate cfg uu____4849 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4853) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____4874  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____4885 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____4900  ->
                      match uu____4900 with
                      | (bv,t1) ->
                          let uu____4907 =
                            let uu____4914 = readback cfg t1  in
                            (bv, uu____4914)  in
                          FStar_Syntax_Syntax.NT uu____4907) uu____4885
                  in
               let uu____4919 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____4919  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close1 qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close1 qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
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
            let uu____4938 =
              let uu____4945 = translate cfg bs typ  in
              let uu____4946 = fmap_opt (translate_univ bs) u  in
              (uu____4945, uu____4946)  in
            FStar_TypeChecker_NBETerm.Tot uu____4938
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4961 =
              let uu____4968 = translate cfg bs typ  in
              let uu____4969 = fmap_opt (translate_univ bs) u  in
              (uu____4968, uu____4969)  in
            FStar_TypeChecker_NBETerm.GTot uu____4961
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4975 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4975

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____4985 =
              let uu____4994 = readback cfg typ  in (uu____4994, u)  in
            FStar_Syntax_Syntax.Total uu____4985
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____5007 =
              let uu____5016 = readback cfg typ  in (uu____5016, u)  in
            FStar_Syntax_Syntax.GTotal uu____5007
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____5024 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____5024
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
        let uu____5030 = c  in
        match uu____5030 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags1;_} ->
            let uu____5050 = FStar_List.map (translate_univ bs) comp_univs
               in
            let uu____5051 = translate cfg bs result_typ  in
            let uu____5052 =
              FStar_List.map
                (fun x  ->
                   let uu____5080 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____5080, (FStar_Pervasives_Native.snd x))) effect_args
               in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____5050;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____5051;
              FStar_TypeChecker_NBETerm.effect_args = uu____5052;
              FStar_TypeChecker_NBETerm.flags = flags1
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____5089 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____5092 =
        FStar_List.map
          (fun x  ->
             let uu____5118 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____5118, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____5089;
        FStar_Syntax_Syntax.effect_args = uu____5092;
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
  fun uu____5119  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____5119 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____5154 =
                     let uu____5163 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____5163
                      in
                   (match uu____5154 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5170 =
                          let uu____5171 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____5171
                           in
                        failwith uu____5170
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___252_5185 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___252_5185.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___252_5185.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___252_5185.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___252_5185.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___252_5185.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___252_5185.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___252_5185.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___252_5185.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____5192 =
                            let uu____5199 =
                              let uu____5200 =
                                let uu____5219 =
                                  let uu____5228 =
                                    let uu____5235 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____5235,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____5228]  in
                                (uu____5219, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____5200  in
                            FStar_Syntax_Syntax.mk uu____5199  in
                          uu____5192 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____5272 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____5272
                          then
                            let uu____5279 =
                              let uu____5284 =
                                let uu____5285 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____5285  in
                              (uu____5284, FStar_Pervasives_Native.None)  in
                            let uu____5286 =
                              let uu____5293 =
                                let uu____5298 =
                                  let uu____5299 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____5299  in
                                (uu____5298, FStar_Pervasives_Native.None)
                                 in
                              [uu____5293]  in
                            uu____5279 :: uu____5286
                          else []  in
                        let t =
                          let uu____5318 =
                            let uu____5319 =
                              let uu____5320 =
                                FStar_Syntax_Util.un_uinst
                                  (FStar_Pervasives_Native.snd
                                     ed.FStar_Syntax_Syntax.bind_repr)
                                 in
                              translate cfg' [] uu____5320  in
                            iapp uu____5319
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____5337 =
                            let uu____5338 =
                              let uu____5345 =
                                let uu____5350 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____5350, FStar_Pervasives_Native.None)
                                 in
                              let uu____5351 =
                                let uu____5358 =
                                  let uu____5363 = translate cfg' bs ty  in
                                  (uu____5363, FStar_Pervasives_Native.None)
                                   in
                                [uu____5358]  in
                              uu____5345 :: uu____5351  in
                            let uu____5376 =
                              let uu____5383 =
                                let uu____5390 =
                                  let uu____5397 =
                                    let uu____5402 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____5402,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____5403 =
                                    let uu____5410 =
                                      let uu____5417 =
                                        let uu____5422 =
                                          translate cfg bs body_lam  in
                                        (uu____5422,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____5417]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____5410
                                     in
                                  uu____5397 :: uu____5403  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____5390
                                 in
                              FStar_List.append maybe_range_arg uu____5383
                               in
                            FStar_List.append uu____5338 uu____5376  in
                          iapp uu____5318 uu____5337  in
                        (debug cfg
                           (fun uu____5454  ->
                              let uu____5455 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____5455);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____5456);
                      FStar_Syntax_Syntax.pos = uu____5457;
                      FStar_Syntax_Syntax.vars = uu____5458;_},(e2,uu____5460)::[])
                   ->
                   translate
                     (let uu___253_5501 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___253_5501.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___253_5501.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___253_5501.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___253_5501.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___253_5501.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___253_5501.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___253_5501.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___253_5501.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app uu____5502 -> translate cfg bs e1
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____5639  ->
                             match uu____5639 with
                             | (pat,wopt,tm) ->
                                 let uu____5687 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____5687)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   translate
                     (let uu___254_5721 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___254_5721.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___254_5721.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___254_5721.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___254_5721.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___254_5721.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___254_5721.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___254_5721.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___254_5721.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs tm
               | uu____5722 ->
                   let uu____5723 =
                     let uu____5724 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____5724
                      in
                   failwith uu____5723)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____5725  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____5725 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____5749 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____5749
              then
                let ed =
                  let uu____5751 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____5751
                   in
                let cfg' =
                  let uu___255_5753 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___255_5753.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___255_5753.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___255_5753.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___255_5753.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___255_5753.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___255_5753.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___255_5753.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___255_5753.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let t =
                  let uu____5755 =
                    let uu____5756 =
                      let uu____5757 =
                        FStar_Syntax_Util.un_uinst
                          (FStar_Pervasives_Native.snd
                             ed.FStar_Syntax_Syntax.return_repr)
                         in
                      translate cfg' [] uu____5757  in
                    iapp uu____5756
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____5770 =
                    let uu____5771 =
                      let uu____5776 = translate cfg' bs ty  in
                      (uu____5776, FStar_Pervasives_Native.None)  in
                    let uu____5777 =
                      let uu____5784 =
                        let uu____5789 = translate cfg' bs e1  in
                        (uu____5789, FStar_Pervasives_Native.None)  in
                      [uu____5784]  in
                    uu____5771 :: uu____5777  in
                  iapp uu____5755 uu____5770  in
                (debug cfg
                   (fun uu____5805  ->
                      let uu____5806 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____5806);
                 t)
              else
                (let uu____5808 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____5808 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____5811 =
                       let uu____5812 = FStar_Ident.text_of_lid msrc  in
                       let uu____5813 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____5812 uu____5813
                        in
                     failwith uu____5811
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____5814;
                       FStar_TypeChecker_Env.mtarget = uu____5815;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____5816;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____5838 =
                       let uu____5839 = FStar_Ident.text_of_lid msrc  in
                       let uu____5840 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____5839 uu____5840
                        in
                     failwith uu____5838
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____5841;
                       FStar_TypeChecker_Env.mtarget = uu____5842;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____5843;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____5882 =
                         let uu____5885 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____5885
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____5882
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___256_5901 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___256_5901.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___256_5901.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___256_5901.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___256_5901.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___256_5901.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___256_5901.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___256_5901.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___256_5901.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let t =
                       let uu____5903 = translate cfg' [] lift_lam  in
                       let uu____5904 =
                         let uu____5905 =
                           let uu____5910 = translate cfg bs e1  in
                           (uu____5910, FStar_Pervasives_Native.None)  in
                         [uu____5905]  in
                       iapp uu____5903 uu____5904  in
                     (debug cfg
                        (fun uu____5922  ->
                           let uu____5923 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____5923);
                      t))

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____5939  ->
           let uu____5940 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____5940);
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
           let uu____5943 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____5943 FStar_Syntax_Util.exp_int
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
           FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range
             r FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Type_t u ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lam (f,targs,arity) ->
           let uu____5985 =
             FStar_List.fold_left
               (fun uu____6028  ->
                  fun tf  ->
                    match uu____6028 with
                    | (args_rev,accus_rev) ->
                        let uu____6080 = tf accus_rev  in
                        (match uu____6080 with
                         | (xt,q) ->
                             let x1 =
                               let uu____6100 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____6100
                                in
                             let uu____6101 =
                               let uu____6104 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____6104 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____6101))) ([], [])
               targs
              in
           (match uu____5985 with
            | (args_rev,accus_rev) ->
                let body =
                  let uu____6148 = f (FStar_List.rev accus_rev)  in
                  readback cfg uu____6148  in
                FStar_Syntax_Util.abs (FStar_List.rev args_rev) body
                  FStar_Pervasives_Native.None)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____6176 =
               let uu____6177 =
                 let uu____6178 = targ ()  in
                 FStar_Pervasives_Native.fst uu____6178  in
               readback cfg uu____6177  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____6176
              in
           let body =
             let uu____6184 =
               let uu____6185 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____6185  in
             readback cfg uu____6184  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____6220 =
             FStar_List.fold_left
               (fun uu____6263  ->
                  fun tf  ->
                    match uu____6263 with
                    | (args_rev,accus_rev) ->
                        let uu____6315 = tf accus_rev  in
                        (match uu____6315 with
                         | (xt,q) ->
                             let x1 =
                               let uu____6335 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____6335
                                in
                             let uu____6336 =
                               let uu____6339 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____6339 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____6336))) ([], [])
               targs
              in
           (match uu____6220 with
            | (args_rev,accus_rev) ->
                let cmp =
                  let uu____6383 = f (FStar_List.rev accus_rev)  in
                  readback_comp cfg uu____6383  in
                FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____6426  ->
                  match uu____6426 with
                  | (x1,q) ->
                      let uu____6437 = readback cfg x1  in (uu____6437, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____6456 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____6463::uu____6464 ->
                let uu____6467 =
                  let uu____6470 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____6470
                    (FStar_List.rev us)
                   in
                apply uu____6467
            | [] ->
                let uu____6471 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____6471)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____6512  ->
                  match uu____6512 with
                  | (x1,q) ->
                      let uu____6523 = readback cfg x1  in (uu____6523, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____6542 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____6549::uu____6550 ->
                let uu____6553 =
                  let uu____6556 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____6556
                    (FStar_List.rev us)
                   in
                apply uu____6553
            | [] ->
                let uu____6557 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____6557)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____6604  ->
                  match uu____6604 with
                  | (x1,q) ->
                      let uu____6615 = readback cfg x1  in (uu____6615, q))
               ts
              in
           let uu____6616 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____6616 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____6676  ->
                  match uu____6676 with
                  | (x1,q) ->
                      let uu____6687 = readback cfg x1  in (uu____6687, q))
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
            | uu____6717 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs,args,arity,_cfg) ->
           let head1 =
             match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inl bv ->
                 let uu____6772 =
                   let uu____6779 =
                     let uu____6780 =
                       let uu____6793 = FStar_Syntax_Syntax.bv_to_name bv  in
                       ((true, lbs), uu____6793)  in
                     FStar_Syntax_Syntax.Tm_let uu____6780  in
                   FStar_Syntax_Syntax.mk uu____6779  in
                 uu____6772 FStar_Pervasives_Native.None
                   FStar_Range.dummyRange
             | FStar_Util.Inr fv ->
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                   FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 =
             map_rev
               (fun uu____6829  ->
                  match uu____6829 with
                  | (x1,q) ->
                      let uu____6840 = readback cfg x1  in (uu____6840, q))
               args
              in
           (match args1 with
            | [] -> head1
            | uu____6845 -> FStar_Syntax_Util.mk_app head1 args1)
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
    match projectee with | Primops  -> true | uu____6879 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____6886 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____6902 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____6922 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____6935 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____6941 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___249_6946  ->
    match uu___249_6946 with
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
            let uu___257_6982 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___258_6985 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___258_6985.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___258_6985.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___258_6985.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___258_6985.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___258_6985.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___258_6985.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___258_6985.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___258_6985.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___258_6985.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___258_6985.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___258_6985.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___258_6985.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___258_6985.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___258_6985.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___258_6985.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___258_6985.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___258_6985.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___258_6985.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___258_6985.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___258_6985.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___258_6985.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___258_6985.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___258_6985.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___258_6985.FStar_TypeChecker_Cfg.nbe_step)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___257_6982.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___257_6982.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___257_6982.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___257_6982.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___257_6982.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___257_6982.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___257_6982.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___257_6982.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____6989  ->
               let uu____6990 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with %s" uu____6990);
          (let uu____6991 = translate cfg1 [] e  in readback cfg1 uu____6991)
  
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
          let uu___259_7013 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___260_7016 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___260_7016.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___260_7016.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___260_7016.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___260_7016.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___260_7016.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___260_7016.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___260_7016.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___260_7016.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___260_7016.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___260_7016.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___260_7016.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___260_7016.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___260_7016.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___260_7016.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___260_7016.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___260_7016.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___260_7016.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___260_7016.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___260_7016.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___260_7016.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___260_7016.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___260_7016.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___260_7016.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___260_7016.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___259_7013.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___259_7013.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___259_7013.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___259_7013.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___259_7013.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___259_7013.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___259_7013.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___259_7013.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____7020  ->
             let uu____7021 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____7021);
        (let r =
           let uu____7023 = translate cfg1 [] e  in readback cfg1 uu____7023
            in
         debug cfg1
           (fun uu____7027  ->
              let uu____7028 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "NBE returned %s" uu____7028);
         r)
  