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
  
let drop_until : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 =
        match l1 with
        | [] -> []
        | x::xs -> let uu____317 = f x  in if uu____317 then l1 else aux xs
         in
      aux l
  
let (trim : Prims.bool Prims.list -> Prims.bool Prims.list) =
  fun l  ->
    let uu____334 = drop_until FStar_Pervasives.id (FStar_List.rev l)  in
    FStar_List.rev uu____334
  
let (implies : Prims.bool -> Prims.bool -> Prims.bool) =
  fun b1  ->
    fun b2  ->
      match (b1, b2) with | (false ,uu____347) -> true | (true ,b21) -> b21
  
let (debug : FStar_TypeChecker_Cfg.cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____364 =
        let uu____365 = FStar_TypeChecker_Cfg.cfg_env cfg  in
        FStar_TypeChecker_Env.debug uu____365 (FStar_Options.Other "NBE")  in
      if uu____364 then f () else ()
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____372 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____372
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____389 = FStar_Syntax_Print.sigelt_to_string_short v1  in
             FStar_Util.print2 "%s -> %%s\n" k uu____389) ()
  
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
            debug cfg
              (fun uu____492  ->
                 let uu____493 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                 let uu____494 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____493
                   uu____494);
            (let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv -> FStar_Util.Inl [scrutinee]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee]
               | FStar_Syntax_Syntax.Pat_dot_term uu____514 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____539  ->
                          let uu____540 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____541 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu____540
                            uu____541);
                     (match c with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____544 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____557 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____557
                           | uu____558 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____560))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____562) ->
                               st = p1
                           | uu____563 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____569 -> false)
                      | uu____570 -> false)
                      in
                   let uu____571 = matches_const scrutinee s  in
                   if uu____571
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____692)::rest_a,(p2,uu____695)::rest_p) ->
                         let uu____729 = matches_pat t p2  in
                         (match uu____729 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____754 -> FStar_Util.Inr false  in
                   (match scrutinee with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____798 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                        if uu____798
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____812 -> FStar_Util.Inr true)
                in
             let res_to_string uu___252_826 =
               match uu___252_826 with
               | FStar_Util.Inr b ->
                   let uu____836 = FStar_Util.string_of_bool b  in
                   Prims.strcat "Inr " uu____836
               | FStar_Util.Inl bs ->
                   let uu____842 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.strcat "Inl " uu____842
                in
             debug cfg
               (fun uu____848  ->
                  let uu____849 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____850 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____851 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____849
                    uu____850 uu____851);
             r)
             in
          match branches1 with
          | [] -> failwith "Branch not found"
          | (p,_wopt,e)::branches2 ->
              let uu____890 = matches_pat scrut1 p  in
              (match uu____890 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____913  ->
                         let uu____914 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____914);
                    FStar_Pervasives_Native.Some (e, matches))
               | FStar_Util.Inr (false ) ->
                   pickBranch_aux scrut1 branches2 branches0
               | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
           in
        pickBranch_aux scrut branches branches
  
let (test_args :
  (FStar_TypeChecker_NBETerm.t,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    Prims.bool Prims.list ->
      (Prims.bool,FStar_TypeChecker_NBETerm.args,FStar_TypeChecker_NBETerm.args)
        FStar_Pervasives_Native.tuple3)
  =
  fun ts  ->
    fun ar_list  ->
      let rec aux ts1 ar_list1 acc res =
        match (ts1, ar_list1) with
        | (uu____1064,[]) -> (true, (FStar_List.rev acc), ts1)
        | ([],uu____1095::uu____1096) -> (false, (FStar_List.rev acc), [])
        | (t::ts2,b::bs) ->
            let uu____1159 =
              res &&
                (let uu____1161 =
                   let uu____1162 =
                     FStar_TypeChecker_NBETerm.isAccu
                       (FStar_Pervasives_Native.fst t)
                      in
                   Prims.op_Negation uu____1162  in
                 implies b uu____1161)
               in
            aux ts2 bs (t :: acc) uu____1159
         in
      aux ts ar_list [] true
  
let (find_sigelt_in_gamma :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.env ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lid  ->
        let mapper uu____1215 =
          match uu____1215 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1298  ->
                         let uu____1299 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1299);
                    FStar_Pervasives_Native.Some elt)
               | uu____1300 -> FStar_Pervasives_Native.None)
           in
        let uu____1315 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1315 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1359 -> true
    | uu____1360 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | uu____1367 -> failwith "Not a universe"
  
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
              (uu____1380,uu____1381,uu____1382,uu____1383,uu____1384,uu____1385);
            FStar_Syntax_Syntax.sigrng = uu____1386;
            FStar_Syntax_Syntax.sigquals = uu____1387;
            FStar_Syntax_Syntax.sigmeta = uu____1388;
            FStar_Syntax_Syntax.sigattrs = uu____1389;_},uu____1390),uu____1391)
        -> true
    | uu____1446 -> false
  
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
            let uu____1472 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1472
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1476 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1476
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____1479 -> u2
        | FStar_Syntax_Syntax.U_unif uu____1480 -> u2
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
           | FStar_Util.Inl uu____1510 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1514 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1514
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
        match f with
        | FStar_TypeChecker_NBETerm.Lam (f1,targs,n1,res) ->
            let m = FStar_List.length args  in
            if m < n1
            then
              let uu____1860 = FStar_List.splitAt m targs  in
              (match uu____1860 with
               | (uu____1900,targs') ->
                   let targs'1 =
                     FStar_List.map
                       (fun targ  ->
                          fun l  ->
                            let uu____1991 =
                              let uu____1994 =
                                map_append FStar_Pervasives_Native.fst args l
                                 in
                              FStar_List.rev uu____1994  in
                            targ uu____1991) targs'
                      in
                   FStar_TypeChecker_NBETerm.Lam
                     (((fun l  ->
                          let uu____2027 =
                            map_append FStar_Pervasives_Native.fst args l  in
                          f1 uu____2027)), targs'1, (n1 - m), res))
            else
              if m = n1
              then
                (let uu____2043 =
                   FStar_List.map FStar_Pervasives_Native.fst args  in
                 f1 uu____2043)
              else
                (let uu____2051 = FStar_List.splitAt n1 args  in
                 match uu____2051 with
                 | (args1,args') ->
                     let uu____2098 =
                       let uu____2099 =
                         FStar_List.map FStar_Pervasives_Native.fst args1  in
                       f1 uu____2099  in
                     iapp cfg uu____2098 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____2218)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____2262 = aux args us ts  in
            (match uu____2262 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____2389)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____2433 = aux args us ts  in
            (match uu____2433 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
        | FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs,acc,ar,ar_lst,tr_lb) ->
            let no_args = FStar_List.length args  in
            if ar > no_args
            then
              FStar_TypeChecker_NBETerm.Rec
                (lb, lbs, bs, (FStar_List.append acc args), (ar - no_args),
                  ar_lst, tr_lb)
            else
              if ar = (Prims.parse_int "0")
              then
                FStar_TypeChecker_NBETerm.Rec
                  (lb, lbs, bs, (FStar_List.append acc args), ar, ar_lst,
                    tr_lb)
              else
                (let full_args = FStar_List.append acc args  in
                 let uu____2593 = test_args full_args ar_lst  in
                 match uu____2593 with
                 | (can_unfold,args1,res) ->
                     if
                       Prims.op_Negation
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                     then
                       (debug cfg
                          (fun uu____2606  ->
                             let uu____2607 =
                               FStar_Syntax_Print.lbname_to_string
                                 lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Util.print1
                               "Zeta is not set; will not unfold %s\n"
                               uu____2607);
                        FStar_TypeChecker_NBETerm.Rec
                          (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                            ar_lst, tr_lb))
                     else
                       if can_unfold
                       then
                         (debug cfg
                            (fun uu____2632  ->
                               let uu____2633 =
                                 FStar_Syntax_Print.lbname_to_string
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               FStar_Util.print1
                                 "Beta reducing recursive function %s\n"
                                 uu____2633);
                          (match res with
                           | [] ->
                               let uu____2638 =
                                 let uu____2639 = make_rec_env tr_lb lbs bs
                                    in
                                 tr_lb uu____2639 lb  in
                               iapp cfg uu____2638 args1
                           | uu____2642::uu____2643 ->
                               let t =
                                 let uu____2659 =
                                   let uu____2660 = make_rec_env tr_lb lbs bs
                                      in
                                   tr_lb uu____2660 lb  in
                                 iapp cfg uu____2659 args1  in
                               iapp cfg t res))
                       else
                         FStar_TypeChecker_NBETerm.Rec
                           (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                             ar_lst, tr_lb))
        | FStar_TypeChecker_NBETerm.Quote uu____2684 ->
            let uu____2689 =
              let uu____2690 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2690  in
            failwith uu____2689
        | FStar_TypeChecker_NBETerm.Lazy uu____2691 ->
            let uu____2704 =
              let uu____2705 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2705  in
            failwith uu____2704
        | FStar_TypeChecker_NBETerm.Constant uu____2706 ->
            let uu____2707 =
              let uu____2708 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2708  in
            failwith uu____2707
        | FStar_TypeChecker_NBETerm.Univ uu____2709 ->
            let uu____2710 =
              let uu____2711 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2711  in
            failwith uu____2710
        | FStar_TypeChecker_NBETerm.Type_t uu____2712 ->
            let uu____2713 =
              let uu____2714 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2714  in
            failwith uu____2713
        | FStar_TypeChecker_NBETerm.Unknown  ->
            let uu____2715 =
              let uu____2716 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2716  in
            failwith uu____2715
        | FStar_TypeChecker_NBETerm.Refinement uu____2717 ->
            let uu____2732 =
              let uu____2733 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2733  in
            failwith uu____2732
        | FStar_TypeChecker_NBETerm.Arrow uu____2734 ->
            let uu____2755 =
              let uu____2756 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2756  in
            failwith uu____2755

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
          let uu____2771 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2772 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2771 uu____2772  in
        let uu____2773 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2773
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2779 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2781  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2779 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2787  ->
                     let uu____2788 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2788);
                (let uu____2789 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____2789 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____2799  ->
                           let uu____2800 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n" uu____2800);
                      (let uu____2801 =
                         let uu____2831 =
                           let f uu____2858 uu____2859 =
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
                             let uu____2915 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 (iapp cfg) args'
                                in
                             match uu____2915 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____2926  ->
                                       let uu____2927 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____2928 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____2927 uu____2928);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____2934  ->
                                       let uu____2935 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____2935);
                                  (let uu____2936 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp cfg uu____2936 args'))), uu____2831,
                           arity, FStar_Pervasives_Native.None)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____2801))
                 | FStar_Pervasives_Native.Some uu____2944 ->
                     (debug1
                        (fun uu____2950  ->
                           let uu____2951 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____2951);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____2956 ->
                     (debug1
                        (fun uu____2964  ->
                           let uu____2965 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____2965);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2973;
                        FStar_Syntax_Syntax.sigquals = uu____2974;
                        FStar_Syntax_Syntax.sigmeta = uu____2975;
                        FStar_Syntax_Syntax.sigattrs = uu____2976;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____3045  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____3053  ->
                                 let uu____3054 =
                                   let uu____3055 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3055
                                    in
                                 let uu____3056 =
                                   let uu____3057 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3057
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____3054 uu____3056);
                            debug1
                              (fun uu____3065  ->
                                 let uu____3066 =
                                   let uu____3067 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3067
                                    in
                                 let uu____3068 =
                                   let uu____3069 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3069
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____3066 uu____3068);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____3070 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____3078;
                        FStar_Syntax_Syntax.sigquals = uu____3079;
                        FStar_Syntax_Syntax.sigmeta = uu____3080;
                        FStar_Syntax_Syntax.sigattrs = uu____3081;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____3150  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____3158  ->
                                 let uu____3159 =
                                   let uu____3160 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3160
                                    in
                                 let uu____3161 =
                                   let uu____3162 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3162
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____3159 uu____3161);
                            debug1
                              (fun uu____3170  ->
                                 let uu____3171 =
                                   let uu____3172 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3172
                                    in
                                 let uu____3173 =
                                   let uu____3174 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3174
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____3171 uu____3173);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____3175 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        | uu____3220 ->
            let uu____3223 =
              let uu____3253 =
                FStar_List.map
                  (fun uu____3278  ->
                     fun _ts  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____3253,
                (FStar_List.length us), FStar_Pervasives_Native.None)
               in
            FStar_TypeChecker_NBETerm.Lam uu____3223

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
          let uu____3338 = FStar_Syntax_Util.let_rec_arity b  in
          match uu____3338 with
          | (ar,maybe_lst) ->
              let uu____3357 =
                match maybe_lst with
                | FStar_Pervasives_Native.None  ->
                    let uu____3372 =
                      FStar_Common.tabulate ar (fun uu____3376  -> true)  in
                    (ar, uu____3372)
                | FStar_Pervasives_Native.Some lst ->
                    let l = trim lst  in ((FStar_List.length l), l)
                 in
              (match uu____3357 with
               | (ar1,ar_lst) ->
                   FStar_TypeChecker_NBETerm.Rec
                     (b, bs, env, [], ar1, ar_lst, callback))

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
              let uu____3487 =
                let uu____3490 = mkRec' callback lb lbs0 bs0  in uu____3490
                  :: bs1
                 in
              aux lbs' lbs0 uu____3487 bs0
           in
        aux lbs lbs bs bs

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____3504 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____3504
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____3510 ->
        let uu____3511 =
          let uu____3512 =
            let uu____3513 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____3513 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____3512  in
        failwith uu____3511

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
          (fun uu____3534  ->
             let uu____3535 =
               let uu____3536 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____3536  in
             let uu____3537 =
               let uu____3538 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____3538  in
             FStar_Util.print2 "Term: %s - %s\n" uu____3535 uu____3537);
        debug1
          (fun uu____3544  ->
             let uu____3545 =
               let uu____3546 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____3546  in
             FStar_Util.print1 "BS list: %s\n" uu____3545);
        (let uu____3551 =
           let uu____3552 = FStar_Syntax_Subst.compress e  in
           uu____3552.FStar_Syntax_Syntax.n  in
         match uu____3551 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____3555,uu____3556) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3594 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3594
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then FStar_List.nth bs db.FStar_Syntax_Syntax.index
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3610  ->
                   let uu____3611 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3612 =
                     let uu____3613 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3613
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____3611 uu____3612);
              (let uu____3618 = translate cfg bs t  in
               let uu____3619 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3623 =
                        let uu____3624 = translate_univ bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____3624  in
                      FStar_TypeChecker_NBETerm.as_arg uu____3623) us
                  in
               iapp cfg uu____3618 uu____3619))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3626 = translate_univ bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____3626
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____3649 =
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
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____3670)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____3649
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____3809  ->
                     let uu____3810 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____3810)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3812,uu____3813) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____3874,uu____3875) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             let uu____3925 =
               let uu____3955 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____4025 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____4025, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               let uu____4054 =
                 FStar_Util.map_opt resc
                   (fun c  ->
                      fun uu____4066  -> translate_residual_comp cfg bs c)
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____3955, (FStar_List.length xs), uu____4054)
                in
             FStar_TypeChecker_NBETerm.Lam uu____3925
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____4099;
                FStar_Syntax_Syntax.vars = uu____4100;_},arg::more::args)
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let uu____4160 = FStar_Syntax_Util.head_and_args e  in
             (match uu____4160 with
              | (reifyh,uu____4178) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app reifyh [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____4222 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____4222)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____4231;
                FStar_Syntax_Syntax.vars = uu____4232;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___254_4274 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___254_4274.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___254_4274.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___254_4274.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___254_4274.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___254_4274.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___254_4274.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___254_4274.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___254_4274.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____4312  ->
                   let uu____4313 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____4314 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____4313
                     uu____4314);
              (let uu____4315 = translate cfg bs head1  in
               let uu____4316 =
                 FStar_List.map
                   (fun x  ->
                      let uu____4338 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____4338, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____4315 uu____4316))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches readback1 =
               let cfg1 =
                 let uu___255_4399 = cfg  in
                 {
                   FStar_TypeChecker_Cfg.steps =
                     (let uu___256_4402 = cfg.FStar_TypeChecker_Cfg.steps  in
                      {
                        FStar_TypeChecker_Cfg.beta =
                          (uu___256_4402.FStar_TypeChecker_Cfg.beta);
                        FStar_TypeChecker_Cfg.iota =
                          (uu___256_4402.FStar_TypeChecker_Cfg.iota);
                        FStar_TypeChecker_Cfg.zeta = false;
                        FStar_TypeChecker_Cfg.weak =
                          (uu___256_4402.FStar_TypeChecker_Cfg.weak);
                        FStar_TypeChecker_Cfg.hnf =
                          (uu___256_4402.FStar_TypeChecker_Cfg.hnf);
                        FStar_TypeChecker_Cfg.primops =
                          (uu___256_4402.FStar_TypeChecker_Cfg.primops);
                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                          (uu___256_4402.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                        FStar_TypeChecker_Cfg.unfold_until =
                          (uu___256_4402.FStar_TypeChecker_Cfg.unfold_until);
                        FStar_TypeChecker_Cfg.unfold_only =
                          (uu___256_4402.FStar_TypeChecker_Cfg.unfold_only);
                        FStar_TypeChecker_Cfg.unfold_fully =
                          (uu___256_4402.FStar_TypeChecker_Cfg.unfold_fully);
                        FStar_TypeChecker_Cfg.unfold_attr =
                          (uu___256_4402.FStar_TypeChecker_Cfg.unfold_attr);
                        FStar_TypeChecker_Cfg.unfold_tac =
                          (uu___256_4402.FStar_TypeChecker_Cfg.unfold_tac);
                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                          =
                          (uu___256_4402.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                        FStar_TypeChecker_Cfg.simplify =
                          (uu___256_4402.FStar_TypeChecker_Cfg.simplify);
                        FStar_TypeChecker_Cfg.erase_universes =
                          (uu___256_4402.FStar_TypeChecker_Cfg.erase_universes);
                        FStar_TypeChecker_Cfg.allow_unbound_universes =
                          (uu___256_4402.FStar_TypeChecker_Cfg.allow_unbound_universes);
                        FStar_TypeChecker_Cfg.reify_ =
                          (uu___256_4402.FStar_TypeChecker_Cfg.reify_);
                        FStar_TypeChecker_Cfg.compress_uvars =
                          (uu___256_4402.FStar_TypeChecker_Cfg.compress_uvars);
                        FStar_TypeChecker_Cfg.no_full_norm =
                          (uu___256_4402.FStar_TypeChecker_Cfg.no_full_norm);
                        FStar_TypeChecker_Cfg.check_no_uvars =
                          (uu___256_4402.FStar_TypeChecker_Cfg.check_no_uvars);
                        FStar_TypeChecker_Cfg.unmeta =
                          (uu___256_4402.FStar_TypeChecker_Cfg.unmeta);
                        FStar_TypeChecker_Cfg.unascribe =
                          (uu___256_4402.FStar_TypeChecker_Cfg.unascribe);
                        FStar_TypeChecker_Cfg.in_full_norm_request =
                          (uu___256_4402.FStar_TypeChecker_Cfg.in_full_norm_request);
                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                          (uu___256_4402.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                        FStar_TypeChecker_Cfg.nbe_step =
                          (uu___256_4402.FStar_TypeChecker_Cfg.nbe_step)
                      });
                   FStar_TypeChecker_Cfg.tcenv =
                     (uu___255_4399.FStar_TypeChecker_Cfg.tcenv);
                   FStar_TypeChecker_Cfg.debug =
                     (uu___255_4399.FStar_TypeChecker_Cfg.debug);
                   FStar_TypeChecker_Cfg.delta_level =
                     (uu___255_4399.FStar_TypeChecker_Cfg.delta_level);
                   FStar_TypeChecker_Cfg.primitive_steps =
                     (uu___255_4399.FStar_TypeChecker_Cfg.primitive_steps);
                   FStar_TypeChecker_Cfg.strong =
                     (uu___255_4399.FStar_TypeChecker_Cfg.strong);
                   FStar_TypeChecker_Cfg.memoize_lazy =
                     (uu___255_4399.FStar_TypeChecker_Cfg.memoize_lazy);
                   FStar_TypeChecker_Cfg.normalize_pure_lets =
                     (uu___255_4399.FStar_TypeChecker_Cfg.normalize_pure_lets);
                   FStar_TypeChecker_Cfg.reifying =
                     (uu___255_4399.FStar_TypeChecker_Cfg.reifying)
                 }  in
               let rec process_pattern bs1 p =
                 let uu____4430 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____4464 =
                         FStar_List.fold_left
                           (fun uu____4502  ->
                              fun uu____4503  ->
                                match (uu____4502, uu____4503) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____4584 = process_pattern bs2 arg
                                       in
                                    (match uu____4584 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____4464 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____4673 =
                           let uu____4674 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4674  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4673
                          in
                       let uu____4675 =
                         let uu____4678 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4678 :: bs1  in
                       (uu____4675, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____4683 =
                           let uu____4684 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4684  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4683
                          in
                       let uu____4685 =
                         let uu____4688 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4688 :: bs1  in
                       (uu____4685, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____4698 =
                           let uu____4699 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4699  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4698
                          in
                       let uu____4700 =
                         let uu____4701 =
                           let uu____4708 =
                             let uu____4711 = translate cfg1 bs1 tm  in
                             readback1 uu____4711  in
                           (x, uu____4708)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____4701  in
                       (bs1, uu____4700)
                    in
                 match uu____4430 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___257_4731 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___257_4731.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____4750  ->
                    match uu____4750 with
                    | (pat,when_clause,e1) ->
                        let uu____4772 = process_pattern bs pat  in
                        (match uu____4772 with
                         | (bs',pat') ->
                             let uu____4785 =
                               let uu____4786 =
                                 let uu____4789 = translate cfg1 bs' e1  in
                                 readback1 uu____4789  in
                               (pat', when_clause, uu____4786)  in
                             FStar_Syntax_Util.branch uu____4785)) branches
                in
             let rec case scrut1 =
               debug1
                 (fun uu____4809  ->
                    let uu____4810 =
                      let uu____4811 = readback cfg scrut1  in
                      FStar_Syntax_Print.term_to_string uu____4811  in
                    FStar_Util.print1 "Match case: (%s)\n" uu____4810);
               (match scrut1 with
                | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                    (debug1
                       (fun uu____4836  ->
                          let uu____4837 =
                            let uu____4838 =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____4861  ->
                                      match uu____4861 with
                                      | (x,q) ->
                                          let uu____4874 =
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              x
                                             in
                                          Prims.strcat
                                            (if FStar_Util.is_some q
                                             then "#"
                                             else "") uu____4874))
                               in
                            FStar_All.pipe_right uu____4838
                              (FStar_String.concat "; ")
                             in
                          FStar_Util.print1 "Match args: %s\n" uu____4837);
                     (let uu____4878 = pickBranch cfg scrut1 branches  in
                      match uu____4878 with
                      | FStar_Pervasives_Native.Some (branch1,args1) ->
                          let uu____4899 =
                            FStar_List.fold_left
                              (fun bs1  -> fun x  -> x :: bs1) bs args1
                             in
                          translate cfg uu____4899 branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                            make_branches))
                | FStar_TypeChecker_NBETerm.Constant c ->
                    (debug1
                       (fun uu____4922  ->
                          let uu____4923 =
                            FStar_TypeChecker_NBETerm.t_to_string scrut1  in
                          FStar_Util.print1 "Match constant : %s\n"
                            uu____4923);
                     (let uu____4924 = pickBranch cfg scrut1 branches  in
                      match uu____4924 with
                      | FStar_Pervasives_Native.Some (branch1,[]) ->
                          translate cfg bs branch1
                      | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                          translate cfg (arg :: bs) branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                            make_branches
                      | FStar_Pervasives_Native.Some (uu____4958,hd1::tl1) ->
                          failwith
                            "Impossible: Matching on constants cannot bind more than one variable"))
                | uu____4971 ->
                    FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                      make_branches)
                in
             let uu____4972 = translate cfg bs scrut  in case uu____4972
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
             let uu____5045 = make_rec_env (translate_letbinding cfg) lbs bs
                in
             translate cfg uu____5045 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____5049) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____5070  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____5081 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____5096  ->
                      match uu____5096 with
                      | (bv,t1) ->
                          let uu____5103 =
                            let uu____5110 = readback cfg t1  in
                            (bv, uu____5110)  in
                          FStar_Syntax_Syntax.NT uu____5103) uu____5081
                  in
               let uu____5115 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____5115  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close1 qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close1 qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li))

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
            let uu____5142 =
              let uu____5149 = translate cfg bs typ  in
              let uu____5150 = fmap_opt (translate_univ bs) u  in
              (uu____5149, uu____5150)  in
            FStar_TypeChecker_NBETerm.Tot uu____5142
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____5165 =
              let uu____5172 = translate cfg bs typ  in
              let uu____5173 = fmap_opt (translate_univ bs) u  in
              (uu____5172, uu____5173)  in
            FStar_TypeChecker_NBETerm.GTot uu____5165
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____5179 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____5179

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____5189 =
              let uu____5198 = readback cfg typ  in (uu____5198, u)  in
            FStar_Syntax_Syntax.Total uu____5189
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____5211 =
              let uu____5220 = readback cfg typ  in (uu____5220, u)  in
            FStar_Syntax_Syntax.GTotal uu____5211
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____5228 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____5228
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
        let uu____5234 = c  in
        match uu____5234 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags1;_} ->
            let uu____5254 = FStar_List.map (translate_univ bs) comp_univs
               in
            let uu____5255 = translate cfg bs result_typ  in
            let uu____5256 =
              FStar_List.map
                (fun x  ->
                   let uu____5284 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____5284, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____5291 = FStar_List.map (translate_flag cfg bs) flags1
               in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____5254;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____5255;
              FStar_TypeChecker_NBETerm.effect_args = uu____5256;
              FStar_TypeChecker_NBETerm.flags = uu____5291
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____5296 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____5299 =
        FStar_List.map
          (fun x  ->
             let uu____5325 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____5325, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____5326 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____5296;
        FStar_Syntax_Syntax.effect_args = uu____5299;
        FStar_Syntax_Syntax.flags = uu____5326
      }

and (translate_residual_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.residual_comp ->
        FStar_TypeChecker_NBETerm.residual_comp)
  =
  fun cfg  ->
    fun bs  ->
      fun c  ->
        let uu____5334 = c  in
        match uu____5334 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____5344 =
              FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____5349 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____5344;
              FStar_TypeChecker_NBETerm.residual_flags = uu____5349
            }

and (readback_residual_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____5354 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (readback cfg)
         in
      let uu____5361 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____5354;
        FStar_Syntax_Syntax.residual_flags = uu____5361
      }

and (translate_flag :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.cflags -> FStar_TypeChecker_NBETerm.cflags)
  =
  fun cfg  ->
    fun bs  ->
      fun f  ->
        match f with
        | FStar_Syntax_Syntax.TOTAL  -> FStar_TypeChecker_NBETerm.TOTAL
        | FStar_Syntax_Syntax.MLEFFECT  -> FStar_TypeChecker_NBETerm.MLEFFECT
        | FStar_Syntax_Syntax.RETURN  -> FStar_TypeChecker_NBETerm.RETURN
        | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
            FStar_TypeChecker_NBETerm.PARTIAL_RETURN
        | FStar_Syntax_Syntax.SOMETRIVIAL  ->
            FStar_TypeChecker_NBETerm.SOMETRIVIAL
        | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  ->
            FStar_TypeChecker_NBETerm.TRIVIAL_POSTCONDITION
        | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
            FStar_TypeChecker_NBETerm.SHOULD_NOT_INLINE
        | FStar_Syntax_Syntax.LEMMA  -> FStar_TypeChecker_NBETerm.LEMMA
        | FStar_Syntax_Syntax.CPS  -> FStar_TypeChecker_NBETerm.CPS
        | FStar_Syntax_Syntax.DECREASES tm ->
            let uu____5372 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____5372

and (readback_flag :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.cflags -> FStar_Syntax_Syntax.cflags)
  =
  fun cfg  ->
    fun f  ->
      match f with
      | FStar_TypeChecker_NBETerm.TOTAL  -> FStar_Syntax_Syntax.TOTAL
      | FStar_TypeChecker_NBETerm.MLEFFECT  -> FStar_Syntax_Syntax.MLEFFECT
      | FStar_TypeChecker_NBETerm.RETURN  -> FStar_Syntax_Syntax.RETURN
      | FStar_TypeChecker_NBETerm.PARTIAL_RETURN  ->
          FStar_Syntax_Syntax.PARTIAL_RETURN
      | FStar_TypeChecker_NBETerm.SOMETRIVIAL  ->
          FStar_Syntax_Syntax.SOMETRIVIAL
      | FStar_TypeChecker_NBETerm.TRIVIAL_POSTCONDITION  ->
          FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION
      | FStar_TypeChecker_NBETerm.SHOULD_NOT_INLINE  ->
          FStar_Syntax_Syntax.SHOULD_NOT_INLINE
      | FStar_TypeChecker_NBETerm.LEMMA  -> FStar_Syntax_Syntax.LEMMA
      | FStar_TypeChecker_NBETerm.CPS  -> FStar_Syntax_Syntax.CPS
      | FStar_TypeChecker_NBETerm.DECREASES t ->
          let uu____5376 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____5376

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____5379  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____5379 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____5414 =
                     let uu____5423 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____5423
                      in
                   (match uu____5414 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5430 =
                          let uu____5431 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____5431
                           in
                        failwith uu____5430
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___258_5445 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___258_5445.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___258_5445.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___258_5445.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___258_5445.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___258_5445.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___258_5445.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___258_5445.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___258_5445.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____5452 =
                            let uu____5459 =
                              let uu____5460 =
                                let uu____5479 =
                                  let uu____5488 =
                                    let uu____5495 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____5495,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____5488]  in
                                (uu____5479, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____5460  in
                            FStar_Syntax_Syntax.mk uu____5459  in
                          uu____5452 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____5532 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____5532
                          then
                            let uu____5539 =
                              let uu____5544 =
                                let uu____5545 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____5545  in
                              (uu____5544, FStar_Pervasives_Native.None)  in
                            let uu____5546 =
                              let uu____5553 =
                                let uu____5558 =
                                  let uu____5559 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____5559  in
                                (uu____5558, FStar_Pervasives_Native.None)
                                 in
                              [uu____5553]  in
                            uu____5539 :: uu____5546
                          else []  in
                        let t =
                          let uu____5578 =
                            let uu____5579 =
                              let uu____5580 =
                                FStar_Syntax_Util.un_uinst
                                  (FStar_Pervasives_Native.snd
                                     ed.FStar_Syntax_Syntax.bind_repr)
                                 in
                              translate cfg' [] uu____5580  in
                            iapp cfg uu____5579
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____5597 =
                            let uu____5598 =
                              let uu____5605 =
                                let uu____5610 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____5610, FStar_Pervasives_Native.None)
                                 in
                              let uu____5611 =
                                let uu____5618 =
                                  let uu____5623 = translate cfg' bs ty  in
                                  (uu____5623, FStar_Pervasives_Native.None)
                                   in
                                [uu____5618]  in
                              uu____5605 :: uu____5611  in
                            let uu____5636 =
                              let uu____5643 =
                                let uu____5650 =
                                  let uu____5657 =
                                    let uu____5662 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____5662,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____5663 =
                                    let uu____5670 =
                                      let uu____5677 =
                                        let uu____5682 =
                                          translate cfg bs body_lam  in
                                        (uu____5682,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____5677]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____5670
                                     in
                                  uu____5657 :: uu____5663  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____5650
                                 in
                              FStar_List.append maybe_range_arg uu____5643
                               in
                            FStar_List.append uu____5598 uu____5636  in
                          iapp cfg uu____5578 uu____5597  in
                        (debug cfg
                           (fun uu____5714  ->
                              let uu____5715 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____5715);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____5716);
                      FStar_Syntax_Syntax.pos = uu____5717;
                      FStar_Syntax_Syntax.vars = uu____5718;_},(e2,uu____5720)::[])
                   ->
                   translate
                     (let uu___259_5761 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___259_5761.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___259_5761.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___259_5761.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___259_5761.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___259_5761.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___259_5761.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___259_5761.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___259_5761.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app uu____5762 -> translate cfg bs e1
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____5899  ->
                             match uu____5899 with
                             | (pat,wopt,tm) ->
                                 let uu____5947 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____5947)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   translate
                     (let uu___260_5981 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___260_5981.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___260_5981.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___260_5981.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___260_5981.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___260_5981.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___260_5981.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___260_5981.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___260_5981.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs tm
               | uu____5982 ->
                   let uu____5983 =
                     let uu____5984 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____5984
                      in
                   failwith uu____5983)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____5985  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____5985 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____6009 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____6009
              then
                let ed =
                  let uu____6011 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____6011
                   in
                let cfg' =
                  let uu___261_6013 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___261_6013.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___261_6013.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___261_6013.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___261_6013.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___261_6013.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___261_6013.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___261_6013.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___261_6013.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let t =
                  let uu____6015 =
                    let uu____6016 =
                      let uu____6017 =
                        FStar_Syntax_Util.un_uinst
                          (FStar_Pervasives_Native.snd
                             ed.FStar_Syntax_Syntax.return_repr)
                         in
                      translate cfg' [] uu____6017  in
                    iapp cfg uu____6016
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____6030 =
                    let uu____6031 =
                      let uu____6036 = translate cfg' bs ty  in
                      (uu____6036, FStar_Pervasives_Native.None)  in
                    let uu____6037 =
                      let uu____6044 =
                        let uu____6049 = translate cfg' bs e1  in
                        (uu____6049, FStar_Pervasives_Native.None)  in
                      [uu____6044]  in
                    uu____6031 :: uu____6037  in
                  iapp cfg uu____6015 uu____6030  in
                (debug cfg
                   (fun uu____6065  ->
                      let uu____6066 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____6066);
                 t)
              else
                (let uu____6068 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____6068 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____6071 =
                       let uu____6072 = FStar_Ident.text_of_lid msrc  in
                       let uu____6073 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____6072 uu____6073
                        in
                     failwith uu____6071
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____6074;
                       FStar_TypeChecker_Env.mtarget = uu____6075;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____6076;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____6098 =
                       let uu____6099 = FStar_Ident.text_of_lid msrc  in
                       let uu____6100 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____6099 uu____6100
                        in
                     failwith uu____6098
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____6101;
                       FStar_TypeChecker_Env.mtarget = uu____6102;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____6103;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____6142 =
                         let uu____6145 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____6145
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____6142
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___262_6161 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___262_6161.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___262_6161.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___262_6161.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___262_6161.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___262_6161.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___262_6161.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___262_6161.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___262_6161.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let t =
                       let uu____6163 = translate cfg' [] lift_lam  in
                       let uu____6164 =
                         let uu____6165 =
                           let uu____6170 = translate cfg bs e1  in
                           (uu____6170, FStar_Pervasives_Native.None)  in
                         [uu____6165]  in
                       iapp cfg uu____6163 uu____6164  in
                     (debug cfg
                        (fun uu____6182  ->
                           let uu____6183 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____6183);
                      t))

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____6199  ->
           let uu____6200 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____6200);
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
           let uu____6203 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____6203 FStar_Syntax_Util.exp_int
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
       | FStar_TypeChecker_NBETerm.Lam (f,targs,arity,resc) ->
           let uu____6256 =
             FStar_List.fold_left
               (fun uu____6299  ->
                  fun tf  ->
                    match uu____6299 with
                    | (args_rev,accus_rev) ->
                        let uu____6351 = tf accus_rev  in
                        (match uu____6351 with
                         | (xt,q) ->
                             let x1 =
                               let uu____6371 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____6371
                                in
                             let uu____6372 =
                               let uu____6375 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____6375 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____6372))) ([], [])
               targs
              in
           (match uu____6256 with
            | (args_rev,accus_rev) ->
                let body =
                  let uu____6419 = f (FStar_List.rev accus_rev)  in
                  readback cfg uu____6419  in
                let uu____6420 =
                  FStar_Util.map_opt resc
                    (fun thunk  ->
                       let uu____6431 = thunk ()  in
                       readback_residual_comp cfg uu____6431)
                   in
                FStar_Syntax_Util.abs (FStar_List.rev args_rev) body
                  uu____6420)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____6459 =
               let uu____6460 =
                 let uu____6461 = targ ()  in
                 FStar_Pervasives_Native.fst uu____6461  in
               readback cfg uu____6460  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____6459
              in
           let body =
             let uu____6467 =
               let uu____6468 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____6468  in
             readback cfg uu____6467  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____6503 =
             FStar_List.fold_left
               (fun uu____6546  ->
                  fun tf  ->
                    match uu____6546 with
                    | (args_rev,accus_rev) ->
                        let uu____6598 = tf accus_rev  in
                        (match uu____6598 with
                         | (xt,q) ->
                             let x1 =
                               let uu____6618 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____6618
                                in
                             let uu____6619 =
                               let uu____6622 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____6622 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____6619))) ([], [])
               targs
              in
           (match uu____6503 with
            | (args_rev,accus_rev) ->
                let cmp =
                  let uu____6666 = f (FStar_List.rev accus_rev)  in
                  readback_comp cfg uu____6666  in
                FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____6709  ->
                  match uu____6709 with
                  | (x1,q) ->
                      let uu____6720 = readback cfg x1  in (uu____6720, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____6739 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____6746::uu____6747 ->
                let uu____6750 =
                  let uu____6753 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____6753
                    (FStar_List.rev us)
                   in
                apply uu____6750
            | [] ->
                let uu____6754 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____6754)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____6795  ->
                  match uu____6795 with
                  | (x1,q) ->
                      let uu____6806 = readback cfg x1  in (uu____6806, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____6825 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____6832::uu____6833 ->
                let uu____6836 =
                  let uu____6839 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____6839
                    (FStar_List.rev us)
                   in
                apply uu____6836
            | [] ->
                let uu____6840 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____6840)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____6887  ->
                  match uu____6887 with
                  | (x1,q) ->
                      let uu____6898 = readback cfg x1  in (uu____6898, q))
               ts
              in
           let uu____6899 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____6899 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____6959  ->
                  match uu____6959 with
                  | (x1,q) ->
                      let uu____6970 = readback cfg x1  in (uu____6970, q))
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
            | uu____7000 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs,args,_ar,_ar_lst,_cfg) ->
           let head1 =
             match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inl bv ->
                 failwith
                   "Reading back of local recursive definitions is not supported yet."
             | FStar_Util.Inr fv ->
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                   FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 =
             map_rev
               (fun uu____7082  ->
                  match uu____7082 with
                  | (x1,q) ->
                      let uu____7093 = readback cfg x1  in (uu____7093, q))
               args
              in
           (match args1 with
            | [] -> head1
            | uu____7098 -> FStar_Syntax_Util.mk_app head1 args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inr
           (uu____7118,uu____7119,thunk)) ->
           let uu____7133 = FStar_Common.force_thunk thunk  in
           readback cfg uu____7133)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____7196 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____7203 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____7219 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____7239 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____7252 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____7258 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___253_7263  ->
    match uu___253_7263 with
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
            let uu___263_7299 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___264_7302 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___264_7302.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___264_7302.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___264_7302.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___264_7302.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___264_7302.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___264_7302.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___264_7302.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___264_7302.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___264_7302.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___264_7302.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___264_7302.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___264_7302.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___264_7302.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___264_7302.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___264_7302.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___264_7302.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___264_7302.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___264_7302.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___264_7302.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___264_7302.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___264_7302.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___264_7302.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___264_7302.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___264_7302.FStar_TypeChecker_Cfg.nbe_step)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___263_7299.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___263_7299.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___263_7299.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___263_7299.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___263_7299.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___263_7299.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___263_7299.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___263_7299.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____7306  ->
               let uu____7307 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with %s" uu____7307);
          (let uu____7308 = translate cfg1 [] e  in readback cfg1 uu____7308)
  
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
          let uu___265_7330 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___266_7333 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___266_7333.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___266_7333.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___266_7333.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___266_7333.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___266_7333.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___266_7333.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___266_7333.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___266_7333.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___266_7333.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___266_7333.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___266_7333.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___266_7333.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___266_7333.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___266_7333.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___266_7333.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___266_7333.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___266_7333.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___266_7333.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___266_7333.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___266_7333.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___266_7333.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___266_7333.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___266_7333.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___266_7333.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___265_7330.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___265_7330.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___265_7330.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___265_7330.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___265_7330.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___265_7330.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___265_7330.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___265_7330.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____7337  ->
             let uu____7338 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____7338);
        (let r =
           let uu____7340 = translate cfg1 [] e  in readback cfg1 uu____7340
            in
         debug cfg1
           (fun uu____7344  ->
              let uu____7345 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "NBE returned %s" uu____7345);
         r)
  