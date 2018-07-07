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
  
let rec (unlazy : FStar_TypeChecker_NBETerm.t -> FStar_TypeChecker_NBETerm.t)
  =
  fun t  ->
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (uu____395,t1) ->
        let uu____417 = FStar_Common.force_thunk t1  in unlazy uu____417
    | t1 -> t1
  
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
          let rec matches_pat scrutinee0 p =
            let scrutinee = unlazy scrutinee0  in
            debug cfg
              (fun uu____562  ->
                 let uu____563 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                 let uu____564 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____563
                   uu____564);
            (let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____584 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____609  ->
                          let uu____610 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____611 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu____610
                            uu____611);
                     (match c with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____614 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____627 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____627
                           | uu____628 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____630))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____632) ->
                               st = p1
                           | uu____633 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____639 -> false)
                      | uu____640 -> false)
                      in
                   let uu____641 = matches_const scrutinee s  in
                   if uu____641
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____762)::rest_a,(p2,uu____765)::rest_p) ->
                         let uu____799 = matches_pat t p2  in
                         (match uu____799 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____824 -> FStar_Util.Inr false  in
                   (match scrutinee with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____868 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                        if uu____868
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____882 -> FStar_Util.Inr true)
                in
             let res_to_string uu___252_896 =
               match uu___252_896 with
               | FStar_Util.Inr b ->
                   let uu____906 = FStar_Util.string_of_bool b  in
                   Prims.strcat "Inr " uu____906
               | FStar_Util.Inl bs ->
                   let uu____912 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.strcat "Inl " uu____912
                in
             debug cfg
               (fun uu____918  ->
                  let uu____919 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____920 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____921 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____919
                    uu____920 uu____921);
             r)
             in
          match branches1 with
          | [] -> failwith "Branch not found"
          | (p,_wopt,e)::branches2 ->
              let uu____960 = matches_pat scrut1 p  in
              (match uu____960 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____983  ->
                         let uu____984 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____984);
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
        | (uu____1134,[]) -> (true, (FStar_List.rev acc), ts1)
        | ([],uu____1165::uu____1166) -> (false, (FStar_List.rev acc), [])
        | (t::ts2,b::bs) ->
            let uu____1229 =
              res &&
                (let uu____1231 =
                   let uu____1232 =
                     FStar_TypeChecker_NBETerm.isAccu
                       (FStar_Pervasives_Native.fst t)
                      in
                   Prims.op_Negation uu____1232  in
                 implies b uu____1231)
               in
            aux ts2 bs (t :: acc) uu____1229
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
        let mapper uu____1285 =
          match uu____1285 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1368  ->
                         let uu____1369 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1369);
                    FStar_Pervasives_Native.Some elt)
               | uu____1370 -> FStar_Pervasives_Native.None)
           in
        let uu____1385 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1385 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1429 -> true
    | uu____1430 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | t ->
        let uu____1438 =
          let uu____1439 = FStar_TypeChecker_NBETerm.t_to_string t  in
          Prims.strcat "Not a universe: " uu____1439  in
        failwith uu____1438
  
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
              (uu____1452,uu____1453,uu____1454,uu____1455,uu____1456,uu____1457);
            FStar_Syntax_Syntax.sigrng = uu____1458;
            FStar_Syntax_Syntax.sigquals = uu____1459;
            FStar_Syntax_Syntax.sigmeta = uu____1460;
            FStar_Syntax_Syntax.sigattrs = uu____1461;_},uu____1462),uu____1463)
        -> true
    | uu____1518 -> false
  
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
            let uu____1544 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1544
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1548 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1548
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____1551 -> u2
        | FStar_Syntax_Syntax.U_unif uu____1552 -> u2
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
           | FStar_Util.Inl uu____1582 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1586 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1586
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
              let uu____1932 = FStar_List.splitAt m targs  in
              (match uu____1932 with
               | (uu____1972,targs') ->
                   let targs'1 =
                     FStar_List.map
                       (fun targ  ->
                          fun l  ->
                            let uu____2063 =
                              let uu____2066 =
                                map_append FStar_Pervasives_Native.fst args l
                                 in
                              FStar_List.rev uu____2066  in
                            targ uu____2063) targs'
                      in
                   FStar_TypeChecker_NBETerm.Lam
                     (((fun l  ->
                          let uu____2099 =
                            map_append FStar_Pervasives_Native.fst args l  in
                          f1 uu____2099)), targs'1, (n1 - m), res))
            else
              if m = n1
              then
                (let uu____2115 =
                   FStar_List.map FStar_Pervasives_Native.fst args  in
                 f1 uu____2115)
              else
                (let uu____2123 = FStar_List.splitAt n1 args  in
                 match uu____2123 with
                 | (args1,args') ->
                     let uu____2170 =
                       let uu____2171 =
                         FStar_List.map FStar_Pervasives_Native.fst args1  in
                       f1 uu____2171  in
                     iapp cfg uu____2170 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____2290)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____2334 = aux args us ts  in
            (match uu____2334 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____2461)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____2505 = aux args us ts  in
            (match uu____2505 with
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
                 let uu____2665 = test_args full_args ar_lst  in
                 match uu____2665 with
                 | (can_unfold,args1,res) ->
                     if
                       Prims.op_Negation
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                     then
                       (debug cfg
                          (fun uu____2678  ->
                             let uu____2679 =
                               FStar_Syntax_Print.lbname_to_string
                                 lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Util.print1
                               "Zeta is not set; will not unfold %s\n"
                               uu____2679);
                        FStar_TypeChecker_NBETerm.Rec
                          (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                            ar_lst, tr_lb))
                     else
                       if can_unfold
                       then
                         (debug cfg
                            (fun uu____2704  ->
                               let uu____2705 =
                                 FStar_Syntax_Print.lbname_to_string
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               FStar_Util.print1
                                 "Beta reducing recursive function %s\n"
                                 uu____2705);
                          (match res with
                           | [] ->
                               let uu____2710 =
                                 let uu____2711 = make_rec_env tr_lb lbs bs
                                    in
                                 tr_lb uu____2711 lb  in
                               iapp cfg uu____2710 args1
                           | uu____2714::uu____2715 ->
                               let t =
                                 let uu____2731 =
                                   let uu____2732 = make_rec_env tr_lb lbs bs
                                      in
                                   tr_lb uu____2732 lb  in
                                 iapp cfg uu____2731 args1  in
                               iapp cfg t res))
                       else
                         FStar_TypeChecker_NBETerm.Rec
                           (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                             ar_lst, tr_lb))
        | FStar_TypeChecker_NBETerm.Quote uu____2756 ->
            let uu____2761 =
              let uu____2762 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2762  in
            failwith uu____2761
        | FStar_TypeChecker_NBETerm.Reflect uu____2763 ->
            let uu____2764 =
              let uu____2765 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2765  in
            failwith uu____2764
        | FStar_TypeChecker_NBETerm.Lazy uu____2766 ->
            let uu____2781 =
              let uu____2782 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2782  in
            failwith uu____2781
        | FStar_TypeChecker_NBETerm.Constant uu____2783 ->
            let uu____2784 =
              let uu____2785 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2785  in
            failwith uu____2784
        | FStar_TypeChecker_NBETerm.Univ uu____2786 ->
            let uu____2787 =
              let uu____2788 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2788  in
            failwith uu____2787
        | FStar_TypeChecker_NBETerm.Type_t uu____2789 ->
            let uu____2790 =
              let uu____2791 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2791  in
            failwith uu____2790
        | FStar_TypeChecker_NBETerm.Unknown  ->
            let uu____2792 =
              let uu____2793 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2793  in
            failwith uu____2792
        | FStar_TypeChecker_NBETerm.Refinement uu____2794 ->
            let uu____2809 =
              let uu____2810 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2810  in
            failwith uu____2809
        | FStar_TypeChecker_NBETerm.Arrow uu____2811 ->
            let uu____2832 =
              let uu____2833 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2833  in
            failwith uu____2832

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
          let uu____2848 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2849 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2848 uu____2849  in
        let uu____2850 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2850
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2856 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2858  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2856 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2864  ->
                     let uu____2865 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2865);
                (let uu____2866 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____2866 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____2876  ->
                           let uu____2877 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n" uu____2877);
                      (let uu____2878 =
                         let uu____2908 =
                           let f uu____2935 uu____2936 =
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
                             let callbacks =
                               {
                                 FStar_TypeChecker_NBETerm.iapp = (iapp cfg);
                                 FStar_TypeChecker_NBETerm.translate =
                                   (translate cfg bs)
                               }  in
                             let uu____2994 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 callbacks args'
                                in
                             match uu____2994 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____3005  ->
                                       let uu____3006 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____3007 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____3006 uu____3007);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____3013  ->
                                       let uu____3014 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____3014);
                                  (let uu____3015 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp cfg uu____3015 args'))), uu____2908,
                           arity, FStar_Pervasives_Native.None)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____2878))
                 | FStar_Pervasives_Native.Some uu____3023 ->
                     (debug1
                        (fun uu____3029  ->
                           let uu____3030 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____3030);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____3035 ->
                     (debug1
                        (fun uu____3043  ->
                           let uu____3044 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____3044);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____3052;
                        FStar_Syntax_Syntax.sigquals = uu____3053;
                        FStar_Syntax_Syntax.sigmeta = uu____3054;
                        FStar_Syntax_Syntax.sigattrs = uu____3055;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____3124  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____3132  ->
                                 let uu____3133 =
                                   let uu____3134 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3134
                                    in
                                 let uu____3135 =
                                   let uu____3136 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3136
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____3133 uu____3135);
                            debug1
                              (fun uu____3144  ->
                                 let uu____3145 =
                                   let uu____3146 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3146
                                    in
                                 let uu____3147 =
                                   let uu____3148 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3148
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____3145 uu____3147);
                            translate_letbinding cfg bs lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____3149 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____3157;
                        FStar_Syntax_Syntax.sigquals = uu____3158;
                        FStar_Syntax_Syntax.sigmeta = uu____3159;
                        FStar_Syntax_Syntax.sigattrs = uu____3160;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____3229  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____3237  ->
                                 let uu____3238 =
                                   let uu____3239 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3239
                                    in
                                 let uu____3240 =
                                   let uu____3241 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3241
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____3238 uu____3240);
                            debug1
                              (fun uu____3249  ->
                                 let uu____3250 =
                                   let uu____3251 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3251
                                    in
                                 let uu____3252 =
                                   let uu____3253 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3253
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____3250 uu____3252);
                            translate_letbinding cfg bs lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____3254 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        | uu____3299 ->
            let uu____3302 =
              let uu____3332 =
                FStar_List.map
                  (fun uu____3357  ->
                     fun _ts  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____3332,
                (FStar_List.length us), FStar_Pervasives_Native.None)
               in
            FStar_TypeChecker_NBETerm.Lam uu____3302

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
          let uu____3417 = FStar_Syntax_Util.let_rec_arity b  in
          match uu____3417 with
          | (ar,maybe_lst) ->
              let uu____3436 =
                match maybe_lst with
                | FStar_Pervasives_Native.None  ->
                    let uu____3451 =
                      FStar_Common.tabulate ar (fun uu____3455  -> true)  in
                    (ar, uu____3451)
                | FStar_Pervasives_Native.Some lst ->
                    let l = trim lst  in ((FStar_List.length l), l)
                 in
              (match uu____3436 with
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
              let uu____3566 =
                let uu____3569 = mkRec' callback lb lbs0 bs0  in uu____3569
                  :: bs1
                 in
              aux lbs' lbs0 uu____3566 bs0
           in
        aux lbs lbs bs bs

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____3583 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____3583
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____3589 ->
        let uu____3590 =
          let uu____3591 =
            let uu____3592 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____3592 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____3591  in
        failwith uu____3590

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
          (fun uu____3613  ->
             let uu____3614 =
               let uu____3615 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____3615  in
             let uu____3616 =
               let uu____3617 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____3617  in
             FStar_Util.print2 "Term: %s - %s\n" uu____3614 uu____3616);
        debug1
          (fun uu____3623  ->
             let uu____3624 =
               let uu____3625 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____3625  in
             FStar_Util.print1 "BS list: %s\n" uu____3624);
        (let uu____3630 =
           let uu____3631 = FStar_Syntax_Subst.compress e  in
           uu____3631.FStar_Syntax_Syntax.n  in
         match uu____3630 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____3634,uu____3635) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3673 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3673
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then FStar_List.nth bs db.FStar_Syntax_Syntax.index
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3689  ->
                   let uu____3690 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3691 =
                     let uu____3692 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3692
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____3690 uu____3691);
              (let uu____3697 = translate cfg bs t  in
               let uu____3698 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3702 =
                        let uu____3703 = translate_univ bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____3703  in
                      FStar_TypeChecker_NBETerm.as_arg uu____3702) us
                  in
               iapp cfg uu____3697 uu____3698))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3705 = translate_univ bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____3705
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____3728 =
               let uu____3749 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____3819 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____3819, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____3749)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____3728
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____3888  ->
                     let uu____3889 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____3889)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3891,uu____3892) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____3953,uu____3954) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             let uu____4004 =
               let uu____4034 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____4104 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____4104, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               let uu____4133 =
                 FStar_Util.map_opt resc
                   (fun c  ->
                      fun uu____4145  -> translate_residual_comp cfg bs c)
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____4034, (FStar_List.length xs), uu____4133)
                in
             FStar_TypeChecker_NBETerm.Lam uu____4004
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____4178;
                FStar_Syntax_Syntax.vars = uu____4179;_},arg::more::args)
             ->
             let uu____4239 = FStar_Syntax_Util.head_and_args e  in
             (match uu____4239 with
              | (head1,uu____4257) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____4301 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____4301)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____4310);
                FStar_Syntax_Syntax.pos = uu____4311;
                FStar_Syntax_Syntax.vars = uu____4312;_},arg::more::args)
             ->
             let uu____4372 = FStar_Syntax_Util.head_and_args e  in
             (match uu____4372 with
              | (head1,uu____4390) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____4434 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____4434)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____4443);
                FStar_Syntax_Syntax.pos = uu____4444;
                FStar_Syntax_Syntax.vars = uu____4445;_},arg::[])
             when cfg.FStar_TypeChecker_Cfg.reifying ->
             let cfg1 =
               let uu___254_4486 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___254_4486.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___254_4486.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___254_4486.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___254_4486.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___254_4486.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___254_4486.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___254_4486.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___254_4486.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = false
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____4491);
                FStar_Syntax_Syntax.pos = uu____4492;
                FStar_Syntax_Syntax.vars = uu____4493;_},arg::[])
             ->
             let uu____4533 =
               translate cfg bs (FStar_Pervasives_Native.fst arg)  in
             FStar_TypeChecker_NBETerm.Reflect uu____4533
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____4538;
                FStar_Syntax_Syntax.vars = uu____4539;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___255_4581 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___255_4581.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___255_4581.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___255_4581.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___255_4581.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___255_4581.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___255_4581.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___255_4581.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___255_4581.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____4619  ->
                   let uu____4620 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____4621 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____4620
                     uu____4621);
              (let uu____4622 = translate cfg bs head1  in
               let uu____4623 =
                 FStar_List.map
                   (fun x  ->
                      let uu____4645 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____4645, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____4622 uu____4623))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches readback1 =
               let cfg1 =
                 let uu___256_4706 = cfg  in
                 {
                   FStar_TypeChecker_Cfg.steps =
                     (let uu___257_4709 = cfg.FStar_TypeChecker_Cfg.steps  in
                      {
                        FStar_TypeChecker_Cfg.beta =
                          (uu___257_4709.FStar_TypeChecker_Cfg.beta);
                        FStar_TypeChecker_Cfg.iota =
                          (uu___257_4709.FStar_TypeChecker_Cfg.iota);
                        FStar_TypeChecker_Cfg.zeta = false;
                        FStar_TypeChecker_Cfg.weak =
                          (uu___257_4709.FStar_TypeChecker_Cfg.weak);
                        FStar_TypeChecker_Cfg.hnf =
                          (uu___257_4709.FStar_TypeChecker_Cfg.hnf);
                        FStar_TypeChecker_Cfg.primops =
                          (uu___257_4709.FStar_TypeChecker_Cfg.primops);
                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                          (uu___257_4709.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                        FStar_TypeChecker_Cfg.unfold_until =
                          (uu___257_4709.FStar_TypeChecker_Cfg.unfold_until);
                        FStar_TypeChecker_Cfg.unfold_only =
                          (uu___257_4709.FStar_TypeChecker_Cfg.unfold_only);
                        FStar_TypeChecker_Cfg.unfold_fully =
                          (uu___257_4709.FStar_TypeChecker_Cfg.unfold_fully);
                        FStar_TypeChecker_Cfg.unfold_attr =
                          (uu___257_4709.FStar_TypeChecker_Cfg.unfold_attr);
                        FStar_TypeChecker_Cfg.unfold_tac =
                          (uu___257_4709.FStar_TypeChecker_Cfg.unfold_tac);
                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                          =
                          (uu___257_4709.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                        FStar_TypeChecker_Cfg.simplify =
                          (uu___257_4709.FStar_TypeChecker_Cfg.simplify);
                        FStar_TypeChecker_Cfg.erase_universes =
                          (uu___257_4709.FStar_TypeChecker_Cfg.erase_universes);
                        FStar_TypeChecker_Cfg.allow_unbound_universes =
                          (uu___257_4709.FStar_TypeChecker_Cfg.allow_unbound_universes);
                        FStar_TypeChecker_Cfg.reify_ =
                          (uu___257_4709.FStar_TypeChecker_Cfg.reify_);
                        FStar_TypeChecker_Cfg.compress_uvars =
                          (uu___257_4709.FStar_TypeChecker_Cfg.compress_uvars);
                        FStar_TypeChecker_Cfg.no_full_norm =
                          (uu___257_4709.FStar_TypeChecker_Cfg.no_full_norm);
                        FStar_TypeChecker_Cfg.check_no_uvars =
                          (uu___257_4709.FStar_TypeChecker_Cfg.check_no_uvars);
                        FStar_TypeChecker_Cfg.unmeta =
                          (uu___257_4709.FStar_TypeChecker_Cfg.unmeta);
                        FStar_TypeChecker_Cfg.unascribe =
                          (uu___257_4709.FStar_TypeChecker_Cfg.unascribe);
                        FStar_TypeChecker_Cfg.in_full_norm_request =
                          (uu___257_4709.FStar_TypeChecker_Cfg.in_full_norm_request);
                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                          (uu___257_4709.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                        FStar_TypeChecker_Cfg.nbe_step =
                          (uu___257_4709.FStar_TypeChecker_Cfg.nbe_step)
                      });
                   FStar_TypeChecker_Cfg.tcenv =
                     (uu___256_4706.FStar_TypeChecker_Cfg.tcenv);
                   FStar_TypeChecker_Cfg.debug =
                     (uu___256_4706.FStar_TypeChecker_Cfg.debug);
                   FStar_TypeChecker_Cfg.delta_level =
                     (uu___256_4706.FStar_TypeChecker_Cfg.delta_level);
                   FStar_TypeChecker_Cfg.primitive_steps =
                     (uu___256_4706.FStar_TypeChecker_Cfg.primitive_steps);
                   FStar_TypeChecker_Cfg.strong =
                     (uu___256_4706.FStar_TypeChecker_Cfg.strong);
                   FStar_TypeChecker_Cfg.memoize_lazy =
                     (uu___256_4706.FStar_TypeChecker_Cfg.memoize_lazy);
                   FStar_TypeChecker_Cfg.normalize_pure_lets =
                     (uu___256_4706.FStar_TypeChecker_Cfg.normalize_pure_lets);
                   FStar_TypeChecker_Cfg.reifying =
                     (uu___256_4706.FStar_TypeChecker_Cfg.reifying)
                 }  in
               let rec process_pattern bs1 p =
                 let uu____4737 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____4771 =
                         FStar_List.fold_left
                           (fun uu____4809  ->
                              fun uu____4810  ->
                                match (uu____4809, uu____4810) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____4891 = process_pattern bs2 arg
                                       in
                                    (match uu____4891 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____4771 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____4980 =
                           let uu____4981 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4981  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4980
                          in
                       let uu____4982 =
                         let uu____4985 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4985 :: bs1  in
                       (uu____4982, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____4990 =
                           let uu____4991 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4991  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4990
                          in
                       let uu____4992 =
                         let uu____4995 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4995 :: bs1  in
                       (uu____4992, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____5005 =
                           let uu____5006 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____5006  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____5005
                          in
                       let uu____5007 =
                         let uu____5008 =
                           let uu____5015 =
                             let uu____5018 = translate cfg1 bs1 tm  in
                             readback1 uu____5018  in
                           (x, uu____5015)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____5008  in
                       (bs1, uu____5007)
                    in
                 match uu____4737 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___258_5038 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___258_5038.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____5057  ->
                    match uu____5057 with
                    | (pat,when_clause,e1) ->
                        let uu____5079 = process_pattern bs pat  in
                        (match uu____5079 with
                         | (bs',pat') ->
                             let uu____5092 =
                               let uu____5093 =
                                 let uu____5096 = translate cfg1 bs' e1  in
                                 readback1 uu____5096  in
                               (pat', when_clause, uu____5093)  in
                             FStar_Syntax_Util.branch uu____5092)) branches
                in
             let rec case scrut1 =
               debug1
                 (fun uu____5118  ->
                    let uu____5119 =
                      let uu____5120 = readback cfg scrut1  in
                      FStar_Syntax_Print.term_to_string uu____5120  in
                    let uu____5121 =
                      FStar_TypeChecker_NBETerm.t_to_string scrut1  in
                    FStar_Util.print2 "Match case: (%s) -- (%s)\n" uu____5119
                      uu____5121);
               (let scrut2 = unlazy scrut1  in
                match scrut2 with
                | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                    (debug1
                       (fun uu____5147  ->
                          let uu____5148 =
                            let uu____5149 =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____5172  ->
                                      match uu____5172 with
                                      | (x,q) ->
                                          let uu____5185 =
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              x
                                             in
                                          Prims.strcat
                                            (if FStar_Util.is_some q
                                             then "#"
                                             else "") uu____5185))
                               in
                            FStar_All.pipe_right uu____5149
                              (FStar_String.concat "; ")
                             in
                          FStar_Util.print1 "Match args: %s\n" uu____5148);
                     (let uu____5189 = pickBranch cfg scrut2 branches  in
                      match uu____5189 with
                      | FStar_Pervasives_Native.Some (branch1,args1) ->
                          let uu____5210 =
                            FStar_List.fold_left
                              (fun bs1  -> fun x  -> x :: bs1) bs args1
                             in
                          translate cfg uu____5210 branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                            make_branches))
                | FStar_TypeChecker_NBETerm.Constant c ->
                    (debug1
                       (fun uu____5233  ->
                          let uu____5234 =
                            FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                          FStar_Util.print1 "Match constant : %s\n"
                            uu____5234);
                     (let uu____5235 = pickBranch cfg scrut2 branches  in
                      match uu____5235 with
                      | FStar_Pervasives_Native.Some (branch1,[]) ->
                          translate cfg bs branch1
                      | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                          translate cfg (arg :: bs) branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                            make_branches
                      | FStar_Pervasives_Native.Some (uu____5269,hd1::tl1) ->
                          failwith
                            "Impossible: Matching on constants cannot bind more than one variable"))
                | uu____5282 ->
                    FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                      make_branches)
                in
             let uu____5283 = translate cfg bs scrut  in case uu____5283
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
             let uu____5356 = make_rec_env (translate_letbinding cfg) lbs bs
                in
             translate cfg uu____5356 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____5360) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____5381  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____5392 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____5407  ->
                      match uu____5407 with
                      | (bv,t1) ->
                          let uu____5414 =
                            let uu____5421 = readback cfg t1  in
                            (bv, uu____5421)  in
                          FStar_Syntax_Syntax.NT uu____5414) uu____5392
                  in
               let uu____5426 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____5426  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close1 qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close1 qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let uu____5430 =
               let uu____5445 =
                 FStar_Common.mk_thunk
                   (fun uu____5450  ->
                      let uu____5451 = FStar_Syntax_Util.unfold_lazy li  in
                      translate cfg bs uu____5451)
                  in
               ((FStar_Util.Inl li), uu____5445)  in
             FStar_TypeChecker_NBETerm.Lazy uu____5430)

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
            let uu____5521 =
              let uu____5528 = translate cfg bs typ  in
              let uu____5529 = fmap_opt (translate_univ bs) u  in
              (uu____5528, uu____5529)  in
            FStar_TypeChecker_NBETerm.Tot uu____5521
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____5544 =
              let uu____5551 = translate cfg bs typ  in
              let uu____5552 = fmap_opt (translate_univ bs) u  in
              (uu____5551, uu____5552)  in
            FStar_TypeChecker_NBETerm.GTot uu____5544
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____5558 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____5558

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____5568 =
              let uu____5577 = readback cfg typ  in (uu____5577, u)  in
            FStar_Syntax_Syntax.Total uu____5568
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____5590 =
              let uu____5599 = readback cfg typ  in (uu____5599, u)  in
            FStar_Syntax_Syntax.GTotal uu____5590
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____5607 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____5607
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
        let uu____5613 = c  in
        match uu____5613 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags1;_} ->
            let uu____5633 = FStar_List.map (translate_univ bs) comp_univs
               in
            let uu____5634 = translate cfg bs result_typ  in
            let uu____5635 =
              FStar_List.map
                (fun x  ->
                   let uu____5663 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____5663, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____5670 = FStar_List.map (translate_flag cfg bs) flags1
               in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____5633;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____5634;
              FStar_TypeChecker_NBETerm.effect_args = uu____5635;
              FStar_TypeChecker_NBETerm.flags = uu____5670
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____5675 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____5678 =
        FStar_List.map
          (fun x  ->
             let uu____5704 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____5704, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____5705 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____5675;
        FStar_Syntax_Syntax.effect_args = uu____5678;
        FStar_Syntax_Syntax.flags = uu____5705
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
        let uu____5713 = c  in
        match uu____5713 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____5723 =
              FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____5728 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____5723;
              FStar_TypeChecker_NBETerm.residual_flags = uu____5728
            }

and (readback_residual_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____5733 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (readback cfg)
         in
      let uu____5740 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____5733;
        FStar_Syntax_Syntax.residual_flags = uu____5740
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
            let uu____5751 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____5751

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
          let uu____5755 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____5755

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____5758  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____5758 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____5793 =
                     let uu____5802 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____5802
                      in
                   (match uu____5793 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5809 =
                          let uu____5810 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____5810
                           in
                        failwith uu____5809
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___259_5824 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___259_5824.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___259_5824.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___259_5824.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___259_5824.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___259_5824.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___259_5824.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___259_5824.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___259_5824.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____5831 =
                            let uu____5838 =
                              let uu____5839 =
                                let uu____5858 =
                                  let uu____5867 =
                                    let uu____5874 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____5874,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____5867]  in
                                (uu____5858, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____5839  in
                            FStar_Syntax_Syntax.mk uu____5838  in
                          uu____5831 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____5911 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____5911
                          then
                            let uu____5918 =
                              let uu____5923 =
                                let uu____5924 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____5924  in
                              (uu____5923, FStar_Pervasives_Native.None)  in
                            let uu____5925 =
                              let uu____5932 =
                                let uu____5937 =
                                  let uu____5938 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____5938  in
                                (uu____5937, FStar_Pervasives_Native.None)
                                 in
                              [uu____5932]  in
                            uu____5918 :: uu____5925
                          else []  in
                        let t =
                          let uu____5957 =
                            let uu____5958 =
                              let uu____5959 =
                                FStar_Syntax_Util.un_uinst
                                  (FStar_Pervasives_Native.snd
                                     ed.FStar_Syntax_Syntax.bind_repr)
                                 in
                              translate cfg' [] uu____5959  in
                            iapp cfg uu____5958
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____5976 =
                            let uu____5977 =
                              let uu____5984 =
                                let uu____5989 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____5989, FStar_Pervasives_Native.None)
                                 in
                              let uu____5990 =
                                let uu____5997 =
                                  let uu____6002 = translate cfg' bs ty  in
                                  (uu____6002, FStar_Pervasives_Native.None)
                                   in
                                [uu____5997]  in
                              uu____5984 :: uu____5990  in
                            let uu____6015 =
                              let uu____6022 =
                                let uu____6029 =
                                  let uu____6036 =
                                    let uu____6041 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____6041,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____6042 =
                                    let uu____6049 =
                                      let uu____6056 =
                                        let uu____6061 =
                                          translate cfg bs body_lam  in
                                        (uu____6061,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____6056]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____6049
                                     in
                                  uu____6036 :: uu____6042  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____6029
                                 in
                              FStar_List.append maybe_range_arg uu____6022
                               in
                            FStar_List.append uu____5977 uu____6015  in
                          iapp cfg uu____5957 uu____5976  in
                        (debug cfg
                           (fun uu____6093  ->
                              let uu____6094 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____6094);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____6095);
                      FStar_Syntax_Syntax.pos = uu____6096;
                      FStar_Syntax_Syntax.vars = uu____6097;_},(e2,uu____6099)::[])
                   ->
                   translate
                     (let uu___260_6140 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___260_6140.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___260_6140.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___260_6140.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___260_6140.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___260_6140.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___260_6140.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___260_6140.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___260_6140.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   (debug cfg
                      (fun uu____6171  ->
                         let uu____6172 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____6173 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____6172
                           uu____6173);
                    (let fallback1 uu____6179 = translate cfg bs e1  in
                     let fallback2 uu____6185 =
                       let uu____6186 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           FStar_Pervasives_Native.None
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate
                         (let uu___261_6193 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___261_6193.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___261_6193.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___261_6193.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___261_6193.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___261_6193.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___261_6193.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___261_6193.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___261_6193.FStar_TypeChecker_Cfg.normalize_pure_lets);
                            FStar_TypeChecker_Cfg.reifying = false
                          }) bs uu____6186
                        in
                     let uu____6194 =
                       let uu____6195 = FStar_Syntax_Util.un_uinst head1  in
                       uu____6195.FStar_Syntax_Syntax.n  in
                     match uu____6194 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             cfg.FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____6201 =
                           let uu____6202 =
                             FStar_TypeChecker_Env.is_action
                               cfg.FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____6202  in
                         if uu____6201
                         then fallback1 ()
                         else
                           (let uu____6204 =
                              let uu____6205 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  cfg.FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____6205  in
                            if uu____6204
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____6220 =
                                   let uu____6225 =
                                     FStar_Syntax_Util.mk_reify head1  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____6225
                                     args
                                    in
                                 uu____6220 FStar_Pervasives_Native.None
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               translate
                                 (let uu___262_6230 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___262_6230.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___262_6230.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___262_6230.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___262_6230.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___262_6230.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong =
                                      (uu___262_6230.FStar_TypeChecker_Cfg.strong);
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___262_6230.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___262_6230.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying = false
                                  }) bs e2))
                     | uu____6231 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____6352  ->
                             match uu____6352 with
                             | (pat,wopt,tm) ->
                                 let uu____6400 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____6400)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   translate
                     (let uu___263_6434 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___263_6434.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___263_6434.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___263_6434.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___263_6434.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___263_6434.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___263_6434.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___263_6434.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___263_6434.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____6436) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____6463 ->
                   let uu____6464 =
                     let uu____6465 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____6465
                      in
                   failwith uu____6464)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____6466  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____6466 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____6490 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____6490
              then
                let ed =
                  let uu____6492 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____6492
                   in
                let ret1 =
                  let uu____6494 =
                    let uu____6495 =
                      FStar_Syntax_Subst.compress
                        (FStar_Pervasives_Native.snd
                           ed.FStar_Syntax_Syntax.return_repr)
                       in
                    uu____6495.FStar_Syntax_Syntax.n  in
                  match uu____6494 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret1,uu____6503::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret1, [FStar_Syntax_Syntax.U_unknown]))
                        FStar_Pervasives_Native.None
                        e1.FStar_Syntax_Syntax.pos
                  | uu____6510 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' =
                  let uu___264_6512 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___264_6512.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___264_6512.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___264_6512.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___264_6512.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___264_6512.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___264_6512.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___264_6512.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___264_6512.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let t =
                  let uu____6514 =
                    let uu____6515 = translate cfg' [] ret1  in
                    iapp cfg' uu____6515
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____6524 =
                    let uu____6525 =
                      let uu____6530 = translate cfg' bs ty  in
                      (uu____6530, FStar_Pervasives_Native.None)  in
                    let uu____6531 =
                      let uu____6538 =
                        let uu____6543 = translate cfg' bs e1  in
                        (uu____6543, FStar_Pervasives_Native.None)  in
                      [uu____6538]  in
                    uu____6525 :: uu____6531  in
                  iapp cfg' uu____6514 uu____6524  in
                (debug cfg
                   (fun uu____6559  ->
                      let uu____6560 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____6560);
                 t)
              else
                (let uu____6562 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____6562 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____6565 =
                       let uu____6566 = FStar_Ident.text_of_lid msrc  in
                       let uu____6567 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____6566 uu____6567
                        in
                     failwith uu____6565
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____6568;
                       FStar_TypeChecker_Env.mtarget = uu____6569;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____6570;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____6592 =
                       let uu____6593 = FStar_Ident.text_of_lid msrc  in
                       let uu____6594 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____6593 uu____6594
                        in
                     failwith uu____6592
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____6595;
                       FStar_TypeChecker_Env.mtarget = uu____6596;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____6597;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____6636 =
                         let uu____6639 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____6639
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____6636
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___265_6655 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___265_6655.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___265_6655.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___265_6655.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___265_6655.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___265_6655.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___265_6655.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___265_6655.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___265_6655.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let t =
                       let uu____6657 = translate cfg' [] lift_lam  in
                       let uu____6658 =
                         let uu____6659 =
                           let uu____6664 = translate cfg bs e1  in
                           (uu____6664, FStar_Pervasives_Native.None)  in
                         [uu____6659]  in
                       iapp cfg uu____6657 uu____6658  in
                     (debug cfg
                        (fun uu____6676  ->
                           let uu____6677 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____6677);
                      t))

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____6693  ->
           let uu____6694 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____6694);
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
           let uu____6697 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____6697 FStar_Syntax_Util.exp_int
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
           let uu____6750 =
             FStar_List.fold_left
               (fun uu____6793  ->
                  fun tf  ->
                    match uu____6793 with
                    | (args_rev,accus_rev) ->
                        let uu____6845 = tf accus_rev  in
                        (match uu____6845 with
                         | (xt,q) ->
                             let x1 =
                               let uu____6865 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____6865
                                in
                             let uu____6866 =
                               let uu____6869 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____6869 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____6866))) ([], [])
               targs
              in
           (match uu____6750 with
            | (args_rev,accus_rev) ->
                let body =
                  let uu____6913 = f (FStar_List.rev accus_rev)  in
                  readback cfg uu____6913  in
                let uu____6914 =
                  FStar_Util.map_opt resc
                    (fun thunk  ->
                       let uu____6925 = thunk ()  in
                       readback_residual_comp cfg uu____6925)
                   in
                FStar_Syntax_Util.abs (FStar_List.rev args_rev) body
                  uu____6914)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____6953 =
               let uu____6954 =
                 let uu____6955 = targ ()  in
                 FStar_Pervasives_Native.fst uu____6955  in
               readback cfg uu____6954  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____6953
              in
           let body =
             let uu____6961 =
               let uu____6962 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____6962  in
             readback cfg uu____6961  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t  in FStar_Syntax_Util.mk_reflect tm
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____6999 =
             FStar_List.fold_left
               (fun uu____7042  ->
                  fun tf  ->
                    match uu____7042 with
                    | (args_rev,accus_rev) ->
                        let uu____7094 = tf accus_rev  in
                        (match uu____7094 with
                         | (xt,q) ->
                             let x1 =
                               let uu____7114 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____7114
                                in
                             let uu____7115 =
                               let uu____7118 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____7118 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____7115))) ([], [])
               targs
              in
           (match uu____6999 with
            | (args_rev,accus_rev) ->
                let cmp =
                  let uu____7162 = f (FStar_List.rev accus_rev)  in
                  readback_comp cfg uu____7162  in
                FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____7205  ->
                  match uu____7205 with
                  | (x1,q) ->
                      let uu____7216 = readback cfg x1  in (uu____7216, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____7235 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____7242::uu____7243 ->
                let uu____7246 =
                  let uu____7249 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____7249
                    (FStar_List.rev us)
                   in
                apply uu____7246
            | [] ->
                let uu____7250 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____7250)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____7291  ->
                  match uu____7291 with
                  | (x1,q) ->
                      let uu____7302 = readback cfg x1  in (uu____7302, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____7321 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____7328::uu____7329 ->
                let uu____7332 =
                  let uu____7335 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____7335
                    (FStar_List.rev us)
                   in
                apply uu____7332
            | [] ->
                let uu____7336 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____7336)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____7383  ->
                  match uu____7383 with
                  | (x1,q) ->
                      let uu____7394 = readback cfg x1  in (uu____7394, q))
               ts
              in
           let uu____7395 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____7395 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____7455  ->
                  match uu____7455 with
                  | (x1,q) ->
                      let uu____7466 = readback cfg x1  in (uu____7466, q))
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
            | uu____7496 -> FStar_Syntax_Util.mk_app head1 args)
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
               (fun uu____7578  ->
                  match uu____7578 with
                  | (x1,q) ->
                      let uu____7589 = readback cfg x1  in (uu____7589, q))
               args
              in
           (match args1 with
            | [] -> head1
            | uu____7594 -> FStar_Syntax_Util.mk_app head1 args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____7606) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (uu____7623,thunk) ->
           let uu____7645 = FStar_Common.force_thunk thunk  in
           readback cfg uu____7645)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____7708 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____7715 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____7731 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____7751 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____7764 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____7770 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___253_7775  ->
    match uu___253_7775 with
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
            let uu___266_7811 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___267_7814 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___267_7814.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___267_7814.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___267_7814.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___267_7814.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___267_7814.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___267_7814.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___267_7814.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___267_7814.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___267_7814.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___267_7814.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___267_7814.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___267_7814.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___267_7814.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___267_7814.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___267_7814.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___267_7814.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___267_7814.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___267_7814.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___267_7814.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___267_7814.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___267_7814.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___267_7814.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___267_7814.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___267_7814.FStar_TypeChecker_Cfg.nbe_step)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___266_7811.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___266_7811.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___266_7811.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___266_7811.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___266_7811.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___266_7811.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___266_7811.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___266_7811.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____7818  ->
               let uu____7819 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with (%s) {\n" uu____7819);
          (let r =
             let uu____7821 = translate cfg1 [] e  in
             readback cfg1 uu____7821  in
           debug cfg1
             (fun uu____7825  ->
                let uu____7826 = FStar_Syntax_Print.term_to_string r  in
                FStar_Util.print1 "}\nNBE returned (%s) {\n" uu____7826);
           r)
  
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
          let uu___268_7848 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___269_7851 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___269_7851.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___269_7851.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___269_7851.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___269_7851.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___269_7851.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___269_7851.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___269_7851.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___269_7851.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___269_7851.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___269_7851.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___269_7851.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___269_7851.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___269_7851.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___269_7851.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___269_7851.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___269_7851.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___269_7851.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___269_7851.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___269_7851.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___269_7851.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___269_7851.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___269_7851.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___269_7851.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___269_7851.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___268_7848.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___268_7848.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___268_7848.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___268_7848.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___268_7848.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___268_7848.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___268_7848.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___268_7848.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____7855  ->
             let uu____7856 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____7856);
        (let r =
           let uu____7858 = translate cfg1 [] e  in readback cfg1 uu____7858
            in
         debug cfg1
           (fun uu____7862  ->
              let uu____7863 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s) {\n" uu____7863);
         r)
  