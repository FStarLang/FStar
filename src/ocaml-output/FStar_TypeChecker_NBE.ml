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
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_var bv -> FStar_Util.Inl [scrutinee]
            | FStar_Syntax_Syntax.Pat_wild bv -> FStar_Util.Inl [scrutinee]
            | FStar_Syntax_Syntax.Pat_dot_term uu____494 -> FStar_Util.Inl []
            | FStar_Syntax_Syntax.Pat_constant s ->
                let matches_const c s1 =
                  debug cfg
                    (fun uu____519  ->
                       let uu____520 =
                         FStar_TypeChecker_NBETerm.t_to_string c  in
                       let uu____521 = FStar_Syntax_Print.const_to_string s1
                          in
                       FStar_Util.print2
                         "Testing term %s against pattern %s\n" uu____520
                         uu____521);
                  (match c with
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Unit ) ->
                       s1 = FStar_Const.Const_unit
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Bool b) ->
                       (match s1 with
                        | FStar_Const.Const_bool p1 -> b = p1
                        | uu____524 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Int i) ->
                       (match s1 with
                        | FStar_Const.Const_int
                            (p1,FStar_Pervasives_Native.None ) ->
                            let uu____537 = FStar_BigInt.big_int_of_string p1
                               in
                            i = uu____537
                        | uu____538 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.String (st,uu____540)) ->
                       (match s1 with
                        | FStar_Const.Const_string (p1,uu____542) -> st = p1
                        | uu____543 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Char c1) ->
                       (match s1 with
                        | FStar_Const.Const_char p1 -> c1 = p1
                        | uu____549 -> false)
                   | uu____550 -> false)
                   in
                let uu____551 = matches_const scrutinee s  in
                if uu____551 then FStar_Util.Inl [] else FStar_Util.Inr false
            | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                let rec matches_args out a p1 =
                  match (a, p1) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t,uu____672)::rest_a,(p2,uu____675)::rest_p) ->
                      let uu____709 = matches_pat t p2  in
                      (match uu____709 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____734 -> FStar_Util.Inr false  in
                (match scrutinee with
                 | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev) ->
                     let uu____778 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                     if uu____778
                     then matches_args [] (FStar_List.rev args_rev) arg_pats
                     else FStar_Util.Inr false
                 | uu____792 -> FStar_Util.Inr true)
             in
          match branches1 with
          | [] -> failwith "Branch not found"
          | (p,_wopt,e)::branches2 ->
              let uu____833 = matches_pat scrut1 p  in
              (match uu____833 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____856  ->
                         let uu____857 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____857);
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
        | (uu____1007,[]) -> (true, (FStar_List.rev acc), ts1)
        | ([],uu____1038::uu____1039) -> (false, (FStar_List.rev acc), [])
        | (t::ts2,b::bs) ->
            let uu____1102 =
              res &&
                (let uu____1104 =
                   let uu____1105 =
                     FStar_TypeChecker_NBETerm.isAccu
                       (FStar_Pervasives_Native.fst t)
                      in
                   Prims.op_Negation uu____1105  in
                 implies b uu____1104)
               in
            aux ts2 bs (t :: acc) uu____1102
         in
      aux ts ar_list [] true
  
let rec (count_abstractions : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    let uu____1119 =
      let uu____1120 = FStar_Syntax_Subst.compress t  in
      uu____1120.FStar_Syntax_Syntax.n  in
    match uu____1119 with
    | FStar_Syntax_Syntax.Tm_delayed uu____1123 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____1146 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_name uu____1147 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_fvar uu____1148 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_constant uu____1149 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_type uu____1150 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_arrow uu____1151 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uvar uu____1166 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_refine uu____1179 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_unknown  -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1187) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1194) ->
        let uu____1219 = count_abstractions body  in
        (FStar_List.length xs) + uu____1219
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1252 =
          let uu____1253 = count_abstractions head1  in
          uu____1253 - (FStar_List.length args)  in
        max uu____1252 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____1314,uu____1315,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____1364,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1383) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1389,uu____1390) ->
        count_abstractions t1
    | uu____1431 -> (Prims.parse_int "0")
  
let (find_sigelt_in_gamma :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.env ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lid  ->
        let mapper uu____1476 =
          match uu____1476 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1559  ->
                         let uu____1560 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1560);
                    FStar_Pervasives_Native.Some elt)
               | uu____1561 -> FStar_Pervasives_Native.None)
           in
        let uu____1576 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1576 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1620 -> true
    | uu____1621 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | uu____1628 -> failwith "Not a universe"
  
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
              (uu____1641,uu____1642,uu____1643,uu____1644,uu____1645,uu____1646);
            FStar_Syntax_Syntax.sigrng = uu____1647;
            FStar_Syntax_Syntax.sigquals = uu____1648;
            FStar_Syntax_Syntax.sigmeta = uu____1649;
            FStar_Syntax_Syntax.sigattrs = uu____1650;_},uu____1651),uu____1652)
        -> true
    | uu____1707 -> false
  
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
            let uu____1733 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1733
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1737 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1737
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____1740 -> u2
        | FStar_Syntax_Syntax.U_unif uu____1741 -> u2
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
           | FStar_Util.Inl uu____1771 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1775 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1775
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
            let uu____2065 = FStar_List.splitAt m targs  in
            (match uu____2065 with
             | (uu____2105,targs') ->
                 let targs'1 =
                   FStar_List.map
                     (fun targ  ->
                        fun l  ->
                          let uu____2196 =
                            let uu____2199 =
                              map_append FStar_Pervasives_Native.fst args l
                               in
                            FStar_List.rev uu____2199  in
                          targ uu____2196) targs'
                    in
                 FStar_TypeChecker_NBETerm.Lam
                   (((fun l  ->
                        let uu____2227 =
                          map_append FStar_Pervasives_Native.fst args l  in
                        f1 uu____2227)), targs'1, (n1 - m)))
          else
            if m = n1
            then
              (let uu____2243 =
                 FStar_List.map FStar_Pervasives_Native.fst args  in
               f1 uu____2243)
            else
              (let uu____2251 = FStar_List.splitAt n1 args  in
               match uu____2251 with
               | (args1,args') ->
                   let uu____2298 =
                     let uu____2299 =
                       FStar_List.map FStar_Pervasives_Native.fst args1  in
                     f1 uu____2299  in
                   iapp uu____2298 args')
      | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
          FStar_TypeChecker_NBETerm.Accu (a, (FStar_List.rev_append args ts))
      | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
          let rec aux args1 us1 ts1 =
            match args1 with
            | (FStar_TypeChecker_NBETerm.Univ u,uu____2418)::args2 ->
                aux args2 (u :: us1) ts1
            | a::args2 -> aux args2 us1 (a :: ts1)
            | [] -> (us1, ts1)  in
          let uu____2462 = aux args us ts  in
          (match uu____2462 with
           | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
      | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
          let rec aux args1 us1 ts1 =
            match args1 with
            | (FStar_TypeChecker_NBETerm.Univ u,uu____2589)::args2 ->
                aux args2 (u :: us1) ts1
            | a::args2 -> aux args2 us1 (a :: ts1)
            | [] -> (us1, ts1)  in
          let uu____2633 = aux args us ts  in
          (match uu____2633 with
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
               let uu____2793 = test_args full_args ar_lst  in
               match uu____2793 with
               | (can_unfold,args1,res) ->
                   if can_unfold
                   then
                     (match res with
                      | [] ->
                          let uu____2807 =
                            let uu____2808 = make_rec_env tr_lb lbs bs  in
                            tr_lb uu____2808 lb  in
                          iapp uu____2807 args1
                      | uu____2811::uu____2812 ->
                          let t =
                            let uu____2828 =
                              let uu____2829 = make_rec_env tr_lb lbs bs  in
                              tr_lb uu____2829 lb  in
                            iapp uu____2828 args1  in
                          iapp t res)
                   else
                     FStar_TypeChecker_NBETerm.Rec
                       (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                         ar_lst, tr_lb))
      | FStar_TypeChecker_NBETerm.Quote uu____2853 ->
          let uu____2858 =
            let uu____2859 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2859  in
          failwith uu____2858
      | FStar_TypeChecker_NBETerm.Lazy uu____2860 ->
          let uu____2861 =
            let uu____2862 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2862  in
          failwith uu____2861
      | FStar_TypeChecker_NBETerm.Constant uu____2863 ->
          let uu____2864 =
            let uu____2865 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2865  in
          failwith uu____2864
      | FStar_TypeChecker_NBETerm.Univ uu____2866 ->
          let uu____2867 =
            let uu____2868 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2868  in
          failwith uu____2867
      | FStar_TypeChecker_NBETerm.Type_t uu____2869 ->
          let uu____2870 =
            let uu____2871 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2871  in
          failwith uu____2870
      | FStar_TypeChecker_NBETerm.Unknown  ->
          let uu____2872 =
            let uu____2873 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2873  in
          failwith uu____2872
      | FStar_TypeChecker_NBETerm.Refinement uu____2874 ->
          let uu____2889 =
            let uu____2890 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2890  in
          failwith uu____2889
      | FStar_TypeChecker_NBETerm.Arrow uu____2891 ->
          let uu____2912 =
            let uu____2913 = FStar_TypeChecker_NBETerm.t_to_string f  in
            Prims.strcat "NBE ill-typed application: " uu____2913  in
          failwith uu____2912

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
          let uu____2928 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2929 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2928 uu____2929  in
        let uu____2930 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2930
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2936 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2938  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2936 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2944  ->
                     let uu____2945 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2945);
                (let uu____2946 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____2946 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____2956  ->
                           let uu____2957 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n" uu____2957);
                      (let uu____2958 =
                         let uu____2981 =
                           let f uu____3008 uu____3009 =
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
                             let uu____3060 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 args'
                                in
                             match uu____3060 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____3071  ->
                                       let uu____3072 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____3073 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____3072 uu____3073);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____3079  ->
                                       let uu____3080 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____3080);
                                  (let uu____3081 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp uu____3081 args'))), uu____2981,
                           arity)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____2958))
                 | FStar_Pervasives_Native.Some uu____3086 ->
                     (debug1
                        (fun uu____3092  ->
                           let uu____3093 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____3093);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____3098 ->
                     (debug1
                        (fun uu____3106  ->
                           let uu____3107 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____3107);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____3115;
                        FStar_Syntax_Syntax.sigquals = uu____3116;
                        FStar_Syntax_Syntax.sigmeta = uu____3117;
                        FStar_Syntax_Syntax.sigattrs = uu____3118;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____3187  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____3195  ->
                                 let uu____3196 =
                                   let uu____3197 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3197
                                    in
                                 let uu____3198 =
                                   let uu____3199 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3199
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____3196 uu____3198);
                            debug1
                              (fun uu____3207  ->
                                 let uu____3208 =
                                   let uu____3209 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3209
                                    in
                                 let uu____3210 =
                                   let uu____3211 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3211
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____3208 uu____3210);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____3212 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____3220;
                        FStar_Syntax_Syntax.sigquals = uu____3221;
                        FStar_Syntax_Syntax.sigmeta = uu____3222;
                        FStar_Syntax_Syntax.sigattrs = uu____3223;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____3292  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____3300  ->
                                 let uu____3301 =
                                   let uu____3302 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3302
                                    in
                                 let uu____3303 =
                                   let uu____3304 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3304
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____3301 uu____3303);
                            debug1
                              (fun uu____3312  ->
                                 let uu____3313 =
                                   let uu____3314 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3314
                                    in
                                 let uu____3315 =
                                   let uu____3316 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3316
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____3313 uu____3315);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____3317 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        | uu____3362 ->
            let uu____3365 =
              let uu____3388 =
                FStar_List.map
                  (fun uu____3413  ->
                     fun _ts  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____3388,
                (FStar_List.length us))
               in
            FStar_TypeChecker_NBETerm.Lam uu____3365

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
          let uu____3465 = FStar_Syntax_Util.let_rec_arity b  in
          match uu____3465 with
          | (ar,maybe_lst) ->
              let uu____3484 =
                match maybe_lst with
                | FStar_Pervasives_Native.None  ->
                    let uu____3499 =
                      FStar_Common.tabulate ar (fun uu____3503  -> true)  in
                    (ar, uu____3499)
                | FStar_Pervasives_Native.Some lst ->
                    let l = trim lst  in ((FStar_List.length l), l)
                 in
              (match uu____3484 with
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
              let uu____3614 =
                let uu____3617 = mkRec' callback lb lbs0 bs0  in uu____3617
                  :: bs1
                 in
              aux lbs' lbs0 uu____3614 bs0
           in
        aux lbs lbs bs bs

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____3631 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____3631
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____3637 ->
        let uu____3638 =
          let uu____3639 =
            let uu____3640 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____3640 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____3639  in
        failwith uu____3638

and (translate_pat : FStar_Syntax_Syntax.pat -> FStar_TypeChecker_NBETerm.t)
  =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3643 = translate_constant c  in
        FStar_TypeChecker_NBETerm.Constant uu____3643
    | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
        let uu____3662 = FStar_TypeChecker_NBETerm.mkConstruct cfv [] []  in
        let uu____3667 =
          FStar_List.map
            (fun uu____3682  ->
               match uu____3682 with
               | (p1,uu____3694) ->
                   let uu____3695 = translate_pat p1  in
                   (uu____3695, FStar_Pervasives_Native.None)) pats
           in
        iapp uu____3662 uu____3667
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
          (fun uu____3726  ->
             let uu____3727 =
               let uu____3728 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____3728  in
             let uu____3729 =
               let uu____3730 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____3730  in
             FStar_Util.print2 "Term: %s - %s\n" uu____3727 uu____3729);
        debug1
          (fun uu____3736  ->
             let uu____3737 =
               let uu____3738 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____3738  in
             FStar_Util.print1 "BS list: %s\n" uu____3737);
        (let uu____3743 =
           let uu____3744 = FStar_Syntax_Subst.compress e  in
           uu____3744.FStar_Syntax_Syntax.n  in
         match uu____3743 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____3747,uu____3748) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3786 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3786
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then FStar_List.nth bs db.FStar_Syntax_Syntax.index
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3802  ->
                   let uu____3803 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3804 =
                     let uu____3805 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3805
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____3803 uu____3804);
              (let uu____3810 = translate cfg bs t  in
               let uu____3811 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3815 =
                        let uu____3816 = translate_univ bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____3816  in
                      FStar_TypeChecker_NBETerm.as_arg uu____3815) us
                  in
               iapp uu____3810 uu____3811))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3818 = translate_univ bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____3818
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____3841 =
               let uu____3862 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____3932 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____3932, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____3862)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____3841
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____4001  ->
                     let uu____4002 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____4002)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____4004,uu____4005) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____4066,uu____4067) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____4092) ->
             let uu____4117 =
               let uu____4140 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____4210 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____4210, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____4140, (FStar_List.length xs))
                in
             FStar_TypeChecker_NBETerm.Lam uu____4117
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____4266;
                FStar_Syntax_Syntax.vars = uu____4267;_},arg::more::args)
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let uu____4327 = FStar_Syntax_Util.head_and_args e  in
             (match uu____4327 with
              | (reifyh,uu____4345) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app reifyh [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____4389 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____4389)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____4398;
                FStar_Syntax_Syntax.vars = uu____4399;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___250_4441 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___250_4441.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___250_4441.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___250_4441.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___250_4441.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___250_4441.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___250_4441.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___250_4441.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___250_4441.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____4479  ->
                   let uu____4480 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____4481 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____4480
                     uu____4481);
              (let uu____4482 = translate cfg bs head1  in
               let uu____4483 =
                 FStar_List.map
                   (fun x  ->
                      let uu____4505 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____4505, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp uu____4482 uu____4483))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               debug1
                 (fun uu____4571  ->
                    let uu____4572 =
                      let uu____4573 = readback cfg scrut1  in
                      FStar_Syntax_Print.term_to_string uu____4573  in
                    FStar_Util.print1 "Match case: (%s)\n" uu____4572);
               (match scrut1 with
                | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                    (debug1
                       (fun uu____4598  ->
                          let uu____4599 =
                            let uu____4600 =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____4623  ->
                                      match uu____4623 with
                                      | (x,q) ->
                                          let uu____4636 =
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              x
                                             in
                                          Prims.strcat
                                            (if FStar_Util.is_some q
                                             then "#"
                                             else "") uu____4636))
                               in
                            FStar_All.pipe_right uu____4600
                              (FStar_String.concat "; ")
                             in
                          FStar_Util.print1 "Match args: %s\n" uu____4599);
                     (let uu____4640 = pickBranch cfg scrut1 branches  in
                      match uu____4640 with
                      | FStar_Pervasives_Native.Some (branch1,args1) ->
                          let uu____4661 =
                            FStar_List.fold_left
                              (fun bs1  -> fun x  -> x :: bs1) bs args1
                             in
                          translate cfg uu____4661 branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                            make_branches))
                | FStar_TypeChecker_NBETerm.Constant c ->
                    (debug1
                       (fun uu____4684  ->
                          let uu____4685 =
                            FStar_TypeChecker_NBETerm.t_to_string scrut1  in
                          FStar_Util.print1 "Match constant : %s\n"
                            uu____4685);
                     (let uu____4686 = pickBranch cfg scrut1 branches  in
                      match uu____4686 with
                      | FStar_Pervasives_Native.Some (branch1,[]) ->
                          translate cfg bs branch1
                      | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                          translate cfg (arg :: bs) branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                            make_branches
                      | FStar_Pervasives_Native.Some (uu____4720,hd1::tl1) ->
                          failwith
                            "Impossible: Matching on constants cannot bind more than one variable"))
                | uu____4733 ->
                    FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                      make_branches)
             
             and make_branches readback1 =
               let rec process_pattern bs1 p =
                 let uu____4766 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____4800 =
                         FStar_List.fold_left
                           (fun uu____4838  ->
                              fun uu____4839  ->
                                match (uu____4838, uu____4839) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____4920 = process_pattern bs2 arg
                                       in
                                    (match uu____4920 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____4800 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____5009 =
                           let uu____5010 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____5010  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____5009
                          in
                       let uu____5011 =
                         let uu____5014 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____5014 :: bs1  in
                       (uu____5011, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____5019 =
                           let uu____5020 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____5020  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____5019
                          in
                       let uu____5021 =
                         let uu____5024 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____5024 :: bs1  in
                       (uu____5021, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____5034 =
                           let uu____5035 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____5035  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____5034
                          in
                       let uu____5036 =
                         let uu____5037 =
                           let uu____5044 =
                             let uu____5047 = translate cfg bs1 tm  in
                             readback1 uu____5047  in
                           (x, uu____5044)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____5037  in
                       (bs1, uu____5036)
                    in
                 match uu____4766 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___251_5067 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___251_5067.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____5086  ->
                    match uu____5086 with
                    | (pat,when_clause,e1) ->
                        let uu____5108 = process_pattern bs pat  in
                        (match uu____5108 with
                         | (bs',pat') ->
                             let uu____5121 =
                               let uu____5122 =
                                 let uu____5125 = translate cfg bs' e1  in
                                 readback1 uu____5125  in
                               (pat', when_clause, uu____5122)  in
                             FStar_Syntax_Util.branch uu____5121)) branches
              in let uu____5134 = translate cfg bs scrut  in case uu____5134
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
             let uu____5207 = make_rec_env (translate_letbinding cfg) lbs bs
                in
             translate cfg uu____5207 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____5211) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____5232  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____5243 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____5258  ->
                      match uu____5258 with
                      | (bv,t1) ->
                          let uu____5265 =
                            let uu____5272 = readback cfg t1  in
                            (bv, uu____5272)  in
                          FStar_Syntax_Syntax.NT uu____5265) uu____5243
                  in
               let uu____5277 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____5277  in
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
            let uu____5296 =
              let uu____5303 = translate cfg bs typ  in
              let uu____5304 = fmap_opt (translate_univ bs) u  in
              (uu____5303, uu____5304)  in
            FStar_TypeChecker_NBETerm.Tot uu____5296
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____5319 =
              let uu____5326 = translate cfg bs typ  in
              let uu____5327 = fmap_opt (translate_univ bs) u  in
              (uu____5326, uu____5327)  in
            FStar_TypeChecker_NBETerm.GTot uu____5319
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____5333 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____5333

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____5343 =
              let uu____5352 = readback cfg typ  in (uu____5352, u)  in
            FStar_Syntax_Syntax.Total uu____5343
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____5365 =
              let uu____5374 = readback cfg typ  in (uu____5374, u)  in
            FStar_Syntax_Syntax.GTotal uu____5365
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____5382 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____5382
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
        let uu____5388 = c  in
        match uu____5388 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags1;_} ->
            let uu____5408 = FStar_List.map (translate_univ bs) comp_univs
               in
            let uu____5409 = translate cfg bs result_typ  in
            let uu____5410 =
              FStar_List.map
                (fun x  ->
                   let uu____5438 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____5438, (FStar_Pervasives_Native.snd x))) effect_args
               in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____5408;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____5409;
              FStar_TypeChecker_NBETerm.effect_args = uu____5410;
              FStar_TypeChecker_NBETerm.flags = flags1
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____5447 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____5450 =
        FStar_List.map
          (fun x  ->
             let uu____5476 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____5476, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____5447;
        FStar_Syntax_Syntax.effect_args = uu____5450;
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
  fun uu____5477  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____5477 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____5512 =
                     let uu____5521 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____5521
                      in
                   (match uu____5512 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5528 =
                          let uu____5529 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____5529
                           in
                        failwith uu____5528
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___252_5543 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___252_5543.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___252_5543.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___252_5543.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___252_5543.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___252_5543.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___252_5543.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___252_5543.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___252_5543.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____5550 =
                            let uu____5557 =
                              let uu____5558 =
                                let uu____5577 =
                                  let uu____5586 =
                                    let uu____5593 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____5593,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____5586]  in
                                (uu____5577, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____5558  in
                            FStar_Syntax_Syntax.mk uu____5557  in
                          uu____5550 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____5630 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____5630
                          then
                            let uu____5637 =
                              let uu____5642 =
                                let uu____5643 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____5643  in
                              (uu____5642, FStar_Pervasives_Native.None)  in
                            let uu____5644 =
                              let uu____5651 =
                                let uu____5656 =
                                  let uu____5657 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____5657  in
                                (uu____5656, FStar_Pervasives_Native.None)
                                 in
                              [uu____5651]  in
                            uu____5637 :: uu____5644
                          else []  in
                        let t =
                          let uu____5676 =
                            let uu____5677 =
                              let uu____5678 =
                                FStar_Syntax_Util.un_uinst
                                  (FStar_Pervasives_Native.snd
                                     ed.FStar_Syntax_Syntax.bind_repr)
                                 in
                              translate cfg' [] uu____5678  in
                            iapp uu____5677
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____5695 =
                            let uu____5696 =
                              let uu____5703 =
                                let uu____5708 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____5708, FStar_Pervasives_Native.None)
                                 in
                              let uu____5709 =
                                let uu____5716 =
                                  let uu____5721 = translate cfg' bs ty  in
                                  (uu____5721, FStar_Pervasives_Native.None)
                                   in
                                [uu____5716]  in
                              uu____5703 :: uu____5709  in
                            let uu____5734 =
                              let uu____5741 =
                                let uu____5748 =
                                  let uu____5755 =
                                    let uu____5760 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____5760,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____5761 =
                                    let uu____5768 =
                                      let uu____5775 =
                                        let uu____5780 =
                                          translate cfg bs body_lam  in
                                        (uu____5780,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____5775]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____5768
                                     in
                                  uu____5755 :: uu____5761  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____5748
                                 in
                              FStar_List.append maybe_range_arg uu____5741
                               in
                            FStar_List.append uu____5696 uu____5734  in
                          iapp uu____5676 uu____5695  in
                        (debug cfg
                           (fun uu____5812  ->
                              let uu____5813 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____5813);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____5814);
                      FStar_Syntax_Syntax.pos = uu____5815;
                      FStar_Syntax_Syntax.vars = uu____5816;_},(e2,uu____5818)::[])
                   ->
                   translate
                     (let uu___253_5859 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___253_5859.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___253_5859.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___253_5859.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___253_5859.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___253_5859.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___253_5859.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___253_5859.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___253_5859.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app uu____5860 -> translate cfg bs e1
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____5997  ->
                             match uu____5997 with
                             | (pat,wopt,tm) ->
                                 let uu____6045 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____6045)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   translate
                     (let uu___254_6079 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___254_6079.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___254_6079.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___254_6079.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___254_6079.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___254_6079.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___254_6079.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___254_6079.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___254_6079.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs tm
               | uu____6080 ->
                   let uu____6081 =
                     let uu____6082 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____6082
                      in
                   failwith uu____6081)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____6083  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____6083 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____6107 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____6107
              then
                let ed =
                  let uu____6109 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____6109
                   in
                let cfg' =
                  let uu___255_6111 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___255_6111.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___255_6111.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___255_6111.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___255_6111.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___255_6111.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___255_6111.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___255_6111.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___255_6111.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let t =
                  let uu____6113 =
                    let uu____6114 =
                      let uu____6115 =
                        FStar_Syntax_Util.un_uinst
                          (FStar_Pervasives_Native.snd
                             ed.FStar_Syntax_Syntax.return_repr)
                         in
                      translate cfg' [] uu____6115  in
                    iapp uu____6114
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____6128 =
                    let uu____6129 =
                      let uu____6134 = translate cfg' bs ty  in
                      (uu____6134, FStar_Pervasives_Native.None)  in
                    let uu____6135 =
                      let uu____6142 =
                        let uu____6147 = translate cfg' bs e1  in
                        (uu____6147, FStar_Pervasives_Native.None)  in
                      [uu____6142]  in
                    uu____6129 :: uu____6135  in
                  iapp uu____6113 uu____6128  in
                (debug cfg
                   (fun uu____6163  ->
                      let uu____6164 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____6164);
                 t)
              else
                (let uu____6166 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____6166 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____6169 =
                       let uu____6170 = FStar_Ident.text_of_lid msrc  in
                       let uu____6171 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____6170 uu____6171
                        in
                     failwith uu____6169
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____6172;
                       FStar_TypeChecker_Env.mtarget = uu____6173;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____6174;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____6196 =
                       let uu____6197 = FStar_Ident.text_of_lid msrc  in
                       let uu____6198 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____6197 uu____6198
                        in
                     failwith uu____6196
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____6199;
                       FStar_TypeChecker_Env.mtarget = uu____6200;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____6201;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____6240 =
                         let uu____6243 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____6243
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____6240
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___256_6259 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___256_6259.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___256_6259.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___256_6259.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___256_6259.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___256_6259.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___256_6259.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___256_6259.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___256_6259.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let t =
                       let uu____6261 = translate cfg' [] lift_lam  in
                       let uu____6262 =
                         let uu____6263 =
                           let uu____6268 = translate cfg bs e1  in
                           (uu____6268, FStar_Pervasives_Native.None)  in
                         [uu____6263]  in
                       iapp uu____6261 uu____6262  in
                     (debug cfg
                        (fun uu____6280  ->
                           let uu____6281 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____6281);
                      t))

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____6297  ->
           let uu____6298 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____6298);
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
           let uu____6301 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____6301 FStar_Syntax_Util.exp_int
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
           let uu____6343 =
             FStar_List.fold_left
               (fun uu____6386  ->
                  fun tf  ->
                    match uu____6386 with
                    | (args_rev,accus_rev) ->
                        let uu____6438 = tf accus_rev  in
                        (match uu____6438 with
                         | (xt,q) ->
                             let x1 =
                               let uu____6458 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____6458
                                in
                             let uu____6459 =
                               let uu____6462 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____6462 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____6459))) ([], [])
               targs
              in
           (match uu____6343 with
            | (args_rev,accus_rev) ->
                let body =
                  let uu____6506 = f (FStar_List.rev accus_rev)  in
                  readback cfg uu____6506  in
                FStar_Syntax_Util.abs (FStar_List.rev args_rev) body
                  FStar_Pervasives_Native.None)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____6534 =
               let uu____6535 =
                 let uu____6536 = targ ()  in
                 FStar_Pervasives_Native.fst uu____6536  in
               readback cfg uu____6535  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____6534
              in
           let body =
             let uu____6542 =
               let uu____6543 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____6543  in
             readback cfg uu____6542  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____6578 =
             FStar_List.fold_left
               (fun uu____6621  ->
                  fun tf  ->
                    match uu____6621 with
                    | (args_rev,accus_rev) ->
                        let uu____6673 = tf accus_rev  in
                        (match uu____6673 with
                         | (xt,q) ->
                             let x1 =
                               let uu____6693 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____6693
                                in
                             let uu____6694 =
                               let uu____6697 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____6697 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____6694))) ([], [])
               targs
              in
           (match uu____6578 with
            | (args_rev,accus_rev) ->
                let cmp =
                  let uu____6741 = f (FStar_List.rev accus_rev)  in
                  readback_comp cfg uu____6741  in
                FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____6784  ->
                  match uu____6784 with
                  | (x1,q) ->
                      let uu____6795 = readback cfg x1  in (uu____6795, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____6814 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____6821::uu____6822 ->
                let uu____6825 =
                  let uu____6828 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____6828
                    (FStar_List.rev us)
                   in
                apply uu____6825
            | [] ->
                let uu____6829 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____6829)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____6870  ->
                  match uu____6870 with
                  | (x1,q) ->
                      let uu____6881 = readback cfg x1  in (uu____6881, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____6900 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____6907::uu____6908 ->
                let uu____6911 =
                  let uu____6914 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____6914
                    (FStar_List.rev us)
                   in
                apply uu____6911
            | [] ->
                let uu____6915 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____6915)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____6962  ->
                  match uu____6962 with
                  | (x1,q) ->
                      let uu____6973 = readback cfg x1  in (uu____6973, q))
               ts
              in
           let uu____6974 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____6974 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____7034  ->
                  match uu____7034 with
                  | (x1,q) ->
                      let uu____7045 = readback cfg x1  in (uu____7045, q))
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
            | uu____7075 -> FStar_Syntax_Util.mk_app head1 args)
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
               (fun uu____7157  ->
                  match uu____7157 with
                  | (x1,q) ->
                      let uu____7168 = readback cfg x1  in (uu____7168, q))
               args
              in
           (match args1 with
            | [] -> head1
            | uu____7173 -> FStar_Syntax_Util.mk_app head1 args1)
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
    match projectee with | Primops  -> true | uu____7207 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____7214 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____7230 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____7250 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____7263 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____7269 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___249_7274  ->
    match uu___249_7274 with
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
            let uu___257_7310 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___258_7313 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___258_7313.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___258_7313.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___258_7313.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___258_7313.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___258_7313.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___258_7313.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___258_7313.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___258_7313.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___258_7313.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___258_7313.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___258_7313.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___258_7313.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___258_7313.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___258_7313.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___258_7313.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___258_7313.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___258_7313.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___258_7313.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___258_7313.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___258_7313.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___258_7313.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___258_7313.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___258_7313.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___258_7313.FStar_TypeChecker_Cfg.nbe_step)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___257_7310.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___257_7310.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___257_7310.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___257_7310.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___257_7310.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___257_7310.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___257_7310.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___257_7310.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____7317  ->
               let uu____7318 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with %s" uu____7318);
          (let uu____7319 = translate cfg1 [] e  in readback cfg1 uu____7319)
  
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
          let uu___259_7341 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___260_7344 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___260_7344.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___260_7344.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___260_7344.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___260_7344.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___260_7344.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___260_7344.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___260_7344.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___260_7344.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___260_7344.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___260_7344.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___260_7344.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___260_7344.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___260_7344.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___260_7344.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___260_7344.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___260_7344.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___260_7344.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___260_7344.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___260_7344.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___260_7344.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___260_7344.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___260_7344.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___260_7344.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___260_7344.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___259_7341.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___259_7341.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___259_7341.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___259_7341.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___259_7341.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___259_7341.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___259_7341.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___259_7341.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____7348  ->
             let uu____7349 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____7349);
        (let r =
           let uu____7351 = translate cfg1 [] e  in readback cfg1 uu____7351
            in
         debug cfg1
           (fun uu____7355  ->
              let uu____7356 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "NBE returned %s" uu____7356);
         r)
  