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
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun f  ->
      fun args  ->
        match f with
        | FStar_TypeChecker_NBETerm.Lam (f1,targs,n1) ->
            let m = FStar_List.length args  in
            if m < n1
            then
              let uu____2066 = FStar_List.splitAt m targs  in
              (match uu____2066 with
               | (uu____2106,targs') ->
                   let targs'1 =
                     FStar_List.map
                       (fun targ  ->
                          fun l  ->
                            let uu____2197 =
                              let uu____2200 =
                                map_append FStar_Pervasives_Native.fst args l
                                 in
                              FStar_List.rev uu____2200  in
                            targ uu____2197) targs'
                      in
                   FStar_TypeChecker_NBETerm.Lam
                     (((fun l  ->
                          let uu____2228 =
                            map_append FStar_Pervasives_Native.fst args l  in
                          f1 uu____2228)), targs'1, (n1 - m)))
            else
              if m = n1
              then
                (let uu____2244 =
                   FStar_List.map FStar_Pervasives_Native.fst args  in
                 f1 uu____2244)
              else
                (let uu____2252 = FStar_List.splitAt n1 args  in
                 match uu____2252 with
                 | (args1,args') ->
                     let uu____2299 =
                       let uu____2300 =
                         FStar_List.map FStar_Pervasives_Native.fst args1  in
                       f1 uu____2300  in
                     iapp cfg uu____2299 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____2419)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____2463 = aux args us ts  in
            (match uu____2463 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____2590)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____2634 = aux args us ts  in
            (match uu____2634 with
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
                 let uu____2794 = test_args full_args ar_lst  in
                 match uu____2794 with
                 | (can_unfold,args1,res) ->
                     if
                       Prims.op_Negation
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                     then
                       (debug cfg
                          (fun uu____2807  ->
                             let uu____2808 =
                               FStar_Syntax_Print.lbname_to_string
                                 lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Util.print1
                               "Zeta is not set; will not unfold %s\n"
                               uu____2808);
                        FStar_TypeChecker_NBETerm.Rec
                          (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                            ar_lst, tr_lb))
                     else
                       if can_unfold
                       then
                         (debug cfg
                            (fun uu____2833  ->
                               let uu____2834 =
                                 FStar_Syntax_Print.lbname_to_string
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               FStar_Util.print1
                                 "Beta reducing recursive function %s\n"
                                 uu____2834);
                          (match res with
                           | [] ->
                               let uu____2839 =
                                 let uu____2840 = make_rec_env tr_lb lbs bs
                                    in
                                 tr_lb uu____2840 lb  in
                               iapp cfg uu____2839 args1
                           | uu____2843::uu____2844 ->
                               let t =
                                 let uu____2860 =
                                   let uu____2861 = make_rec_env tr_lb lbs bs
                                      in
                                   tr_lb uu____2861 lb  in
                                 iapp cfg uu____2860 args1  in
                               iapp cfg t res))
                       else
                         FStar_TypeChecker_NBETerm.Rec
                           (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                             ar_lst, tr_lb))
        | FStar_TypeChecker_NBETerm.Quote uu____2885 ->
            let uu____2890 =
              let uu____2891 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2891  in
            failwith uu____2890
        | FStar_TypeChecker_NBETerm.Lazy uu____2892 ->
            let uu____2893 =
              let uu____2894 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2894  in
            failwith uu____2893
        | FStar_TypeChecker_NBETerm.Constant uu____2895 ->
            let uu____2896 =
              let uu____2897 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2897  in
            failwith uu____2896
        | FStar_TypeChecker_NBETerm.Univ uu____2898 ->
            let uu____2899 =
              let uu____2900 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2900  in
            failwith uu____2899
        | FStar_TypeChecker_NBETerm.Type_t uu____2901 ->
            let uu____2902 =
              let uu____2903 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2903  in
            failwith uu____2902
        | FStar_TypeChecker_NBETerm.Unknown  ->
            let uu____2904 =
              let uu____2905 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2905  in
            failwith uu____2904
        | FStar_TypeChecker_NBETerm.Refinement uu____2906 ->
            let uu____2921 =
              let uu____2922 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2922  in
            failwith uu____2921
        | FStar_TypeChecker_NBETerm.Arrow uu____2923 ->
            let uu____2944 =
              let uu____2945 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.strcat "NBE ill-typed application: " uu____2945  in
            failwith uu____2944

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
          let uu____2960 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2961 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2960 uu____2961  in
        let uu____2962 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2962
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2968 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2970  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2968 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2976  ->
                     let uu____2977 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2977);
                (let uu____2978 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____2978 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____2988  ->
                           let uu____2989 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n" uu____2989);
                      (let uu____2990 =
                         let uu____3013 =
                           let f uu____3040 uu____3041 =
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
                             let uu____3092 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 (iapp cfg) args'
                                in
                             match uu____3092 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____3103  ->
                                       let uu____3104 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____3105 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____3104 uu____3105);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____3111  ->
                                       let uu____3112 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____3112);
                                  (let uu____3113 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp cfg uu____3113 args'))), uu____3013,
                           arity)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____2990))
                 | FStar_Pervasives_Native.Some uu____3118 ->
                     (debug1
                        (fun uu____3124  ->
                           let uu____3125 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____3125);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____3130 ->
                     (debug1
                        (fun uu____3138  ->
                           let uu____3139 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____3139);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____3147;
                        FStar_Syntax_Syntax.sigquals = uu____3148;
                        FStar_Syntax_Syntax.sigmeta = uu____3149;
                        FStar_Syntax_Syntax.sigattrs = uu____3150;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____3219  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____3227  ->
                                 let uu____3228 =
                                   let uu____3229 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3229
                                    in
                                 let uu____3230 =
                                   let uu____3231 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3231
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____3228 uu____3230);
                            debug1
                              (fun uu____3239  ->
                                 let uu____3240 =
                                   let uu____3241 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3241
                                    in
                                 let uu____3242 =
                                   let uu____3243 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3243
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____3240 uu____3242);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____3244 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____3252;
                        FStar_Syntax_Syntax.sigquals = uu____3253;
                        FStar_Syntax_Syntax.sigmeta = uu____3254;
                        FStar_Syntax_Syntax.sigattrs = uu____3255;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____3324  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____3332  ->
                                 let uu____3333 =
                                   let uu____3334 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3334
                                    in
                                 let uu____3335 =
                                   let uu____3336 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3336
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____3333 uu____3335);
                            debug1
                              (fun uu____3344  ->
                                 let uu____3345 =
                                   let uu____3346 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____3346
                                    in
                                 let uu____3347 =
                                   let uu____3348 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____3348
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____3345 uu____3347);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____3349 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        | uu____3394 ->
            let uu____3397 =
              let uu____3420 =
                FStar_List.map
                  (fun uu____3445  ->
                     fun _ts  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____3420,
                (FStar_List.length us))
               in
            FStar_TypeChecker_NBETerm.Lam uu____3397

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
          let uu____3497 = FStar_Syntax_Util.let_rec_arity b  in
          match uu____3497 with
          | (ar,maybe_lst) ->
              let uu____3516 =
                match maybe_lst with
                | FStar_Pervasives_Native.None  ->
                    let uu____3531 =
                      FStar_Common.tabulate ar (fun uu____3535  -> true)  in
                    (ar, uu____3531)
                | FStar_Pervasives_Native.Some lst ->
                    let l = trim lst  in ((FStar_List.length l), l)
                 in
              (match uu____3516 with
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
              let uu____3646 =
                let uu____3649 = mkRec' callback lb lbs0 bs0  in uu____3649
                  :: bs1
                 in
              aux lbs' lbs0 uu____3646 bs0
           in
        aux lbs lbs bs bs

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____3663 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____3663
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____3669 ->
        let uu____3670 =
          let uu____3671 =
            let uu____3672 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____3672 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____3671  in
        failwith uu____3670

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
          (fun uu____3693  ->
             let uu____3694 =
               let uu____3695 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____3695  in
             let uu____3696 =
               let uu____3697 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____3697  in
             FStar_Util.print2 "Term: %s - %s\n" uu____3694 uu____3696);
        debug1
          (fun uu____3703  ->
             let uu____3704 =
               let uu____3705 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____3705  in
             FStar_Util.print1 "BS list: %s\n" uu____3704);
        (let uu____3710 =
           let uu____3711 = FStar_Syntax_Subst.compress e  in
           uu____3711.FStar_Syntax_Syntax.n  in
         match uu____3710 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____3714,uu____3715) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3753 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3753
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then FStar_List.nth bs db.FStar_Syntax_Syntax.index
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3769  ->
                   let uu____3770 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3771 =
                     let uu____3772 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3772
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____3770 uu____3771);
              (let uu____3777 = translate cfg bs t  in
               let uu____3778 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3782 =
                        let uu____3783 = translate_univ bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____3783  in
                      FStar_TypeChecker_NBETerm.as_arg uu____3782) us
                  in
               iapp cfg uu____3777 uu____3778))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3785 = translate_univ bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____3785
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____3808 =
               let uu____3829 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____3899 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____3899, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____3829)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____3808
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____3968  ->
                     let uu____3969 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____3969)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3971,uu____3972) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____4033,uu____4034) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____4059) ->
             let uu____4084 =
               let uu____4107 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____4177 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____4177, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____4107, (FStar_List.length xs))
                in
             FStar_TypeChecker_NBETerm.Lam uu____4084
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____4233;
                FStar_Syntax_Syntax.vars = uu____4234;_},arg::more::args)
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let uu____4294 = FStar_Syntax_Util.head_and_args e  in
             (match uu____4294 with
              | (reifyh,uu____4312) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app reifyh [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____4356 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____4356)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____4365;
                FStar_Syntax_Syntax.vars = uu____4366;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___250_4408 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___250_4408.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___250_4408.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___250_4408.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___250_4408.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___250_4408.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___250_4408.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___250_4408.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___250_4408.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____4446  ->
                   let uu____4447 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____4448 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____4447
                     uu____4448);
              (let uu____4449 = translate cfg bs head1  in
               let uu____4450 =
                 FStar_List.map
                   (fun x  ->
                      let uu____4472 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____4472, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____4449 uu____4450))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches readback1 =
               let cfg1 =
                 let uu___251_4533 = cfg  in
                 {
                   FStar_TypeChecker_Cfg.steps =
                     (let uu___252_4536 = cfg.FStar_TypeChecker_Cfg.steps  in
                      {
                        FStar_TypeChecker_Cfg.beta =
                          (uu___252_4536.FStar_TypeChecker_Cfg.beta);
                        FStar_TypeChecker_Cfg.iota =
                          (uu___252_4536.FStar_TypeChecker_Cfg.iota);
                        FStar_TypeChecker_Cfg.zeta = false;
                        FStar_TypeChecker_Cfg.weak =
                          (uu___252_4536.FStar_TypeChecker_Cfg.weak);
                        FStar_TypeChecker_Cfg.hnf =
                          (uu___252_4536.FStar_TypeChecker_Cfg.hnf);
                        FStar_TypeChecker_Cfg.primops =
                          (uu___252_4536.FStar_TypeChecker_Cfg.primops);
                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                          (uu___252_4536.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                        FStar_TypeChecker_Cfg.unfold_until =
                          (uu___252_4536.FStar_TypeChecker_Cfg.unfold_until);
                        FStar_TypeChecker_Cfg.unfold_only =
                          (uu___252_4536.FStar_TypeChecker_Cfg.unfold_only);
                        FStar_TypeChecker_Cfg.unfold_fully =
                          (uu___252_4536.FStar_TypeChecker_Cfg.unfold_fully);
                        FStar_TypeChecker_Cfg.unfold_attr =
                          (uu___252_4536.FStar_TypeChecker_Cfg.unfold_attr);
                        FStar_TypeChecker_Cfg.unfold_tac =
                          (uu___252_4536.FStar_TypeChecker_Cfg.unfold_tac);
                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                          =
                          (uu___252_4536.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                        FStar_TypeChecker_Cfg.simplify =
                          (uu___252_4536.FStar_TypeChecker_Cfg.simplify);
                        FStar_TypeChecker_Cfg.erase_universes =
                          (uu___252_4536.FStar_TypeChecker_Cfg.erase_universes);
                        FStar_TypeChecker_Cfg.allow_unbound_universes =
                          (uu___252_4536.FStar_TypeChecker_Cfg.allow_unbound_universes);
                        FStar_TypeChecker_Cfg.reify_ =
                          (uu___252_4536.FStar_TypeChecker_Cfg.reify_);
                        FStar_TypeChecker_Cfg.compress_uvars =
                          (uu___252_4536.FStar_TypeChecker_Cfg.compress_uvars);
                        FStar_TypeChecker_Cfg.no_full_norm =
                          (uu___252_4536.FStar_TypeChecker_Cfg.no_full_norm);
                        FStar_TypeChecker_Cfg.check_no_uvars =
                          (uu___252_4536.FStar_TypeChecker_Cfg.check_no_uvars);
                        FStar_TypeChecker_Cfg.unmeta =
                          (uu___252_4536.FStar_TypeChecker_Cfg.unmeta);
                        FStar_TypeChecker_Cfg.unascribe =
                          (uu___252_4536.FStar_TypeChecker_Cfg.unascribe);
                        FStar_TypeChecker_Cfg.in_full_norm_request =
                          (uu___252_4536.FStar_TypeChecker_Cfg.in_full_norm_request);
                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                          (uu___252_4536.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                        FStar_TypeChecker_Cfg.nbe_step =
                          (uu___252_4536.FStar_TypeChecker_Cfg.nbe_step)
                      });
                   FStar_TypeChecker_Cfg.tcenv =
                     (uu___251_4533.FStar_TypeChecker_Cfg.tcenv);
                   FStar_TypeChecker_Cfg.debug =
                     (uu___251_4533.FStar_TypeChecker_Cfg.debug);
                   FStar_TypeChecker_Cfg.delta_level =
                     (uu___251_4533.FStar_TypeChecker_Cfg.delta_level);
                   FStar_TypeChecker_Cfg.primitive_steps =
                     (uu___251_4533.FStar_TypeChecker_Cfg.primitive_steps);
                   FStar_TypeChecker_Cfg.strong =
                     (uu___251_4533.FStar_TypeChecker_Cfg.strong);
                   FStar_TypeChecker_Cfg.memoize_lazy =
                     (uu___251_4533.FStar_TypeChecker_Cfg.memoize_lazy);
                   FStar_TypeChecker_Cfg.normalize_pure_lets =
                     (uu___251_4533.FStar_TypeChecker_Cfg.normalize_pure_lets);
                   FStar_TypeChecker_Cfg.reifying =
                     (uu___251_4533.FStar_TypeChecker_Cfg.reifying)
                 }  in
               let rec process_pattern bs1 p =
                 let uu____4564 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____4598 =
                         FStar_List.fold_left
                           (fun uu____4636  ->
                              fun uu____4637  ->
                                match (uu____4636, uu____4637) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____4718 = process_pattern bs2 arg
                                       in
                                    (match uu____4718 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____4598 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____4807 =
                           let uu____4808 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4808  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4807
                          in
                       let uu____4809 =
                         let uu____4812 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4812 :: bs1  in
                       (uu____4809, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____4817 =
                           let uu____4818 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4818  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4817
                          in
                       let uu____4819 =
                         let uu____4822 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4822 :: bs1  in
                       (uu____4819, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____4832 =
                           let uu____4833 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4833  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4832
                          in
                       let uu____4834 =
                         let uu____4835 =
                           let uu____4842 =
                             let uu____4845 = translate cfg1 bs1 tm  in
                             readback1 uu____4845  in
                           (x, uu____4842)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____4835  in
                       (bs1, uu____4834)
                    in
                 match uu____4564 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___253_4865 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___253_4865.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____4884  ->
                    match uu____4884 with
                    | (pat,when_clause,e1) ->
                        let uu____4906 = process_pattern bs pat  in
                        (match uu____4906 with
                         | (bs',pat') ->
                             let uu____4919 =
                               let uu____4920 =
                                 let uu____4923 = translate cfg1 bs' e1  in
                                 readback1 uu____4923  in
                               (pat', when_clause, uu____4920)  in
                             FStar_Syntax_Util.branch uu____4919)) branches
                in
             let rec case scrut1 =
               debug1
                 (fun uu____4943  ->
                    let uu____4944 =
                      let uu____4945 = readback cfg scrut1  in
                      FStar_Syntax_Print.term_to_string uu____4945  in
                    FStar_Util.print1 "Match case: (%s)\n" uu____4944);
               (match scrut1 with
                | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                    (debug1
                       (fun uu____4970  ->
                          let uu____4971 =
                            let uu____4972 =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____4995  ->
                                      match uu____4995 with
                                      | (x,q) ->
                                          let uu____5008 =
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              x
                                             in
                                          Prims.strcat
                                            (if FStar_Util.is_some q
                                             then "#"
                                             else "") uu____5008))
                               in
                            FStar_All.pipe_right uu____4972
                              (FStar_String.concat "; ")
                             in
                          FStar_Util.print1 "Match args: %s\n" uu____4971);
                     (let uu____5012 = pickBranch cfg scrut1 branches  in
                      match uu____5012 with
                      | FStar_Pervasives_Native.Some (branch1,args1) ->
                          let uu____5033 =
                            FStar_List.fold_left
                              (fun bs1  -> fun x  -> x :: bs1) bs args1
                             in
                          translate cfg uu____5033 branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                            make_branches))
                | FStar_TypeChecker_NBETerm.Constant c ->
                    (debug1
                       (fun uu____5056  ->
                          let uu____5057 =
                            FStar_TypeChecker_NBETerm.t_to_string scrut1  in
                          FStar_Util.print1 "Match constant : %s\n"
                            uu____5057);
                     (let uu____5058 = pickBranch cfg scrut1 branches  in
                      match uu____5058 with
                      | FStar_Pervasives_Native.Some (branch1,[]) ->
                          translate cfg bs branch1
                      | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                          translate cfg (arg :: bs) branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                            make_branches
                      | FStar_Pervasives_Native.Some (uu____5092,hd1::tl1) ->
                          failwith
                            "Impossible: Matching on constants cannot bind more than one variable"))
                | uu____5105 ->
                    FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                      make_branches)
                in
             let uu____5106 = translate cfg bs scrut  in case uu____5106
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
             let uu____5179 = make_rec_env (translate_letbinding cfg) lbs bs
                in
             translate cfg uu____5179 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____5183) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____5204  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____5215 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____5230  ->
                      match uu____5230 with
                      | (bv,t1) ->
                          let uu____5237 =
                            let uu____5244 = readback cfg t1  in
                            (bv, uu____5244)  in
                          FStar_Syntax_Syntax.NT uu____5237) uu____5215
                  in
               let uu____5249 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____5249  in
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
            let uu____5268 =
              let uu____5275 = translate cfg bs typ  in
              let uu____5276 = fmap_opt (translate_univ bs) u  in
              (uu____5275, uu____5276)  in
            FStar_TypeChecker_NBETerm.Tot uu____5268
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____5291 =
              let uu____5298 = translate cfg bs typ  in
              let uu____5299 = fmap_opt (translate_univ bs) u  in
              (uu____5298, uu____5299)  in
            FStar_TypeChecker_NBETerm.GTot uu____5291
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____5305 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____5305

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____5315 =
              let uu____5324 = readback cfg typ  in (uu____5324, u)  in
            FStar_Syntax_Syntax.Total uu____5315
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____5337 =
              let uu____5346 = readback cfg typ  in (uu____5346, u)  in
            FStar_Syntax_Syntax.GTotal uu____5337
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____5354 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____5354
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
        let uu____5360 = c  in
        match uu____5360 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags1;_} ->
            let uu____5380 = FStar_List.map (translate_univ bs) comp_univs
               in
            let uu____5381 = translate cfg bs result_typ  in
            let uu____5382 =
              FStar_List.map
                (fun x  ->
                   let uu____5410 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____5410, (FStar_Pervasives_Native.snd x))) effect_args
               in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____5380;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____5381;
              FStar_TypeChecker_NBETerm.effect_args = uu____5382;
              FStar_TypeChecker_NBETerm.flags = flags1
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____5419 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____5422 =
        FStar_List.map
          (fun x  ->
             let uu____5448 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____5448, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____5419;
        FStar_Syntax_Syntax.effect_args = uu____5422;
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
  fun uu____5449  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____5449 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____5484 =
                     let uu____5493 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____5493
                      in
                   (match uu____5484 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5500 =
                          let uu____5501 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____5501
                           in
                        failwith uu____5500
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___254_5515 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___254_5515.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___254_5515.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___254_5515.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___254_5515.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___254_5515.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___254_5515.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___254_5515.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___254_5515.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____5522 =
                            let uu____5529 =
                              let uu____5530 =
                                let uu____5549 =
                                  let uu____5558 =
                                    let uu____5565 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____5565,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____5558]  in
                                (uu____5549, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____5530  in
                            FStar_Syntax_Syntax.mk uu____5529  in
                          uu____5522 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____5602 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____5602
                          then
                            let uu____5609 =
                              let uu____5614 =
                                let uu____5615 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____5615  in
                              (uu____5614, FStar_Pervasives_Native.None)  in
                            let uu____5616 =
                              let uu____5623 =
                                let uu____5628 =
                                  let uu____5629 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____5629  in
                                (uu____5628, FStar_Pervasives_Native.None)
                                 in
                              [uu____5623]  in
                            uu____5609 :: uu____5616
                          else []  in
                        let t =
                          let uu____5648 =
                            let uu____5649 =
                              let uu____5650 =
                                FStar_Syntax_Util.un_uinst
                                  (FStar_Pervasives_Native.snd
                                     ed.FStar_Syntax_Syntax.bind_repr)
                                 in
                              translate cfg' [] uu____5650  in
                            iapp cfg uu____5649
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____5667 =
                            let uu____5668 =
                              let uu____5675 =
                                let uu____5680 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____5680, FStar_Pervasives_Native.None)
                                 in
                              let uu____5681 =
                                let uu____5688 =
                                  let uu____5693 = translate cfg' bs ty  in
                                  (uu____5693, FStar_Pervasives_Native.None)
                                   in
                                [uu____5688]  in
                              uu____5675 :: uu____5681  in
                            let uu____5706 =
                              let uu____5713 =
                                let uu____5720 =
                                  let uu____5727 =
                                    let uu____5732 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____5732,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____5733 =
                                    let uu____5740 =
                                      let uu____5747 =
                                        let uu____5752 =
                                          translate cfg bs body_lam  in
                                        (uu____5752,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____5747]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____5740
                                     in
                                  uu____5727 :: uu____5733  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____5720
                                 in
                              FStar_List.append maybe_range_arg uu____5713
                               in
                            FStar_List.append uu____5668 uu____5706  in
                          iapp cfg uu____5648 uu____5667  in
                        (debug cfg
                           (fun uu____5784  ->
                              let uu____5785 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____5785);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____5786);
                      FStar_Syntax_Syntax.pos = uu____5787;
                      FStar_Syntax_Syntax.vars = uu____5788;_},(e2,uu____5790)::[])
                   ->
                   translate
                     (let uu___255_5831 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___255_5831.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___255_5831.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___255_5831.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___255_5831.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___255_5831.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___255_5831.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___255_5831.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___255_5831.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app uu____5832 -> translate cfg bs e1
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____5969  ->
                             match uu____5969 with
                             | (pat,wopt,tm) ->
                                 let uu____6017 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____6017)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   translate
                     (let uu___256_6051 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___256_6051.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___256_6051.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___256_6051.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___256_6051.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___256_6051.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___256_6051.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___256_6051.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___256_6051.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs tm
               | uu____6052 ->
                   let uu____6053 =
                     let uu____6054 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____6054
                      in
                   failwith uu____6053)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____6055  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____6055 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____6079 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____6079
              then
                let ed =
                  let uu____6081 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____6081
                   in
                let cfg' =
                  let uu___257_6083 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___257_6083.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___257_6083.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___257_6083.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___257_6083.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___257_6083.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___257_6083.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___257_6083.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___257_6083.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let t =
                  let uu____6085 =
                    let uu____6086 =
                      let uu____6087 =
                        FStar_Syntax_Util.un_uinst
                          (FStar_Pervasives_Native.snd
                             ed.FStar_Syntax_Syntax.return_repr)
                         in
                      translate cfg' [] uu____6087  in
                    iapp cfg uu____6086
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____6100 =
                    let uu____6101 =
                      let uu____6106 = translate cfg' bs ty  in
                      (uu____6106, FStar_Pervasives_Native.None)  in
                    let uu____6107 =
                      let uu____6114 =
                        let uu____6119 = translate cfg' bs e1  in
                        (uu____6119, FStar_Pervasives_Native.None)  in
                      [uu____6114]  in
                    uu____6101 :: uu____6107  in
                  iapp cfg uu____6085 uu____6100  in
                (debug cfg
                   (fun uu____6135  ->
                      let uu____6136 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____6136);
                 t)
              else
                (let uu____6138 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____6138 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____6141 =
                       let uu____6142 = FStar_Ident.text_of_lid msrc  in
                       let uu____6143 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____6142 uu____6143
                        in
                     failwith uu____6141
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____6144;
                       FStar_TypeChecker_Env.mtarget = uu____6145;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____6146;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____6168 =
                       let uu____6169 = FStar_Ident.text_of_lid msrc  in
                       let uu____6170 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____6169 uu____6170
                        in
                     failwith uu____6168
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____6171;
                       FStar_TypeChecker_Env.mtarget = uu____6172;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____6173;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____6212 =
                         let uu____6215 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____6215
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____6212
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___258_6231 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___258_6231.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___258_6231.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___258_6231.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___258_6231.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___258_6231.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___258_6231.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___258_6231.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___258_6231.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let t =
                       let uu____6233 = translate cfg' [] lift_lam  in
                       let uu____6234 =
                         let uu____6235 =
                           let uu____6240 = translate cfg bs e1  in
                           (uu____6240, FStar_Pervasives_Native.None)  in
                         [uu____6235]  in
                       iapp cfg uu____6233 uu____6234  in
                     (debug cfg
                        (fun uu____6252  ->
                           let uu____6253 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____6253);
                      t))

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____6269  ->
           let uu____6270 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____6270);
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
           let uu____6273 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____6273 FStar_Syntax_Util.exp_int
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
           let uu____6315 =
             FStar_List.fold_left
               (fun uu____6358  ->
                  fun tf  ->
                    match uu____6358 with
                    | (args_rev,accus_rev) ->
                        let uu____6410 = tf accus_rev  in
                        (match uu____6410 with
                         | (xt,q) ->
                             let x1 =
                               let uu____6430 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____6430
                                in
                             let uu____6431 =
                               let uu____6434 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____6434 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____6431))) ([], [])
               targs
              in
           (match uu____6315 with
            | (args_rev,accus_rev) ->
                let body =
                  let uu____6478 = f (FStar_List.rev accus_rev)  in
                  readback cfg uu____6478  in
                FStar_Syntax_Util.abs (FStar_List.rev args_rev) body
                  FStar_Pervasives_Native.None)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____6506 =
               let uu____6507 =
                 let uu____6508 = targ ()  in
                 FStar_Pervasives_Native.fst uu____6508  in
               readback cfg uu____6507  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____6506
              in
           let body =
             let uu____6514 =
               let uu____6515 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____6515  in
             readback cfg uu____6514  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____6550 =
             FStar_List.fold_left
               (fun uu____6593  ->
                  fun tf  ->
                    match uu____6593 with
                    | (args_rev,accus_rev) ->
                        let uu____6645 = tf accus_rev  in
                        (match uu____6645 with
                         | (xt,q) ->
                             let x1 =
                               let uu____6665 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____6665
                                in
                             let uu____6666 =
                               let uu____6669 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____6669 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____6666))) ([], [])
               targs
              in
           (match uu____6550 with
            | (args_rev,accus_rev) ->
                let cmp =
                  let uu____6713 = f (FStar_List.rev accus_rev)  in
                  readback_comp cfg uu____6713  in
                FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____6756  ->
                  match uu____6756 with
                  | (x1,q) ->
                      let uu____6767 = readback cfg x1  in (uu____6767, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____6786 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____6793::uu____6794 ->
                let uu____6797 =
                  let uu____6800 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____6800
                    (FStar_List.rev us)
                   in
                apply uu____6797
            | [] ->
                let uu____6801 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____6801)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____6842  ->
                  match uu____6842 with
                  | (x1,q) ->
                      let uu____6853 = readback cfg x1  in (uu____6853, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____6872 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____6879::uu____6880 ->
                let uu____6883 =
                  let uu____6886 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____6886
                    (FStar_List.rev us)
                   in
                apply uu____6883
            | [] ->
                let uu____6887 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____6887)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____6934  ->
                  match uu____6934 with
                  | (x1,q) ->
                      let uu____6945 = readback cfg x1  in (uu____6945, q))
               ts
              in
           let uu____6946 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____6946 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____7006  ->
                  match uu____7006 with
                  | (x1,q) ->
                      let uu____7017 = readback cfg x1  in (uu____7017, q))
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
            | uu____7047 -> FStar_Syntax_Util.mk_app head1 args)
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
               (fun uu____7129  ->
                  match uu____7129 with
                  | (x1,q) ->
                      let uu____7140 = readback cfg x1  in (uu____7140, q))
               args
              in
           (match args1 with
            | [] -> head1
            | uu____7145 -> FStar_Syntax_Util.mk_app head1 args1)
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
    match projectee with | Primops  -> true | uu____7179 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____7186 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____7202 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____7222 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____7235 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____7241 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___249_7246  ->
    match uu___249_7246 with
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
            let uu___259_7282 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___260_7285 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___260_7285.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___260_7285.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___260_7285.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___260_7285.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___260_7285.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___260_7285.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___260_7285.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___260_7285.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___260_7285.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___260_7285.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___260_7285.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___260_7285.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___260_7285.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___260_7285.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___260_7285.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___260_7285.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___260_7285.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___260_7285.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___260_7285.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___260_7285.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___260_7285.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___260_7285.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___260_7285.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___260_7285.FStar_TypeChecker_Cfg.nbe_step)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___259_7282.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___259_7282.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___259_7282.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___259_7282.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___259_7282.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___259_7282.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___259_7282.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___259_7282.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____7289  ->
               let uu____7290 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with %s" uu____7290);
          (let uu____7291 = translate cfg1 [] e  in readback cfg1 uu____7291)
  
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
          let uu___261_7313 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___262_7316 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___262_7316.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___262_7316.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___262_7316.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___262_7316.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___262_7316.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___262_7316.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___262_7316.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___262_7316.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___262_7316.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___262_7316.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___262_7316.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___262_7316.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___262_7316.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___262_7316.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___262_7316.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___262_7316.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___262_7316.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___262_7316.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___262_7316.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___262_7316.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___262_7316.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___262_7316.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___262_7316.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___262_7316.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___261_7313.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___261_7313.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___261_7313.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___261_7313.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___261_7313.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___261_7313.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___261_7313.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___261_7313.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____7320  ->
             let uu____7321 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____7321);
        (let r =
           let uu____7323 = translate cfg1 [] e  in readback cfg1 uu____7323
            in
         debug cfg1
           (fun uu____7327  ->
              let uu____7328 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "NBE returned %s" uu____7328);
         r)
  