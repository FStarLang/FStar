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
            let uu____59711 = let uu____59714 = f x  in uu____59714 :: acc
               in
            aux xs uu____59711
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
              let uu____59785 = let uu____59788 = f x  in uu____59788 :: acc
                 in
              aux xs uu____59785
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
            let uu____59838 = f x  in
            let uu____59839 = map_append f xs l2  in uu____59838 ::
              uu____59839
  
let rec drop : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p  ->
    fun l  ->
      match l with
      | [] -> []
      | x::xs ->
          let uu____59878 = p x  in
          if uu____59878 then x :: xs else drop p xs
  
let fmap_opt :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun x  ->
      FStar_Util.bind_opt x
        (fun x1  ->
           let uu____59920 = f x1  in
           FStar_Pervasives_Native.Some uu____59920)
  
let drop_until : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 =
        match l1 with
        | [] -> []
        | x::xs ->
            let uu____59970 = f x  in if uu____59970 then l1 else aux xs
         in
      aux l
  
let (trim : Prims.bool Prims.list -> Prims.bool Prims.list) =
  fun l  ->
    let uu____59995 = drop_until FStar_Pervasives.id (FStar_List.rev l)  in
    FStar_List.rev uu____59995
  
let (implies : Prims.bool -> Prims.bool -> Prims.bool) =
  fun b1  ->
    fun b2  ->
      match (b1, b2) with | (false ,uu____60022) -> true | (true ,b21) -> b21
  
let (debug : FStar_TypeChecker_Cfg.cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____60049 =
        let uu____60051 = FStar_TypeChecker_Cfg.cfg_env cfg  in
        FStar_TypeChecker_Env.debug uu____60051 (FStar_Options.Other "NBE")
         in
      if uu____60049 then f () else ()
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____60062 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____60062
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____60083 = FStar_Syntax_Print.sigelt_to_string_short v1
                in
             FStar_Util.print2 "%s -> %%s\n" k uu____60083) ()
  
let (unlazy : FStar_TypeChecker_NBETerm.t -> FStar_TypeChecker_NBETerm.t) =
  fun t  ->
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (uu____60092,t1) ->
        FStar_Common.force_thunk t1
    | t1 -> t1
  
let (pickBranch :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_Syntax_Syntax.branch Prims.list ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_NBETerm.t Prims.list)
          FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun scrut  ->
      fun branches  ->
        let rec pickBranch_aux scrut1 branches1 branches0 =
          let rec matches_pat scrutinee0 p =
            debug cfg
              (fun uu____60220  ->
                 let uu____60221 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0  in
                 let uu____60223 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____60221
                   uu____60223);
            (let scrutinee = unlazy scrutinee0  in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____60250 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____60277  ->
                          let uu____60278 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____60280 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n"
                            uu____60278 uu____60280);
                     (match c with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____60290 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____60307 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____60307
                           | uu____60308 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____60311))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____60316) ->
                               st = p1
                           | uu____60320 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____60328 -> false)
                      | uu____60330 -> false)
                      in
                   let uu____60332 = matches_const scrutinee s  in
                   if uu____60332
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____60470)::rest_a,(p2,uu____60473)::rest_p) ->
                         let uu____60512 = matches_pat t p2  in
                         (match uu____60512 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____60541 -> FStar_Util.Inr false  in
                   (match scrutinee with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____60589 = FStar_Syntax_Syntax.fv_eq fv fv'
                           in
                        if uu____60589
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____60609 -> FStar_Util.Inr true)
                in
             let res_to_string uu___585_60627 =
               match uu___585_60627 with
               | FStar_Util.Inr b ->
                   let uu____60641 = FStar_Util.string_of_bool b  in
                   Prims.op_Hat "Inr " uu____60641
               | FStar_Util.Inl bs ->
                   let uu____60650 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.op_Hat "Inl " uu____60650
                in
             debug cfg
               (fun uu____60658  ->
                  let uu____60659 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____60661 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____60663 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____60659
                    uu____60661 uu____60663);
             r)
             in
          match branches1 with
          | [] -> failwith "Branch not found"
          | (p,_wopt,e)::branches2 ->
              let uu____60705 = matches_pat scrut1 p  in
              (match uu____60705 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____60730  ->
                         let uu____60731 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____60731);
                    FStar_Pervasives_Native.Some (e, matches))
               | FStar_Util.Inr (false ) ->
                   pickBranch_aux scrut1 branches2 branches0
               | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
           in
        pickBranch_aux scrut branches branches
  
let (test_args :
  (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
    Prims.bool Prims.list ->
      (Prims.bool * FStar_TypeChecker_NBETerm.args *
        FStar_TypeChecker_NBETerm.args))
  =
  fun ts  ->
    fun ar_list  ->
      let rec aux ts1 ar_list1 acc res =
        match (ts1, ar_list1) with
        | (uu____60899,[]) -> (true, (FStar_List.rev acc), ts1)
        | ([],uu____60934::uu____60935) -> (false, (FStar_List.rev acc), [])
        | (t::ts2,b::bs) ->
            let uu____61008 =
              res &&
                (let uu____61011 =
                   let uu____61013 =
                     FStar_TypeChecker_NBETerm.isAccu
                       (FStar_Pervasives_Native.fst t)
                      in
                   Prims.op_Negation uu____61013  in
                 implies b uu____61011)
               in
            aux ts2 bs (t :: acc) uu____61008
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
        let mapper uu____61069 =
          match uu____61069 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____61152  ->
                         let uu____61153 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____61153);
                    FStar_Pervasives_Native.Some elt)
               | uu____61156 -> FStar_Pervasives_Native.None)
           in
        let uu____61171 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____61171 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____61218 -> true
    | uu____61220 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | t ->
        let uu____61230 =
          let uu____61232 = FStar_TypeChecker_NBETerm.t_to_string t  in
          Prims.op_Hat "Not a universe: " uu____61232  in
        failwith uu____61230
  
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
              (uu____61254,uu____61255,uu____61256,uu____61257,uu____61258,uu____61259);
            FStar_Syntax_Syntax.sigrng = uu____61260;
            FStar_Syntax_Syntax.sigquals = uu____61261;
            FStar_Syntax_Syntax.sigmeta = uu____61262;
            FStar_Syntax_Syntax.sigattrs = uu____61263;_},uu____61264),uu____61265)
        -> true
    | uu____61323 -> false
  
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
            let uu____61355 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____61355
        | FStar_Syntax_Syntax.U_max us ->
            let uu____61359 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____61359
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____61362 -> u2
        | FStar_Syntax_Syntax.U_unif uu____61363 -> u2
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
           | FStar_Util.Inl uu____61394 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____61399 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____61399
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
              let uu____61746 = FStar_List.splitAt m targs  in
              (match uu____61746 with
               | (uu____61782,targs') ->
                   let targs'1 =
                     FStar_List.map
                       (fun targ  ->
                          fun l  ->
                            let uu____61873 =
                              let uu____61876 =
                                map_append FStar_Pervasives_Native.fst args l
                                 in
                              FStar_List.rev uu____61876  in
                            targ uu____61873) targs'
                      in
                   FStar_TypeChecker_NBETerm.Lam
                     (((fun l  ->
                          let uu____61910 =
                            map_append FStar_Pervasives_Native.fst args l  in
                          f1 uu____61910)), targs'1, (n1 - m), res))
            else
              if m = n1
              then
                (let uu____61921 =
                   FStar_List.map FStar_Pervasives_Native.fst args  in
                 f1 uu____61921)
              else
                (let uu____61930 = FStar_List.splitAt n1 args  in
                 match uu____61930 with
                 | (args1,args') ->
                     let uu____61977 =
                       let uu____61978 =
                         FStar_List.map FStar_Pervasives_Native.fst args1  in
                       f1 uu____61978  in
                     iapp cfg uu____61977 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____62097)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____62141 = aux args us ts  in
            (match uu____62141 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____62268)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____62312 = aux args us ts  in
            (match uu____62312 with
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
                 let uu____62478 = test_args full_args ar_lst  in
                 match uu____62478 with
                 | (can_unfold,args1,res) ->
                     if
                       Prims.op_Negation
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                     then
                       (debug cfg
                          (fun uu____62495  ->
                             let uu____62496 =
                               FStar_Syntax_Print.lbname_to_string
                                 lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Util.print1
                               "Zeta is not set; will not unfold %s\n"
                               uu____62496);
                        FStar_TypeChecker_NBETerm.Rec
                          (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                            ar_lst, tr_lb))
                     else
                       if can_unfold
                       then
                         (debug cfg
                            (fun uu____62528  ->
                               let uu____62529 =
                                 FStar_Syntax_Print.lbname_to_string
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               FStar_Util.print1
                                 "Beta reducing recursive function %s\n"
                                 uu____62529);
                          (match res with
                           | [] ->
                               let uu____62536 =
                                 let uu____62537 = make_rec_env tr_lb lbs bs
                                    in
                                 tr_lb uu____62537 lb  in
                               iapp cfg uu____62536 args1
                           | uu____62540::uu____62541 ->
                               let t =
                                 let uu____62557 =
                                   let uu____62558 =
                                     make_rec_env tr_lb lbs bs  in
                                   tr_lb uu____62558 lb  in
                                 iapp cfg uu____62557 args1  in
                               iapp cfg t res))
                       else
                         FStar_TypeChecker_NBETerm.Rec
                           (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                             ar_lst, tr_lb))
        | FStar_TypeChecker_NBETerm.Quote uu____62586 ->
            let uu____62591 =
              let uu____62593 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____62593  in
            failwith uu____62591
        | FStar_TypeChecker_NBETerm.Reflect uu____62596 ->
            let uu____62597 =
              let uu____62599 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____62599  in
            failwith uu____62597
        | FStar_TypeChecker_NBETerm.Lazy uu____62602 ->
            let uu____62617 =
              let uu____62619 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____62619  in
            failwith uu____62617
        | FStar_TypeChecker_NBETerm.Constant uu____62622 ->
            let uu____62623 =
              let uu____62625 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____62625  in
            failwith uu____62623
        | FStar_TypeChecker_NBETerm.Univ uu____62628 ->
            let uu____62629 =
              let uu____62631 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____62631  in
            failwith uu____62629
        | FStar_TypeChecker_NBETerm.Type_t uu____62634 ->
            let uu____62635 =
              let uu____62637 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____62637  in
            failwith uu____62635
        | FStar_TypeChecker_NBETerm.Unknown  ->
            let uu____62640 =
              let uu____62642 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____62642  in
            failwith uu____62640
        | FStar_TypeChecker_NBETerm.Refinement uu____62645 ->
            let uu____62660 =
              let uu____62662 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____62662  in
            failwith uu____62660
        | FStar_TypeChecker_NBETerm.Arrow uu____62665 ->
            let uu____62686 =
              let uu____62688 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____62688  in
            failwith uu____62686

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
          let uu____62705 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____62706 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____62705 uu____62706  in
        let uu____62707 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____62707
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____62716 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____62718  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____62716 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____62725  ->
                     let uu____62726 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____62726);
                (let uu____62729 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____62729 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____62740  ->
                           let uu____62741 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n"
                             uu____62741);
                      (let uu____62744 =
                         let uu____62775 =
                           let f uu____62803 uu____62804 =
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
                             let uu____62864 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 callbacks args'
                                in
                             match uu____62864 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____62875  ->
                                       let uu____62876 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____62878 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____62876 uu____62878);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____62886  ->
                                       let uu____62887 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____62887);
                                  (let uu____62890 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp cfg uu____62890 args'))),
                           uu____62775, arity, FStar_Pervasives_Native.None)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____62744))
                 | FStar_Pervasives_Native.Some uu____62898 ->
                     (debug1
                        (fun uu____62904  ->
                           let uu____62905 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____62905);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____62912 ->
                     (debug1
                        (fun uu____62920  ->
                           let uu____62921 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____62921);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____62931;
                        FStar_Syntax_Syntax.sigquals = uu____62932;
                        FStar_Syntax_Syntax.sigmeta = uu____62933;
                        FStar_Syntax_Syntax.sigattrs = uu____62934;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____63007  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____63017  ->
                                 let uu____63018 =
                                   let uu____63020 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____63020
                                    in
                                 let uu____63021 =
                                   let uu____63023 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____63023
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____63018 uu____63021);
                            debug1
                              (fun uu____63032  ->
                                 let uu____63033 =
                                   let uu____63035 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____63035
                                    in
                                 let uu____63036 =
                                   let uu____63038 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____63038
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____63033 uu____63036);
                            translate_letbinding cfg bs lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____63041 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____63049;
                        FStar_Syntax_Syntax.sigquals = uu____63050;
                        FStar_Syntax_Syntax.sigmeta = uu____63051;
                        FStar_Syntax_Syntax.sigattrs = uu____63052;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____63125  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____63135  ->
                                 let uu____63136 =
                                   let uu____63138 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____63138
                                    in
                                 let uu____63139 =
                                   let uu____63141 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____63141
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____63136 uu____63139);
                            debug1
                              (fun uu____63150  ->
                                 let uu____63151 =
                                   let uu____63153 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____63153
                                    in
                                 let uu____63154 =
                                   let uu____63156 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____63156
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____63151 uu____63154);
                            translate_letbinding cfg bs lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____63159 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        | uu____63204 ->
            let uu____63207 =
              let uu____63238 =
                FStar_List.map
                  (fun uu____63263  ->
                     fun _ts  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____63238,
                (FStar_List.length us), FStar_Pervasives_Native.None)
               in
            FStar_TypeChecker_NBETerm.Lam uu____63207

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
          let uu____63324 = FStar_Syntax_Util.let_rec_arity b  in
          match uu____63324 with
          | (ar,maybe_lst) ->
              let uu____63349 =
                match maybe_lst with
                | FStar_Pervasives_Native.None  ->
                    let uu____63369 =
                      FStar_Common.tabulate ar (fun uu____63375  -> true)  in
                    (ar, uu____63369)
                | FStar_Pervasives_Native.Some lst ->
                    let l = trim lst  in ((FStar_List.length l), l)
                 in
              (match uu____63349 with
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
              let uu____63502 =
                let uu____63505 = mkRec' callback lb lbs0 bs0  in uu____63505
                  :: bs1
                 in
              aux lbs' lbs0 uu____63502 bs0
           in
        aux lbs lbs bs bs

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____63522 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____63522
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____63531 ->
        let uu____63532 =
          let uu____63534 =
            let uu____63536 = FStar_Syntax_Print.const_to_string c  in
            Prims.op_Hat uu____63536 ": Not yet implemented"  in
          Prims.op_Hat "Tm_constant " uu____63534  in
        failwith uu____63532

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
          (fun uu____63560  ->
             let uu____63561 =
               let uu____63563 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____63563  in
             let uu____63564 =
               let uu____63566 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____63566  in
             FStar_Util.print2 "Term: %s - %s\n" uu____63561 uu____63564);
        debug1
          (fun uu____63573  ->
             let uu____63574 =
               let uu____63576 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____63576  in
             FStar_Util.print1 "BS list: %s\n" uu____63574);
        (let uu____63585 =
           let uu____63586 = FStar_Syntax_Subst.compress e  in
           uu____63586.FStar_Syntax_Syntax.n  in
         match uu____63585 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____63589,uu____63590) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____63629 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____63629
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then FStar_List.nth bs db.FStar_Syntax_Syntax.index
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____63648  ->
                   let uu____63649 = FStar_Syntax_Print.term_to_string t  in
                   let uu____63651 =
                     let uu____63653 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____63653
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____63649 uu____63651);
              (let uu____63664 = translate cfg bs t  in
               let uu____63665 =
                 FStar_List.map
                   (fun x  ->
                      let uu____63669 =
                        let uu____63670 = translate_univ bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____63670  in
                      FStar_TypeChecker_NBETerm.as_arg uu____63669) us
                  in
               iapp cfg uu____63664 uu____63665))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____63672 = translate_univ bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____63672
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____63695 =
               let uu____63716 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____63786 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____63786, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____63716)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____63695
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____63855  ->
                     let uu____63856 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____63856)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____63858,uu____63859) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____63921,uu____63922) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             let uu____63973 =
               let uu____64004 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____64074 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____64074, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               let uu____64103 =
                 FStar_Util.map_opt resc
                   (fun c  ->
                      fun uu____64115  -> translate_residual_comp cfg bs c)
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____64004, (FStar_List.length xs), uu____64103)
                in
             FStar_TypeChecker_NBETerm.Lam uu____63973
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____64149;
                FStar_Syntax_Syntax.vars = uu____64150;_},arg::more::args)
             ->
             let uu____64210 = FStar_Syntax_Util.head_and_args e  in
             (match uu____64210 with
              | (head1,uu____64228) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____64272 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____64272)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____64281);
                FStar_Syntax_Syntax.pos = uu____64282;
                FStar_Syntax_Syntax.vars = uu____64283;_},arg::more::args)
             ->
             let uu____64343 = FStar_Syntax_Util.head_and_args e  in
             (match uu____64343 with
              | (head1,uu____64361) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____64405 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____64405)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____64414);
                FStar_Syntax_Syntax.pos = uu____64415;
                FStar_Syntax_Syntax.vars = uu____64416;_},arg::[])
             when cfg.FStar_TypeChecker_Cfg.reifying ->
             let cfg1 =
               let uu___1234_64457 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___1234_64457.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___1234_64457.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___1234_64457.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___1234_64457.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___1234_64457.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___1234_64457.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___1234_64457.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___1234_64457.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = false
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____64463);
                FStar_Syntax_Syntax.pos = uu____64464;
                FStar_Syntax_Syntax.vars = uu____64465;_},arg::[])
             ->
             let uu____64505 =
               translate cfg bs (FStar_Pervasives_Native.fst arg)  in
             FStar_TypeChecker_NBETerm.Reflect uu____64505
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____64510;
                FStar_Syntax_Syntax.vars = uu____64511;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___1257_64553 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___1257_64553.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___1257_64553.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___1257_64553.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___1257_64553.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___1257_64553.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___1257_64553.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___1257_64553.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___1257_64553.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____64592  ->
                   let uu____64593 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____64595 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____64593
                     uu____64595);
              (let uu____64598 = translate cfg bs head1  in
               let uu____64599 =
                 FStar_List.map
                   (fun x  ->
                      let uu____64621 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____64621, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____64598 uu____64599))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches readback1 =
               let cfg1 =
                 let uu___1273_64682 = cfg  in
                 {
                   FStar_TypeChecker_Cfg.steps =
                     (let uu___1275_64685 = cfg.FStar_TypeChecker_Cfg.steps
                         in
                      {
                        FStar_TypeChecker_Cfg.beta =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.beta);
                        FStar_TypeChecker_Cfg.iota =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.iota);
                        FStar_TypeChecker_Cfg.zeta = false;
                        FStar_TypeChecker_Cfg.weak =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.weak);
                        FStar_TypeChecker_Cfg.hnf =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.hnf);
                        FStar_TypeChecker_Cfg.primops =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.primops);
                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                        FStar_TypeChecker_Cfg.unfold_until =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.unfold_until);
                        FStar_TypeChecker_Cfg.unfold_only =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.unfold_only);
                        FStar_TypeChecker_Cfg.unfold_fully =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.unfold_fully);
                        FStar_TypeChecker_Cfg.unfold_attr =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.unfold_attr);
                        FStar_TypeChecker_Cfg.unfold_tac =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.unfold_tac);
                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                          =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                        FStar_TypeChecker_Cfg.simplify =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.simplify);
                        FStar_TypeChecker_Cfg.erase_universes =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.erase_universes);
                        FStar_TypeChecker_Cfg.allow_unbound_universes =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.allow_unbound_universes);
                        FStar_TypeChecker_Cfg.reify_ =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.reify_);
                        FStar_TypeChecker_Cfg.compress_uvars =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.compress_uvars);
                        FStar_TypeChecker_Cfg.no_full_norm =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.no_full_norm);
                        FStar_TypeChecker_Cfg.check_no_uvars =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.check_no_uvars);
                        FStar_TypeChecker_Cfg.unmeta =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.unmeta);
                        FStar_TypeChecker_Cfg.unascribe =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.unascribe);
                        FStar_TypeChecker_Cfg.in_full_norm_request =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.in_full_norm_request);
                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                        FStar_TypeChecker_Cfg.nbe_step =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.nbe_step);
                        FStar_TypeChecker_Cfg.for_extraction =
                          (uu___1275_64685.FStar_TypeChecker_Cfg.for_extraction)
                      });
                   FStar_TypeChecker_Cfg.tcenv =
                     (uu___1273_64682.FStar_TypeChecker_Cfg.tcenv);
                   FStar_TypeChecker_Cfg.debug =
                     (uu___1273_64682.FStar_TypeChecker_Cfg.debug);
                   FStar_TypeChecker_Cfg.delta_level =
                     (uu___1273_64682.FStar_TypeChecker_Cfg.delta_level);
                   FStar_TypeChecker_Cfg.primitive_steps =
                     (uu___1273_64682.FStar_TypeChecker_Cfg.primitive_steps);
                   FStar_TypeChecker_Cfg.strong =
                     (uu___1273_64682.FStar_TypeChecker_Cfg.strong);
                   FStar_TypeChecker_Cfg.memoize_lazy =
                     (uu___1273_64682.FStar_TypeChecker_Cfg.memoize_lazy);
                   FStar_TypeChecker_Cfg.normalize_pure_lets =
                     (uu___1273_64682.FStar_TypeChecker_Cfg.normalize_pure_lets);
                   FStar_TypeChecker_Cfg.reifying =
                     (uu___1273_64682.FStar_TypeChecker_Cfg.reifying)
                 }  in
               let rec process_pattern bs1 p =
                 let uu____64714 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____64750 =
                         FStar_List.fold_left
                           (fun uu____64791  ->
                              fun uu____64792  ->
                                match (uu____64791, uu____64792) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____64884 = process_pattern bs2 arg
                                       in
                                    (match uu____64884 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____64750 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____64983 =
                           let uu____64984 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____64984  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____64983
                          in
                       let uu____64985 =
                         let uu____64988 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____64988 :: bs1  in
                       (uu____64985, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____64993 =
                           let uu____64994 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____64994  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____64993
                          in
                       let uu____64995 =
                         let uu____64998 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____64998 :: bs1  in
                       (uu____64995, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____65008 =
                           let uu____65009 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____65009  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____65008
                          in
                       let uu____65010 =
                         let uu____65011 =
                           let uu____65018 =
                             let uu____65021 = translate cfg1 bs1 tm  in
                             readback1 uu____65021  in
                           (x, uu____65018)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____65011  in
                       (bs1, uu____65010)
                    in
                 match uu____64714 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___1313_65041 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___1313_65041.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____65060  ->
                    match uu____65060 with
                    | (pat,when_clause,e1) ->
                        let uu____65082 = process_pattern bs pat  in
                        (match uu____65082 with
                         | (bs',pat') ->
                             let uu____65095 =
                               let uu____65096 =
                                 let uu____65099 = translate cfg1 bs' e1  in
                                 readback1 uu____65099  in
                               (pat', when_clause, uu____65096)  in
                             FStar_Syntax_Util.branch uu____65095)) branches
                in
             let rec case scrut1 =
               debug1
                 (fun uu____65121  ->
                    let uu____65122 =
                      let uu____65124 = readback cfg scrut1  in
                      FStar_Syntax_Print.term_to_string uu____65124  in
                    let uu____65125 =
                      FStar_TypeChecker_NBETerm.t_to_string scrut1  in
                    FStar_Util.print2 "Match case: (%s) -- (%s)\n"
                      uu____65122 uu____65125);
               (let scrut2 = unlazy scrut1  in
                match scrut2 with
                | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                    (debug1
                       (fun uu____65153  ->
                          let uu____65154 =
                            let uu____65156 =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____65182  ->
                                      match uu____65182 with
                                      | (x,q) ->
                                          let uu____65196 =
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              x
                                             in
                                          Prims.op_Hat
                                            (if FStar_Util.is_some q
                                             then "#"
                                             else "") uu____65196))
                               in
                            FStar_All.pipe_right uu____65156
                              (FStar_String.concat "; ")
                             in
                          FStar_Util.print1 "Match args: %s\n" uu____65154);
                     (let uu____65210 = pickBranch cfg scrut2 branches  in
                      match uu____65210 with
                      | FStar_Pervasives_Native.Some (branch1,args1) ->
                          let uu____65231 =
                            FStar_List.fold_left
                              (fun bs1  -> fun x  -> x :: bs1) bs args1
                             in
                          translate cfg uu____65231 branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                            make_branches))
                | FStar_TypeChecker_NBETerm.Constant c ->
                    (debug1
                       (fun uu____65254  ->
                          let uu____65255 =
                            FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                          FStar_Util.print1 "Match constant : %s\n"
                            uu____65255);
                     (let uu____65258 = pickBranch cfg scrut2 branches  in
                      match uu____65258 with
                      | FStar_Pervasives_Native.Some (branch1,[]) ->
                          translate cfg bs branch1
                      | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                          translate cfg (arg :: bs) branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                            make_branches
                      | FStar_Pervasives_Native.Some (uu____65292,hd1::tl1)
                          ->
                          failwith
                            "Impossible: Matching on constants cannot bind more than one variable"))
                | uu____65306 ->
                    FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                      make_branches)
                in
             let uu____65307 = translate cfg bs scrut  in case uu____65307
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
             let uu____65386 = make_rec_env (translate_letbinding cfg) lbs bs
                in
             translate cfg uu____65386 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____65390) ->
             translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____65411  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____65424 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____65439  ->
                      match uu____65439 with
                      | (bv,t1) ->
                          let uu____65446 =
                            let uu____65453 = readback cfg t1  in
                            (bv, uu____65453)  in
                          FStar_Syntax_Syntax.NT uu____65446) uu____65424
                  in
               let uu____65458 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____65458  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close1 qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close1 qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu____65467 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____65474  ->
                    let uu____65475 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____65475);
               translate cfg bs t  in
             let uu____65478 =
               let uu____65493 = FStar_Common.mk_thunk f  in
               ((FStar_Util.Inl li), uu____65493)  in
             FStar_TypeChecker_NBETerm.Lazy uu____65478)

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
            let uu____65525 =
              let uu____65532 = translate cfg bs typ  in
              let uu____65533 = fmap_opt (translate_univ bs) u  in
              (uu____65532, uu____65533)  in
            FStar_TypeChecker_NBETerm.Tot uu____65525
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____65548 =
              let uu____65555 = translate cfg bs typ  in
              let uu____65556 = fmap_opt (translate_univ bs) u  in
              (uu____65555, uu____65556)  in
            FStar_TypeChecker_NBETerm.GTot uu____65548
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____65562 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____65562

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____65572 =
              let uu____65581 = readback cfg typ  in (uu____65581, u)  in
            FStar_Syntax_Syntax.Total uu____65572
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____65594 =
              let uu____65603 = readback cfg typ  in (uu____65603, u)  in
            FStar_Syntax_Syntax.GTotal uu____65594
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____65611 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____65611
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
        let uu____65617 = c  in
        match uu____65617 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____65637 = FStar_List.map (translate_univ bs) comp_univs
               in
            let uu____65638 = translate cfg bs result_typ  in
            let uu____65639 =
              FStar_List.map
                (fun x  ->
                   let uu____65667 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____65667, (FStar_Pervasives_Native.snd x)))
                effect_args
               in
            let uu____65674 = FStar_List.map (translate_flag cfg bs) flags
               in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____65637;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____65638;
              FStar_TypeChecker_NBETerm.effect_args = uu____65639;
              FStar_TypeChecker_NBETerm.flags = uu____65674
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____65679 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____65682 =
        FStar_List.map
          (fun x  ->
             let uu____65708 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____65708, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____65709 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____65679;
        FStar_Syntax_Syntax.effect_args = uu____65682;
        FStar_Syntax_Syntax.flags = uu____65709
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
        let uu____65717 = c  in
        match uu____65717 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____65727 =
              FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____65732 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____65727;
              FStar_TypeChecker_NBETerm.residual_flags = uu____65732
            }

and (readback_residual_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____65737 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (readback cfg)
         in
      let uu____65744 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____65737;
        FStar_Syntax_Syntax.residual_flags = uu____65744
      }

and (translate_flag :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.cflag -> FStar_TypeChecker_NBETerm.cflag)
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
            let uu____65755 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____65755

and (readback_flag :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.cflag -> FStar_Syntax_Syntax.cflag)
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
          let uu____65759 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____65759

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____65762  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____65762 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____65800 =
                     let uu____65809 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____65809
                      in
                   (match uu____65800 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____65816 =
                          let uu____65818 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____65818
                           in
                        failwith uu____65816
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___1521_65834 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___1521_65834.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___1521_65834.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___1521_65834.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___1521_65834.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___1521_65834.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___1521_65834.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___1521_65834.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___1521_65834.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____65842 =
                            let uu____65849 =
                              let uu____65850 =
                                let uu____65869 =
                                  let uu____65878 =
                                    let uu____65885 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____65885,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____65878]  in
                                (uu____65869, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____65850  in
                            FStar_Syntax_Syntax.mk uu____65849  in
                          uu____65842 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____65919 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____65919
                          then
                            let uu____65928 =
                              let uu____65933 =
                                let uu____65934 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____65934  in
                              (uu____65933, FStar_Pervasives_Native.None)  in
                            let uu____65935 =
                              let uu____65942 =
                                let uu____65947 =
                                  let uu____65948 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____65948  in
                                (uu____65947, FStar_Pervasives_Native.None)
                                 in
                              [uu____65942]  in
                            uu____65928 :: uu____65935
                          else []  in
                        let t =
                          let uu____65968 =
                            let uu____65969 =
                              let uu____65970 =
                                FStar_Syntax_Util.un_uinst
                                  (FStar_Pervasives_Native.snd
                                     ed.FStar_Syntax_Syntax.bind_repr)
                                 in
                              translate cfg' [] uu____65970  in
                            iapp cfg uu____65969
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____65987 =
                            let uu____65988 =
                              let uu____65995 =
                                let uu____66000 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____66000, FStar_Pervasives_Native.None)
                                 in
                              let uu____66001 =
                                let uu____66008 =
                                  let uu____66013 = translate cfg' bs ty  in
                                  (uu____66013, FStar_Pervasives_Native.None)
                                   in
                                [uu____66008]  in
                              uu____65995 :: uu____66001  in
                            let uu____66026 =
                              let uu____66033 =
                                let uu____66040 =
                                  let uu____66047 =
                                    let uu____66052 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____66052,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____66053 =
                                    let uu____66060 =
                                      let uu____66067 =
                                        let uu____66072 =
                                          translate cfg bs body_lam  in
                                        (uu____66072,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____66067]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____66060
                                     in
                                  uu____66047 :: uu____66053  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) ::
                                  uu____66040
                                 in
                              FStar_List.append maybe_range_arg uu____66033
                               in
                            FStar_List.append uu____65988 uu____66026  in
                          iapp cfg uu____65968 uu____65987  in
                        (debug cfg
                           (fun uu____66104  ->
                              let uu____66105 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____66105);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____66108);
                      FStar_Syntax_Syntax.pos = uu____66109;
                      FStar_Syntax_Syntax.vars = uu____66110;_},(e2,uu____66112)::[])
                   ->
                   translate
                     (let uu___1543_66153 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___1543_66153.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1543_66153.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1543_66153.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___1543_66153.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1543_66153.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1543_66153.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1543_66153.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___1543_66153.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   (debug cfg
                      (fun uu____66185  ->
                         let uu____66186 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____66188 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____66186
                           uu____66188);
                    (let fallback1 uu____66196 = translate cfg bs e1  in
                     let fallback2 uu____66202 =
                       let uu____66203 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           FStar_Pervasives_Native.None
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate
                         (let uu___1555_66210 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___1555_66210.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___1555_66210.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___1555_66210.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___1555_66210.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___1555_66210.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___1555_66210.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___1555_66210.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___1555_66210.FStar_TypeChecker_Cfg.normalize_pure_lets);
                            FStar_TypeChecker_Cfg.reifying = false
                          }) bs uu____66203
                        in
                     let uu____66212 =
                       let uu____66213 = FStar_Syntax_Util.un_uinst head1  in
                       uu____66213.FStar_Syntax_Syntax.n  in
                     match uu____66212 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             cfg.FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____66219 =
                           let uu____66221 =
                             FStar_TypeChecker_Env.is_action
                               cfg.FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____66221  in
                         if uu____66219
                         then fallback1 ()
                         else
                           (let uu____66226 =
                              let uu____66228 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  cfg.FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____66228  in
                            if uu____66226
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____66245 =
                                   let uu____66250 =
                                     FStar_Syntax_Util.mk_reify head1  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____66250
                                     args
                                    in
                                 uu____66245 FStar_Pervasives_Native.None
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               translate
                                 (let uu___1564_66253 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1564_66253.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1564_66253.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1564_66253.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1564_66253.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1564_66253.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong =
                                      (uu___1564_66253.FStar_TypeChecker_Cfg.strong);
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1564_66253.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1564_66253.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying = false
                                  }) bs e2))
                     | uu____66255 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____66376  ->
                             match uu____66376 with
                             | (pat,wopt,tm) ->
                                 let uu____66424 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____66424)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   translate
                     (let uu___1577_66458 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___1577_66458.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1577_66458.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1577_66458.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___1577_66458.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1577_66458.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1577_66458.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1577_66458.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___1577_66458.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____66461) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____66488 ->
                   let uu____66489 =
                     let uu____66491 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____66491
                      in
                   failwith uu____66489)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____66494  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____66494 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____66518 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____66518
              then
                let ed =
                  let uu____66522 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____66522
                   in
                let ret1 =
                  let uu____66524 =
                    let uu____66525 =
                      FStar_Syntax_Subst.compress
                        (FStar_Pervasives_Native.snd
                           ed.FStar_Syntax_Syntax.return_repr)
                       in
                    uu____66525.FStar_Syntax_Syntax.n  in
                  match uu____66524 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret1,uu____66533::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret1, [FStar_Syntax_Syntax.U_unknown]))
                        FStar_Pervasives_Native.None
                        e1.FStar_Syntax_Syntax.pos
                  | uu____66540 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' =
                  let uu___1610_66543 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___1610_66543.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1610_66543.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1610_66543.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___1610_66543.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1610_66543.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1610_66543.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1610_66543.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1610_66543.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let t =
                  let uu____66546 =
                    let uu____66547 = translate cfg' [] ret1  in
                    iapp cfg' uu____66547
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____66556 =
                    let uu____66557 =
                      let uu____66562 = translate cfg' bs ty  in
                      (uu____66562, FStar_Pervasives_Native.None)  in
                    let uu____66563 =
                      let uu____66570 =
                        let uu____66575 = translate cfg' bs e1  in
                        (uu____66575, FStar_Pervasives_Native.None)  in
                      [uu____66570]  in
                    uu____66557 :: uu____66563  in
                  iapp cfg' uu____66546 uu____66556  in
                (debug cfg
                   (fun uu____66591  ->
                      let uu____66592 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____66592);
                 t)
              else
                (let uu____66597 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____66597 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____66600 =
                       let uu____66602 = FStar_Ident.text_of_lid msrc  in
                       let uu____66604 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____66602 uu____66604
                        in
                     failwith uu____66600
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____66607;
                       FStar_TypeChecker_Env.mtarget = uu____66608;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____66609;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____66631 =
                       let uu____66633 = FStar_Ident.text_of_lid msrc  in
                       let uu____66635 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____66633 uu____66635
                        in
                     failwith uu____66631
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____66638;
                       FStar_TypeChecker_Env.mtarget = uu____66639;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____66640;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____66679 =
                         let uu____66682 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____66682
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____66679
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___1634_66698 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___1634_66698.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1634_66698.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1634_66698.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___1634_66698.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1634_66698.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1634_66698.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1634_66698.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___1634_66698.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let t =
                       let uu____66701 = translate cfg' [] lift_lam  in
                       let uu____66702 =
                         let uu____66703 =
                           let uu____66708 = translate cfg bs e1  in
                           (uu____66708, FStar_Pervasives_Native.None)  in
                         [uu____66703]  in
                       iapp cfg uu____66701 uu____66702  in
                     (debug cfg
                        (fun uu____66720  ->
                           let uu____66721 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____66721);
                      t))

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____66739  ->
           let uu____66740 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____66740);
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
           let uu____66748 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____66748 FStar_Syntax_Util.exp_int
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
           let uu____66808 =
             FStar_List.fold_left
               (fun uu____66851  ->
                  fun tf  ->
                    match uu____66851 with
                    | (args_rev,accus_rev) ->
                        let uu____66903 = tf accus_rev  in
                        (match uu____66903 with
                         | (xt,q) ->
                             let x1 =
                               let uu____66923 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____66923
                                in
                             let uu____66924 =
                               let uu____66927 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____66927 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____66924))) ([], [])
               targs
              in
           (match uu____66808 with
            | (args_rev,accus_rev) ->
                let body =
                  let uu____66971 = f (FStar_List.rev accus_rev)  in
                  readback cfg uu____66971  in
                let uu____66972 =
                  FStar_Util.map_opt resc
                    (fun thunk1  ->
                       let uu____66983 = thunk1 ()  in
                       readback_residual_comp cfg uu____66983)
                   in
                FStar_Syntax_Util.abs (FStar_List.rev args_rev) body
                  uu____66972)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____67011 =
               let uu____67012 =
                 let uu____67013 = targ ()  in
                 FStar_Pervasives_Native.fst uu____67013  in
               readback cfg uu____67012  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____67011
              in
           let body =
             let uu____67019 =
               let uu____67020 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____67020  in
             readback cfg uu____67019  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t  in FStar_Syntax_Util.mk_reflect tm
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____67057 =
             FStar_List.fold_left
               (fun uu____67100  ->
                  fun tf  ->
                    match uu____67100 with
                    | (args_rev,accus_rev) ->
                        let uu____67152 = tf accus_rev  in
                        (match uu____67152 with
                         | (xt,q) ->
                             let x1 =
                               let uu____67172 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____67172
                                in
                             let uu____67173 =
                               let uu____67176 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____67176 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____67173))) ([], [])
               targs
              in
           (match uu____67057 with
            | (args_rev,accus_rev) ->
                let cmp =
                  let uu____67220 = f (FStar_List.rev accus_rev)  in
                  readback_comp cfg uu____67220  in
                FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____67263  ->
                  match uu____67263 with
                  | (x1,q) ->
                      let uu____67274 = readback cfg x1  in (uu____67274, q))
               args
              in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____67293 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____67300::uu____67301 ->
                let uu____67304 =
                  let uu____67307 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____67307
                    (FStar_List.rev us)
                   in
                apply1 uu____67304
            | [] ->
                let uu____67308 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply1 uu____67308)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____67349  ->
                  match uu____67349 with
                  | (x1,q) ->
                      let uu____67360 = readback cfg x1  in (uu____67360, q))
               args
              in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____67379 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____67386::uu____67387 ->
                let uu____67390 =
                  let uu____67393 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____67393
                    (FStar_List.rev us)
                   in
                apply1 uu____67390
            | [] ->
                let uu____67394 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply1 uu____67394)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____67441  ->
                  match uu____67441 with
                  | (x1,q) ->
                      let uu____67452 = readback cfg x1  in (uu____67452, q))
               ts
              in
           let uu____67453 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____67453 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____67513  ->
                  match uu____67513 with
                  | (x1,q) ->
                      let uu____67524 = readback cfg x1  in (uu____67524, q))
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
            | uu____67554 -> FStar_Syntax_Util.mk_app head1 args)
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
               (fun uu____67641  ->
                  match uu____67641 with
                  | (x1,q) ->
                      let uu____67652 = readback cfg x1  in (uu____67652, q))
               args
              in
           (match args1 with
            | [] -> head1
            | uu____67657 -> FStar_Syntax_Util.mk_app head1 args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____67669) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (uu____67686,thunk1) ->
           let uu____67708 = FStar_Common.force_thunk thunk1  in
           readback cfg uu____67708)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____67737 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____67749 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____67770 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____67797 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____67821 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____67832 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___586_67839  ->
    match uu___586_67839 with
    | Primops  -> FStar_TypeChecker_Env.Primops
    | UnfoldUntil d -> FStar_TypeChecker_Env.UnfoldUntil d
    | UnfoldOnly lids -> FStar_TypeChecker_Env.UnfoldOnly lids
    | UnfoldAttr lids -> FStar_TypeChecker_Env.UnfoldAttr lids
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
            let uu___1832_67878 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1834_67881 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1834_67881.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1832_67878.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1832_67878.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1832_67878.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1832_67878.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1832_67878.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1832_67878.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1832_67878.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1832_67878.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____67886  ->
               let uu____67887 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with (%s) {\n" uu____67887);
          (let r =
             let uu____67891 = translate cfg1 [] e  in
             readback cfg1 uu____67891  in
           debug cfg1
             (fun uu____67895  ->
                let uu____67896 = FStar_Syntax_Print.term_to_string r  in
                FStar_Util.print1 "}\nNBE returned (%s)\n" uu____67896);
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
          let uu___1849_67921 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1851_67924 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1851_67924.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1849_67921.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1849_67921.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1849_67921.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1849_67921.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1849_67921.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1849_67921.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1849_67921.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1849_67921.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____67929  ->
             let uu____67930 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____67930);
        (let r =
           let uu____67934 = translate cfg1 [] e  in
           readback cfg1 uu____67934  in
         debug cfg1
           (fun uu____67938  ->
              let uu____67939 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____67939);
         r)
  