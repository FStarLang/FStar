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
            let uu____64596 = let uu____64599 = f x  in uu____64599 :: acc
               in
            aux xs uu____64596
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
              let uu____64670 = let uu____64673 = f x  in uu____64673 :: acc
                 in
              aux xs uu____64670
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
            let uu____64723 = f x  in
            let uu____64724 = map_append f xs l2  in uu____64723 ::
              uu____64724
  
let rec drop : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p  ->
    fun l  ->
      match l with
      | [] -> []
      | x::xs ->
          let uu____64763 = p x  in
          if uu____64763 then x :: xs else drop p xs
  
let fmap_opt :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun x  ->
      FStar_Util.bind_opt x
        (fun x1  ->
           let uu____64805 = f x1  in
           FStar_Pervasives_Native.Some uu____64805)
  
let drop_until : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 =
        match l1 with
        | [] -> []
        | x::xs ->
            let uu____64855 = f x  in if uu____64855 then l1 else aux xs
         in
      aux l
  
let (trim : Prims.bool Prims.list -> Prims.bool Prims.list) =
  fun l  ->
    let uu____64880 = drop_until FStar_Pervasives.id (FStar_List.rev l)  in
    FStar_List.rev uu____64880
  
let (implies : Prims.bool -> Prims.bool -> Prims.bool) =
  fun b1  ->
    fun b2  ->
      match (b1, b2) with | (false ,uu____64907) -> true | (true ,b21) -> b21
  
let (debug : FStar_TypeChecker_Cfg.cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____64934 =
        let uu____64936 = FStar_TypeChecker_Cfg.cfg_env cfg  in
        FStar_TypeChecker_Env.debug uu____64936 (FStar_Options.Other "NBE")
         in
      if uu____64934 then f () else ()
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____64947 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____64947
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____64968 = FStar_Syntax_Print.sigelt_to_string_short v1
                in
             FStar_Util.print2 "%s -> %%s\n" k uu____64968) ()
  
let (unlazy : FStar_TypeChecker_NBETerm.t -> FStar_TypeChecker_NBETerm.t) =
  fun t  ->
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (uu____64977,t1) ->
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
              (fun uu____65145  ->
                 let uu____65146 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0  in
                 let uu____65148 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____65146
                   uu____65148);
            (let scrutinee = unlazy scrutinee0  in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____65175 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____65202  ->
                          let uu____65203 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____65205 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n"
                            uu____65203 uu____65205);
                     (match c with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____65215 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____65232 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____65232
                           | uu____65233 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____65236))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____65241) ->
                               st = p1
                           | uu____65245 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____65253 -> false)
                      | uu____65255 -> false)
                      in
                   let uu____65257 = matches_const scrutinee s  in
                   if uu____65257
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____65395)::rest_a,(p2,uu____65398)::rest_p) ->
                         let uu____65437 = matches_pat t p2  in
                         (match uu____65437 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____65466 -> FStar_Util.Inr false  in
                   (match scrutinee with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____65514 = FStar_Syntax_Syntax.fv_eq fv fv'
                           in
                        if uu____65514
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____65534 -> FStar_Util.Inr true)
                in
             let res_to_string uu___585_65552 =
               match uu___585_65552 with
               | FStar_Util.Inr b ->
                   let uu____65566 = FStar_Util.string_of_bool b  in
                   Prims.op_Hat "Inr " uu____65566
               | FStar_Util.Inl bs ->
                   let uu____65575 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.op_Hat "Inl " uu____65575
                in
             debug cfg
               (fun uu____65583  ->
                  let uu____65584 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____65586 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____65588 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____65584
                    uu____65586 uu____65588);
             r)
             in
          match branches1 with
          | [] -> failwith "Branch not found"
          | (p,_wopt,e)::branches2 ->
              let uu____65630 = matches_pat scrut1 p  in
              (match uu____65630 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____65655  ->
                         let uu____65656 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____65656);
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
        | (uu____65824,[]) -> (true, (FStar_List.rev acc), ts1)
        | ([],uu____65859::uu____65860) -> (false, (FStar_List.rev acc), [])
        | (t::ts2,b::bs) ->
            let uu____65933 =
              res &&
                (let uu____65936 =
                   let uu____65938 =
                     FStar_TypeChecker_NBETerm.isAccu
                       (FStar_Pervasives_Native.fst t)
                      in
                   Prims.op_Negation uu____65938  in
                 implies b uu____65936)
               in
            aux ts2 bs (t :: acc) uu____65933
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
        let mapper uu____65994 =
          match uu____65994 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____66077  ->
                         let uu____66078 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____66078);
                    FStar_Pervasives_Native.Some elt)
               | uu____66081 -> FStar_Pervasives_Native.None)
           in
        let uu____66096 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____66096 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____66143 -> true
    | uu____66145 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | t ->
        let uu____66155 =
          let uu____66157 = FStar_TypeChecker_NBETerm.t_to_string t  in
          Prims.op_Hat "Not a universe: " uu____66157  in
        failwith uu____66155
  
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
              (uu____66179,uu____66180,uu____66181,uu____66182,uu____66183,uu____66184);
            FStar_Syntax_Syntax.sigrng = uu____66185;
            FStar_Syntax_Syntax.sigquals = uu____66186;
            FStar_Syntax_Syntax.sigmeta = uu____66187;
            FStar_Syntax_Syntax.sigattrs = uu____66188;_},uu____66189),uu____66190)
        -> true
    | uu____66248 -> false
  
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
            let uu____66280 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____66280
        | FStar_Syntax_Syntax.U_max us ->
            let uu____66284 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____66284
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____66287 -> u2
        | FStar_Syntax_Syntax.U_unif uu____66288 -> u2
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
           | FStar_Util.Inl uu____66319 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____66324 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____66324
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
              let uu____66677 = FStar_List.splitAt m targs  in
              (match uu____66677 with
               | (uu____66717,targs') ->
                   let targs'1 =
                     FStar_List.map
                       (fun targ  ->
                          fun l  ->
                            let uu____66808 =
                              let uu____66811 =
                                map_append FStar_Pervasives_Native.fst args l
                                 in
                              FStar_List.rev uu____66811  in
                            targ uu____66808) targs'
                      in
                   FStar_TypeChecker_NBETerm.Lam
                     (((fun l  ->
                          let uu____66845 =
                            map_append FStar_Pervasives_Native.fst args l  in
                          f1 uu____66845)), targs'1, (n1 - m), res))
            else
              if m = n1
              then
                (let uu____66864 =
                   FStar_List.map FStar_Pervasives_Native.fst args  in
                 f1 uu____66864)
              else
                (let uu____66873 = FStar_List.splitAt n1 args  in
                 match uu____66873 with
                 | (args1,args') ->
                     let uu____66920 =
                       let uu____66921 =
                         FStar_List.map FStar_Pervasives_Native.fst args1  in
                       f1 uu____66921  in
                     iapp cfg uu____66920 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____67040)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____67084 = aux args us ts  in
            (match uu____67084 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____67211)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____67255 = aux args us ts  in
            (match uu____67255 with
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
                 let uu____67429 = test_args full_args ar_lst  in
                 match uu____67429 with
                 | (can_unfold,args1,res) ->
                     if
                       Prims.op_Negation
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                     then
                       (debug cfg
                          (fun uu____67446  ->
                             let uu____67447 =
                               FStar_Syntax_Print.lbname_to_string
                                 lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Util.print1
                               "Zeta is not set; will not unfold %s\n"
                               uu____67447);
                        FStar_TypeChecker_NBETerm.Rec
                          (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                            ar_lst, tr_lb))
                     else
                       if can_unfold
                       then
                         (debug cfg
                            (fun uu____67479  ->
                               let uu____67480 =
                                 FStar_Syntax_Print.lbname_to_string
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               FStar_Util.print1
                                 "Beta reducing recursive function %s\n"
                                 uu____67480);
                          (match res with
                           | [] ->
                               let uu____67487 =
                                 let uu____67488 = make_rec_env tr_lb lbs bs
                                    in
                                 tr_lb uu____67488 lb  in
                               iapp cfg uu____67487 args1
                           | uu____67491::uu____67492 ->
                               let t =
                                 let uu____67508 =
                                   let uu____67509 =
                                     make_rec_env tr_lb lbs bs  in
                                   tr_lb uu____67509 lb  in
                                 iapp cfg uu____67508 args1  in
                               iapp cfg t res))
                       else
                         FStar_TypeChecker_NBETerm.Rec
                           (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                             ar_lst, tr_lb))
        | FStar_TypeChecker_NBETerm.Quote uu____67537 ->
            let uu____67542 =
              let uu____67544 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____67544  in
            failwith uu____67542
        | FStar_TypeChecker_NBETerm.Reflect uu____67547 ->
            let uu____67548 =
              let uu____67550 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____67550  in
            failwith uu____67548
        | FStar_TypeChecker_NBETerm.Lazy uu____67553 ->
            let uu____67568 =
              let uu____67570 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____67570  in
            failwith uu____67568
        | FStar_TypeChecker_NBETerm.Constant uu____67573 ->
            let uu____67574 =
              let uu____67576 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____67576  in
            failwith uu____67574
        | FStar_TypeChecker_NBETerm.Univ uu____67579 ->
            let uu____67580 =
              let uu____67582 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____67582  in
            failwith uu____67580
        | FStar_TypeChecker_NBETerm.Type_t uu____67585 ->
            let uu____67586 =
              let uu____67588 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____67588  in
            failwith uu____67586
        | FStar_TypeChecker_NBETerm.Unknown  ->
            let uu____67591 =
              let uu____67593 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____67593  in
            failwith uu____67591
        | FStar_TypeChecker_NBETerm.Refinement uu____67596 ->
            let uu____67611 =
              let uu____67613 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____67613  in
            failwith uu____67611
        | FStar_TypeChecker_NBETerm.Arrow uu____67616 ->
            let uu____67637 =
              let uu____67639 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____67639  in
            failwith uu____67637

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
          let uu____67656 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____67657 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____67656 uu____67657  in
        let uu____67658 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____67658
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____67667 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____67669  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____67667 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____67676  ->
                     let uu____67677 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____67677);
                (let uu____67680 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____67680 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____67691  ->
                           let uu____67692 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n"
                             uu____67692);
                      (let uu____67695 =
                         let uu____67726 =
                           let f uu____67754 uu____67755 =
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
                             let uu____67815 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 callbacks args'
                                in
                             match uu____67815 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____67826  ->
                                       let uu____67827 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____67829 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____67827 uu____67829);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____67837  ->
                                       let uu____67838 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____67838);
                                  (let uu____67841 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp cfg uu____67841 args'))),
                           uu____67726, arity, FStar_Pervasives_Native.None)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____67695))
                 | FStar_Pervasives_Native.Some uu____67849 ->
                     (debug1
                        (fun uu____67855  ->
                           let uu____67856 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____67856);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____67863 ->
                     (debug1
                        (fun uu____67871  ->
                           let uu____67872 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____67872);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____67882;
                        FStar_Syntax_Syntax.sigquals = uu____67883;
                        FStar_Syntax_Syntax.sigmeta = uu____67884;
                        FStar_Syntax_Syntax.sigattrs = uu____67885;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____67958  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____67968  ->
                                 let uu____67969 =
                                   let uu____67971 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____67971
                                    in
                                 let uu____67972 =
                                   let uu____67974 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____67974
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____67969 uu____67972);
                            debug1
                              (fun uu____67983  ->
                                 let uu____67984 =
                                   let uu____67986 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____67986
                                    in
                                 let uu____67987 =
                                   let uu____67989 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____67989
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____67984 uu____67987);
                            translate_letbinding cfg bs lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____67992 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____68000;
                        FStar_Syntax_Syntax.sigquals = uu____68001;
                        FStar_Syntax_Syntax.sigmeta = uu____68002;
                        FStar_Syntax_Syntax.sigattrs = uu____68003;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____68076  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____68086  ->
                                 let uu____68087 =
                                   let uu____68089 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____68089
                                    in
                                 let uu____68090 =
                                   let uu____68092 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____68092
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____68087 uu____68090);
                            debug1
                              (fun uu____68101  ->
                                 let uu____68102 =
                                   let uu____68104 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____68104
                                    in
                                 let uu____68105 =
                                   let uu____68107 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____68107
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____68102 uu____68105);
                            translate_letbinding cfg bs lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____68110 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        | uu____68155 ->
            let uu____68158 =
              let uu____68189 =
                FStar_List.map
                  (fun uu____68214  ->
                     fun _ts  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____68189,
                (FStar_List.length us), FStar_Pervasives_Native.None)
               in
            FStar_TypeChecker_NBETerm.Lam uu____68158

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
          let uu____68275 = FStar_Syntax_Util.let_rec_arity b  in
          match uu____68275 with
          | (ar,maybe_lst) ->
              let uu____68300 =
                match maybe_lst with
                | FStar_Pervasives_Native.None  ->
                    let uu____68320 =
                      FStar_Common.tabulate ar (fun uu____68326  -> true)  in
                    (ar, uu____68320)
                | FStar_Pervasives_Native.Some lst ->
                    let l = trim lst  in ((FStar_List.length l), l)
                 in
              (match uu____68300 with
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
              let uu____68453 =
                let uu____68456 = mkRec' callback lb lbs0 bs0  in uu____68456
                  :: bs1
                 in
              aux lbs' lbs0 uu____68453 bs0
           in
        aux lbs lbs bs bs

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____68473 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____68473
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____68482 ->
        let uu____68483 =
          let uu____68485 =
            let uu____68487 = FStar_Syntax_Print.const_to_string c  in
            Prims.op_Hat uu____68487 ": Not yet implemented"  in
          Prims.op_Hat "Tm_constant " uu____68485  in
        failwith uu____68483

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
          (fun uu____68511  ->
             let uu____68512 =
               let uu____68514 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____68514  in
             let uu____68515 =
               let uu____68517 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____68517  in
             FStar_Util.print2 "Term: %s - %s\n" uu____68512 uu____68515);
        debug1
          (fun uu____68524  ->
             let uu____68525 =
               let uu____68527 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____68527  in
             FStar_Util.print1 "BS list: %s\n" uu____68525);
        (let uu____68536 =
           let uu____68537 = FStar_Syntax_Subst.compress e  in
           uu____68537.FStar_Syntax_Syntax.n  in
         match uu____68536 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____68540,uu____68541) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____68580 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____68580
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then FStar_List.nth bs db.FStar_Syntax_Syntax.index
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____68599  ->
                   let uu____68600 = FStar_Syntax_Print.term_to_string t  in
                   let uu____68602 =
                     let uu____68604 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____68604
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____68600 uu____68602);
              (let uu____68615 = translate cfg bs t  in
               let uu____68616 =
                 FStar_List.map
                   (fun x  ->
                      let uu____68620 =
                        let uu____68621 = translate_univ bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____68621  in
                      FStar_TypeChecker_NBETerm.as_arg uu____68620) us
                  in
               iapp cfg uu____68615 uu____68616))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____68623 = translate_univ bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____68623
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____68646 =
               let uu____68667 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____68737 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____68737, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____68667)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____68646
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____68806  ->
                     let uu____68807 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____68807)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____68809,uu____68810) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____68872,uu____68873) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             let uu____68924 =
               let uu____68955 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____69025 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____69025, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               let uu____69054 =
                 FStar_Util.map_opt resc
                   (fun c  ->
                      fun uu____69066  -> translate_residual_comp cfg bs c)
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____68955, (FStar_List.length xs), uu____69054)
                in
             FStar_TypeChecker_NBETerm.Lam uu____68924
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____69100;
                FStar_Syntax_Syntax.vars = uu____69101;_},arg::more::args)
             ->
             let uu____69161 = FStar_Syntax_Util.head_and_args e  in
             (match uu____69161 with
              | (head1,uu____69179) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____69223 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____69223)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____69232);
                FStar_Syntax_Syntax.pos = uu____69233;
                FStar_Syntax_Syntax.vars = uu____69234;_},arg::more::args)
             ->
             let uu____69294 = FStar_Syntax_Util.head_and_args e  in
             (match uu____69294 with
              | (head1,uu____69312) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____69356 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____69356)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____69365);
                FStar_Syntax_Syntax.pos = uu____69366;
                FStar_Syntax_Syntax.vars = uu____69367;_},arg::[])
             when cfg.FStar_TypeChecker_Cfg.reifying ->
             let cfg1 =
               let uu___1234_69408 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___1234_69408.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___1234_69408.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___1234_69408.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___1234_69408.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___1234_69408.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___1234_69408.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___1234_69408.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___1234_69408.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = false
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____69414);
                FStar_Syntax_Syntax.pos = uu____69415;
                FStar_Syntax_Syntax.vars = uu____69416;_},arg::[])
             ->
             let uu____69456 =
               translate cfg bs (FStar_Pervasives_Native.fst arg)  in
             FStar_TypeChecker_NBETerm.Reflect uu____69456
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____69461;
                FStar_Syntax_Syntax.vars = uu____69462;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___1257_69504 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___1257_69504.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___1257_69504.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___1257_69504.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___1257_69504.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___1257_69504.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___1257_69504.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___1257_69504.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___1257_69504.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____69543  ->
                   let uu____69544 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____69546 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____69544
                     uu____69546);
              (let uu____69549 = translate cfg bs head1  in
               let uu____69550 =
                 FStar_List.map
                   (fun x  ->
                      let uu____69572 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____69572, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____69549 uu____69550))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches readback1 =
               let cfg1 =
                 let uu___1273_69633 = cfg  in
                 {
                   FStar_TypeChecker_Cfg.steps =
                     (let uu___1275_69636 = cfg.FStar_TypeChecker_Cfg.steps
                         in
                      {
                        FStar_TypeChecker_Cfg.beta =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.beta);
                        FStar_TypeChecker_Cfg.iota =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.iota);
                        FStar_TypeChecker_Cfg.zeta = false;
                        FStar_TypeChecker_Cfg.weak =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.weak);
                        FStar_TypeChecker_Cfg.hnf =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.hnf);
                        FStar_TypeChecker_Cfg.primops =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.primops);
                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                        FStar_TypeChecker_Cfg.unfold_until =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.unfold_until);
                        FStar_TypeChecker_Cfg.unfold_only =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.unfold_only);
                        FStar_TypeChecker_Cfg.unfold_fully =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.unfold_fully);
                        FStar_TypeChecker_Cfg.unfold_attr =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.unfold_attr);
                        FStar_TypeChecker_Cfg.unfold_tac =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.unfold_tac);
                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                          =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                        FStar_TypeChecker_Cfg.simplify =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.simplify);
                        FStar_TypeChecker_Cfg.erase_universes =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.erase_universes);
                        FStar_TypeChecker_Cfg.allow_unbound_universes =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.allow_unbound_universes);
                        FStar_TypeChecker_Cfg.reify_ =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.reify_);
                        FStar_TypeChecker_Cfg.compress_uvars =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.compress_uvars);
                        FStar_TypeChecker_Cfg.no_full_norm =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.no_full_norm);
                        FStar_TypeChecker_Cfg.check_no_uvars =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.check_no_uvars);
                        FStar_TypeChecker_Cfg.unmeta =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.unmeta);
                        FStar_TypeChecker_Cfg.unascribe =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.unascribe);
                        FStar_TypeChecker_Cfg.in_full_norm_request =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.in_full_norm_request);
                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                        FStar_TypeChecker_Cfg.nbe_step =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.nbe_step);
                        FStar_TypeChecker_Cfg.for_extraction =
                          (uu___1275_69636.FStar_TypeChecker_Cfg.for_extraction)
                      });
                   FStar_TypeChecker_Cfg.tcenv =
                     (uu___1273_69633.FStar_TypeChecker_Cfg.tcenv);
                   FStar_TypeChecker_Cfg.debug =
                     (uu___1273_69633.FStar_TypeChecker_Cfg.debug);
                   FStar_TypeChecker_Cfg.delta_level =
                     (uu___1273_69633.FStar_TypeChecker_Cfg.delta_level);
                   FStar_TypeChecker_Cfg.primitive_steps =
                     (uu___1273_69633.FStar_TypeChecker_Cfg.primitive_steps);
                   FStar_TypeChecker_Cfg.strong =
                     (uu___1273_69633.FStar_TypeChecker_Cfg.strong);
                   FStar_TypeChecker_Cfg.memoize_lazy =
                     (uu___1273_69633.FStar_TypeChecker_Cfg.memoize_lazy);
                   FStar_TypeChecker_Cfg.normalize_pure_lets =
                     (uu___1273_69633.FStar_TypeChecker_Cfg.normalize_pure_lets);
                   FStar_TypeChecker_Cfg.reifying =
                     (uu___1273_69633.FStar_TypeChecker_Cfg.reifying)
                 }  in
               let rec process_pattern bs1 p =
                 let uu____69665 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____69701 =
                         FStar_List.fold_left
                           (fun uu____69742  ->
                              fun uu____69743  ->
                                match (uu____69742, uu____69743) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____69835 = process_pattern bs2 arg
                                       in
                                    (match uu____69835 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____69701 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____69934 =
                           let uu____69935 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____69935  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____69934
                          in
                       let uu____69936 =
                         let uu____69939 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____69939 :: bs1  in
                       (uu____69936, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____69944 =
                           let uu____69945 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____69945  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____69944
                          in
                       let uu____69946 =
                         let uu____69949 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____69949 :: bs1  in
                       (uu____69946, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____69959 =
                           let uu____69960 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____69960  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____69959
                          in
                       let uu____69961 =
                         let uu____69962 =
                           let uu____69969 =
                             let uu____69972 = translate cfg1 bs1 tm  in
                             readback1 uu____69972  in
                           (x, uu____69969)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____69962  in
                       (bs1, uu____69961)
                    in
                 match uu____69665 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___1313_69992 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___1313_69992.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____70011  ->
                    match uu____70011 with
                    | (pat,when_clause,e1) ->
                        let uu____70033 = process_pattern bs pat  in
                        (match uu____70033 with
                         | (bs',pat') ->
                             let uu____70046 =
                               let uu____70047 =
                                 let uu____70050 = translate cfg1 bs' e1  in
                                 readback1 uu____70050  in
                               (pat', when_clause, uu____70047)  in
                             FStar_Syntax_Util.branch uu____70046)) branches
                in
             let rec case scrut1 =
               debug1
                 (fun uu____70072  ->
                    let uu____70073 =
                      let uu____70075 = readback cfg scrut1  in
                      FStar_Syntax_Print.term_to_string uu____70075  in
                    let uu____70076 =
                      FStar_TypeChecker_NBETerm.t_to_string scrut1  in
                    FStar_Util.print2 "Match case: (%s) -- (%s)\n"
                      uu____70073 uu____70076);
               (let scrut2 = unlazy scrut1  in
                match scrut2 with
                | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                    (debug1
                       (fun uu____70104  ->
                          let uu____70105 =
                            let uu____70107 =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____70133  ->
                                      match uu____70133 with
                                      | (x,q) ->
                                          let uu____70147 =
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              x
                                             in
                                          Prims.op_Hat
                                            (if FStar_Util.is_some q
                                             then "#"
                                             else "") uu____70147))
                               in
                            FStar_All.pipe_right uu____70107
                              (FStar_String.concat "; ")
                             in
                          FStar_Util.print1 "Match args: %s\n" uu____70105);
                     (let uu____70161 = pickBranch cfg scrut2 branches  in
                      match uu____70161 with
                      | FStar_Pervasives_Native.Some (branch1,args1) ->
                          let uu____70182 =
                            FStar_List.fold_left
                              (fun bs1  -> fun x  -> x :: bs1) bs args1
                             in
                          translate cfg uu____70182 branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                            make_branches))
                | FStar_TypeChecker_NBETerm.Constant c ->
                    (debug1
                       (fun uu____70205  ->
                          let uu____70206 =
                            FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                          FStar_Util.print1 "Match constant : %s\n"
                            uu____70206);
                     (let uu____70209 = pickBranch cfg scrut2 branches  in
                      match uu____70209 with
                      | FStar_Pervasives_Native.Some (branch1,[]) ->
                          translate cfg bs branch1
                      | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                          translate cfg (arg :: bs) branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                            make_branches
                      | FStar_Pervasives_Native.Some (uu____70243,hd1::tl1)
                          ->
                          failwith
                            "Impossible: Matching on constants cannot bind more than one variable"))
                | uu____70257 ->
                    FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                      make_branches)
                in
             let uu____70258 = translate cfg bs scrut  in case uu____70258
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
             let uu____70337 = make_rec_env (translate_letbinding cfg) lbs bs
                in
             translate cfg uu____70337 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____70341) ->
             translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____70362  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____70375 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____70390  ->
                      match uu____70390 with
                      | (bv,t1) ->
                          let uu____70397 =
                            let uu____70404 = readback cfg t1  in
                            (bv, uu____70404)  in
                          FStar_Syntax_Syntax.NT uu____70397) uu____70375
                  in
               let uu____70409 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____70409  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close1 qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close1 qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu____70418 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____70425  ->
                    let uu____70426 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____70426);
               translate cfg bs t  in
             let uu____70429 =
               let uu____70444 = FStar_Common.mk_thunk f  in
               ((FStar_Util.Inl li), uu____70444)  in
             FStar_TypeChecker_NBETerm.Lazy uu____70429)

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
            let uu____70516 =
              let uu____70523 = translate cfg bs typ  in
              let uu____70524 = fmap_opt (translate_univ bs) u  in
              (uu____70523, uu____70524)  in
            FStar_TypeChecker_NBETerm.Tot uu____70516
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____70539 =
              let uu____70546 = translate cfg bs typ  in
              let uu____70547 = fmap_opt (translate_univ bs) u  in
              (uu____70546, uu____70547)  in
            FStar_TypeChecker_NBETerm.GTot uu____70539
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____70553 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____70553

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____70563 =
              let uu____70572 = readback cfg typ  in (uu____70572, u)  in
            FStar_Syntax_Syntax.Total uu____70563
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____70585 =
              let uu____70594 = readback cfg typ  in (uu____70594, u)  in
            FStar_Syntax_Syntax.GTotal uu____70585
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____70602 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____70602
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
        let uu____70608 = c  in
        match uu____70608 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____70628 = FStar_List.map (translate_univ bs) comp_univs
               in
            let uu____70629 = translate cfg bs result_typ  in
            let uu____70630 =
              FStar_List.map
                (fun x  ->
                   let uu____70658 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____70658, (FStar_Pervasives_Native.snd x)))
                effect_args
               in
            let uu____70665 = FStar_List.map (translate_flag cfg bs) flags
               in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____70628;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____70629;
              FStar_TypeChecker_NBETerm.effect_args = uu____70630;
              FStar_TypeChecker_NBETerm.flags = uu____70665
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____70670 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____70673 =
        FStar_List.map
          (fun x  ->
             let uu____70699 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____70699, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____70700 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____70670;
        FStar_Syntax_Syntax.effect_args = uu____70673;
        FStar_Syntax_Syntax.flags = uu____70700
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
        let uu____70708 = c  in
        match uu____70708 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____70718 =
              FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____70723 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____70718;
              FStar_TypeChecker_NBETerm.residual_flags = uu____70723
            }

and (readback_residual_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____70728 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (readback cfg)
         in
      let uu____70735 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____70728;
        FStar_Syntax_Syntax.residual_flags = uu____70735
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
            let uu____70746 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____70746

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
          let uu____70750 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____70750

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____70753  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____70753 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____70791 =
                     let uu____70800 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____70800
                      in
                   (match uu____70791 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____70807 =
                          let uu____70809 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____70809
                           in
                        failwith uu____70807
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___1521_70825 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___1521_70825.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___1521_70825.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___1521_70825.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___1521_70825.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___1521_70825.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___1521_70825.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___1521_70825.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___1521_70825.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____70833 =
                            let uu____70840 =
                              let uu____70841 =
                                let uu____70860 =
                                  let uu____70869 =
                                    let uu____70876 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____70876,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____70869]  in
                                (uu____70860, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____70841  in
                            FStar_Syntax_Syntax.mk uu____70840  in
                          uu____70833 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____70913 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____70913
                          then
                            let uu____70922 =
                              let uu____70927 =
                                let uu____70928 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____70928  in
                              (uu____70927, FStar_Pervasives_Native.None)  in
                            let uu____70929 =
                              let uu____70936 =
                                let uu____70941 =
                                  let uu____70942 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____70942  in
                                (uu____70941, FStar_Pervasives_Native.None)
                                 in
                              [uu____70936]  in
                            uu____70922 :: uu____70929
                          else []  in
                        let t =
                          let uu____70962 =
                            let uu____70963 =
                              let uu____70964 =
                                FStar_Syntax_Util.un_uinst
                                  (FStar_Pervasives_Native.snd
                                     ed.FStar_Syntax_Syntax.bind_repr)
                                 in
                              translate cfg' [] uu____70964  in
                            iapp cfg uu____70963
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____70981 =
                            let uu____70982 =
                              let uu____70989 =
                                let uu____70994 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____70994, FStar_Pervasives_Native.None)
                                 in
                              let uu____70995 =
                                let uu____71002 =
                                  let uu____71007 = translate cfg' bs ty  in
                                  (uu____71007, FStar_Pervasives_Native.None)
                                   in
                                [uu____71002]  in
                              uu____70989 :: uu____70995  in
                            let uu____71020 =
                              let uu____71027 =
                                let uu____71034 =
                                  let uu____71041 =
                                    let uu____71046 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____71046,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____71047 =
                                    let uu____71054 =
                                      let uu____71061 =
                                        let uu____71066 =
                                          translate cfg bs body_lam  in
                                        (uu____71066,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____71061]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____71054
                                     in
                                  uu____71041 :: uu____71047  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) ::
                                  uu____71034
                                 in
                              FStar_List.append maybe_range_arg uu____71027
                               in
                            FStar_List.append uu____70982 uu____71020  in
                          iapp cfg uu____70962 uu____70981  in
                        (debug cfg
                           (fun uu____71098  ->
                              let uu____71099 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____71099);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____71102);
                      FStar_Syntax_Syntax.pos = uu____71103;
                      FStar_Syntax_Syntax.vars = uu____71104;_},(e2,uu____71106)::[])
                   ->
                   translate
                     (let uu___1543_71147 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___1543_71147.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1543_71147.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1543_71147.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___1543_71147.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1543_71147.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1543_71147.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1543_71147.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___1543_71147.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   (debug cfg
                      (fun uu____71179  ->
                         let uu____71180 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____71182 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____71180
                           uu____71182);
                    (let fallback1 uu____71190 = translate cfg bs e1  in
                     let fallback2 uu____71196 =
                       let uu____71197 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           FStar_Pervasives_Native.None
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate
                         (let uu___1555_71204 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___1555_71204.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___1555_71204.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___1555_71204.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___1555_71204.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___1555_71204.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___1555_71204.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___1555_71204.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___1555_71204.FStar_TypeChecker_Cfg.normalize_pure_lets);
                            FStar_TypeChecker_Cfg.reifying = false
                          }) bs uu____71197
                        in
                     let uu____71206 =
                       let uu____71207 = FStar_Syntax_Util.un_uinst head1  in
                       uu____71207.FStar_Syntax_Syntax.n  in
                     match uu____71206 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             cfg.FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____71213 =
                           let uu____71215 =
                             FStar_TypeChecker_Env.is_action
                               cfg.FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____71215  in
                         if uu____71213
                         then fallback1 ()
                         else
                           (let uu____71220 =
                              let uu____71222 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  cfg.FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____71222  in
                            if uu____71220
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____71239 =
                                   let uu____71244 =
                                     FStar_Syntax_Util.mk_reify head1  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____71244
                                     args
                                    in
                                 uu____71239 FStar_Pervasives_Native.None
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               translate
                                 (let uu___1564_71249 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1564_71249.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1564_71249.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1564_71249.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1564_71249.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1564_71249.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong =
                                      (uu___1564_71249.FStar_TypeChecker_Cfg.strong);
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1564_71249.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1564_71249.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying = false
                                  }) bs e2))
                     | uu____71251 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____71372  ->
                             match uu____71372 with
                             | (pat,wopt,tm) ->
                                 let uu____71420 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____71420)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   translate
                     (let uu___1577_71454 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___1577_71454.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1577_71454.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1577_71454.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___1577_71454.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1577_71454.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1577_71454.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1577_71454.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___1577_71454.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____71457) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____71484 ->
                   let uu____71485 =
                     let uu____71487 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____71487
                      in
                   failwith uu____71485)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____71490  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____71490 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____71514 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____71514
              then
                let ed =
                  let uu____71518 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____71518
                   in
                let ret1 =
                  let uu____71520 =
                    let uu____71521 =
                      FStar_Syntax_Subst.compress
                        (FStar_Pervasives_Native.snd
                           ed.FStar_Syntax_Syntax.return_repr)
                       in
                    uu____71521.FStar_Syntax_Syntax.n  in
                  match uu____71520 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret1,uu____71529::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret1, [FStar_Syntax_Syntax.U_unknown]))
                        FStar_Pervasives_Native.None
                        e1.FStar_Syntax_Syntax.pos
                  | uu____71536 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' =
                  let uu___1610_71539 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___1610_71539.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1610_71539.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1610_71539.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___1610_71539.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1610_71539.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1610_71539.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1610_71539.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1610_71539.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let t =
                  let uu____71542 =
                    let uu____71543 = translate cfg' [] ret1  in
                    iapp cfg' uu____71543
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____71552 =
                    let uu____71553 =
                      let uu____71558 = translate cfg' bs ty  in
                      (uu____71558, FStar_Pervasives_Native.None)  in
                    let uu____71559 =
                      let uu____71566 =
                        let uu____71571 = translate cfg' bs e1  in
                        (uu____71571, FStar_Pervasives_Native.None)  in
                      [uu____71566]  in
                    uu____71553 :: uu____71559  in
                  iapp cfg' uu____71542 uu____71552  in
                (debug cfg
                   (fun uu____71587  ->
                      let uu____71588 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____71588);
                 t)
              else
                (let uu____71593 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____71593 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____71596 =
                       let uu____71598 = FStar_Ident.text_of_lid msrc  in
                       let uu____71600 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____71598 uu____71600
                        in
                     failwith uu____71596
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____71603;
                       FStar_TypeChecker_Env.mtarget = uu____71604;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____71605;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____71627 =
                       let uu____71629 = FStar_Ident.text_of_lid msrc  in
                       let uu____71631 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____71629 uu____71631
                        in
                     failwith uu____71627
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____71634;
                       FStar_TypeChecker_Env.mtarget = uu____71635;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____71636;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____71675 =
                         let uu____71678 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____71678
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____71675
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___1634_71694 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___1634_71694.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1634_71694.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1634_71694.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___1634_71694.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1634_71694.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1634_71694.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1634_71694.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___1634_71694.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let t =
                       let uu____71697 = translate cfg' [] lift_lam  in
                       let uu____71698 =
                         let uu____71699 =
                           let uu____71704 = translate cfg bs e1  in
                           (uu____71704, FStar_Pervasives_Native.None)  in
                         [uu____71699]  in
                       iapp cfg uu____71697 uu____71698  in
                     (debug cfg
                        (fun uu____71716  ->
                           let uu____71717 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____71717);
                      t))

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____71735  ->
           let uu____71736 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____71736);
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
           let uu____71744 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____71744 FStar_Syntax_Util.exp_int
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
           let uu____71804 =
             FStar_List.fold_left
               (fun uu____71847  ->
                  fun tf  ->
                    match uu____71847 with
                    | (args_rev,accus_rev) ->
                        let uu____71899 = tf accus_rev  in
                        (match uu____71899 with
                         | (xt,q) ->
                             let x1 =
                               let uu____71919 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____71919
                                in
                             let uu____71920 =
                               let uu____71923 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____71923 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____71920))) ([], [])
               targs
              in
           (match uu____71804 with
            | (args_rev,accus_rev) ->
                let body =
                  let uu____71967 = f (FStar_List.rev accus_rev)  in
                  readback cfg uu____71967  in
                let uu____71968 =
                  FStar_Util.map_opt resc
                    (fun thunk1  ->
                       let uu____71979 = thunk1 ()  in
                       readback_residual_comp cfg uu____71979)
                   in
                FStar_Syntax_Util.abs (FStar_List.rev args_rev) body
                  uu____71968)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____72007 =
               let uu____72008 =
                 let uu____72009 = targ ()  in
                 FStar_Pervasives_Native.fst uu____72009  in
               readback cfg uu____72008  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____72007
              in
           let body =
             let uu____72015 =
               let uu____72016 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____72016  in
             readback cfg uu____72015  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t  in FStar_Syntax_Util.mk_reflect tm
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____72053 =
             FStar_List.fold_left
               (fun uu____72096  ->
                  fun tf  ->
                    match uu____72096 with
                    | (args_rev,accus_rev) ->
                        let uu____72148 = tf accus_rev  in
                        (match uu____72148 with
                         | (xt,q) ->
                             let x1 =
                               let uu____72168 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____72168
                                in
                             let uu____72169 =
                               let uu____72172 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____72172 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____72169))) ([], [])
               targs
              in
           (match uu____72053 with
            | (args_rev,accus_rev) ->
                let cmp =
                  let uu____72216 = f (FStar_List.rev accus_rev)  in
                  readback_comp cfg uu____72216  in
                FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____72259  ->
                  match uu____72259 with
                  | (x1,q) ->
                      let uu____72270 = readback cfg x1  in (uu____72270, q))
               args
              in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____72289 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____72296::uu____72297 ->
                let uu____72300 =
                  let uu____72303 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____72303
                    (FStar_List.rev us)
                   in
                apply1 uu____72300
            | [] ->
                let uu____72304 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply1 uu____72304)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____72345  ->
                  match uu____72345 with
                  | (x1,q) ->
                      let uu____72356 = readback cfg x1  in (uu____72356, q))
               args
              in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____72375 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____72382::uu____72383 ->
                let uu____72386 =
                  let uu____72389 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____72389
                    (FStar_List.rev us)
                   in
                apply1 uu____72386
            | [] ->
                let uu____72390 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply1 uu____72390)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____72437  ->
                  match uu____72437 with
                  | (x1,q) ->
                      let uu____72448 = readback cfg x1  in (uu____72448, q))
               ts
              in
           let uu____72449 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____72449 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____72509  ->
                  match uu____72509 with
                  | (x1,q) ->
                      let uu____72520 = readback cfg x1  in (uu____72520, q))
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
            | uu____72550 -> FStar_Syntax_Util.mk_app head1 args)
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
               (fun uu____72637  ->
                  match uu____72637 with
                  | (x1,q) ->
                      let uu____72648 = readback cfg x1  in (uu____72648, q))
               args
              in
           (match args1 with
            | [] -> head1
            | uu____72653 -> FStar_Syntax_Util.mk_app head1 args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____72665) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (uu____72682,thunk1) ->
           let uu____72704 = FStar_Common.force_thunk thunk1  in
           readback cfg uu____72704)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____72773 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____72785 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____72807 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____72835 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____72860 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____72871 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___586_72878  ->
    match uu___586_72878 with
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
            let uu___1832_72917 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1834_72920 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1834_72920.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1832_72917.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1832_72917.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1832_72917.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1832_72917.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1832_72917.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1832_72917.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1832_72917.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1832_72917.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____72925  ->
               let uu____72926 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with (%s) {\n" uu____72926);
          (let r =
             let uu____72930 = translate cfg1 [] e  in
             readback cfg1 uu____72930  in
           debug cfg1
             (fun uu____72934  ->
                let uu____72935 = FStar_Syntax_Print.term_to_string r  in
                FStar_Util.print1 "}\nNBE returned (%s)\n" uu____72935);
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
          let uu___1849_72960 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1851_72963 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1851_72963.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1849_72960.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1849_72960.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1849_72960.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1849_72960.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1849_72960.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1849_72960.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1849_72960.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1849_72960.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____72968  ->
             let uu____72969 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____72969);
        (let r =
           let uu____72973 = translate cfg1 [] e  in
           readback cfg1 uu____72973  in
         debug cfg1
           (fun uu____72977  ->
              let uu____72978 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____72978);
         r)
  