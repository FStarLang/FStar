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
            let uu____78 = let uu____81 = f x  in uu____81 :: acc  in
            aux xs uu____78
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
              let uu____152 = let uu____155 = f x  in uu____155 :: acc  in
              aux xs uu____152
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
            let uu____205 = f x  in
            let uu____206 = map_append f xs l2  in uu____205 :: uu____206
  
let rec drop : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p  ->
    fun l  ->
      match l with
      | [] -> []
      | x::xs ->
          let uu____245 = p x  in if uu____245 then x :: xs else drop p xs
  
let fmap_opt :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun x  ->
      FStar_Util.bind_opt x
        (fun x1  ->
           let uu____287 = f x1  in FStar_Pervasives_Native.Some uu____287)
  
let drop_until : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 =
        match l1 with
        | [] -> []
        | x::xs -> let uu____337 = f x  in if uu____337 then l1 else aux xs
         in
      aux l
  
let (trim : Prims.bool Prims.list -> Prims.bool Prims.list) =
  fun l  ->
    let uu____362 = drop_until FStar_Pervasives.id (FStar_List.rev l)  in
    FStar_List.rev uu____362
  
let (implies : Prims.bool -> Prims.bool -> Prims.bool) =
  fun b1  ->
    fun b2  ->
      match (b1, b2) with | (false ,uu____389) -> true | (true ,b21) -> b21
  
let (debug : FStar_TypeChecker_Cfg.cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____486 =
        let uu____488 = FStar_TypeChecker_Cfg.cfg_env cfg  in
        FStar_TypeChecker_Env.debug uu____488 (FStar_Options.Other "NBE")  in
      if uu____486 then f () else ()
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____615 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____615
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____656 = FStar_Syntax_Print.sigelt_to_string_short v1  in
             FStar_Util.print2 "%s -> %%s\n" k uu____656) ()
  
let (unlazy : FStar_TypeChecker_NBETerm.t -> FStar_TypeChecker_NBETerm.t) =
  fun t  ->
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (uu____665,t1) ->
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
              (fun uu____887  ->
                 let uu____888 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0  in
                 let uu____890 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____888
                   uu____890);
            (let scrutinee = unlazy scrutinee0  in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____927 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____963  ->
                          let uu____964 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____966 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu____964
                            uu____966);
                     (match c with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____976 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____993 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____993
                           | uu____994 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____997))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____1002) ->
                               st = p1
                           | uu____1006 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____1014 -> false)
                      | uu____1016 -> false)
                      in
                   let uu____1018 = matches_const scrutinee s  in
                   if uu____1018
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____1168)::rest_a,(p2,uu____1171)::rest_p) ->
                         let uu____1210 = matches_pat t p2  in
                         (match uu____1210 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____1239 -> FStar_Util.Inr false  in
                   (match scrutinee with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____1293 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                        if uu____1293
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____1313 -> FStar_Util.Inr true)
                in
             let res_to_string uu___0_1331 =
               match uu___0_1331 with
               | FStar_Util.Inr b ->
                   let uu____1345 = FStar_Util.string_of_bool b  in
                   Prims.op_Hat "Inr " uu____1345
               | FStar_Util.Inl bs ->
                   let uu____1354 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.op_Hat "Inl " uu____1354
                in
             debug cfg
               (fun uu____1362  ->
                  let uu____1363 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____1365 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____1367 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____1363
                    uu____1365 uu____1367);
             r)
             in
          match branches1 with
          | [] -> failwith "Branch not found"
          | (p,_wopt,e)::branches2 ->
              let uu____1439 = matches_pat scrut1 p  in
              (match uu____1439 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____1468  ->
                         let uu____1469 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____1469);
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
        | (uu____1649,[]) -> (true, (FStar_List.rev acc), ts1)
        | ([],uu____1684::uu____1685) -> (false, (FStar_List.rev acc), [])
        | (t::ts2,b::bs) ->
            let uu____1758 =
              res &&
                (let uu____1761 =
                   let uu____1763 =
                     FStar_TypeChecker_NBETerm.isAccu
                       (FStar_Pervasives_Native.fst t)
                      in
                   Prims.op_Negation uu____1763  in
                 implies b uu____1761)
               in
            aux ts2 bs (t :: acc) uu____1758
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
        let mapper uu____2029 =
          match uu____2029 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____2192  ->
                         let uu____2193 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____2193);
                    FStar_Pervasives_Native.Some elt)
               | uu____2201 -> FStar_Pervasives_Native.None)
           in
        let uu____2230 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____2230 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____2300 -> true
    | uu____2302 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | t ->
        let uu____2312 =
          let uu____2314 = FStar_TypeChecker_NBETerm.t_to_string t  in
          Prims.op_Hat "Not a universe: " uu____2314  in
        failwith uu____2312
  
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
              (uu____2342,uu____2343,uu____2344,uu____2345,uu____2346,uu____2347);
            FStar_Syntax_Syntax.sigrng = uu____2348;
            FStar_Syntax_Syntax.sigquals = uu____2349;
            FStar_Syntax_Syntax.sigmeta = uu____2350;
            FStar_Syntax_Syntax.sigattrs = uu____2351;_},uu____2352),uu____2353)
        -> true
    | uu____2481 -> false
  
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
            let uu____2513 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2513
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2517 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2517
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____2520 -> u2
        | FStar_Syntax_Syntax.U_unif uu____2523 -> u2
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
           | FStar_Util.Inl uu____2611 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____2647 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____2647
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
              let uu____3775 = FStar_List.splitAt m targs  in
              (match uu____3775 with
               | (uu____3811,targs') ->
                   let targs'1 =
                     FStar_List.map
                       (fun targ  ->
                          fun l  ->
                            let uu____3902 =
                              let uu____3905 =
                                map_append FStar_Pervasives_Native.fst args l
                                 in
                              FStar_List.rev uu____3905  in
                            targ uu____3902) targs'
                      in
                   FStar_TypeChecker_NBETerm.Lam
                     (((fun l  ->
                          let uu____3946 =
                            map_append FStar_Pervasives_Native.fst args l  in
                          f1 uu____3946)), targs'1, (n1 - m), res))
            else
              if m = n1
              then
                (let uu____3957 =
                   FStar_List.map FStar_Pervasives_Native.fst args  in
                 f1 uu____3957)
              else
                (let uu____3966 = FStar_List.splitAt n1 args  in
                 match uu____3966 with
                 | (args1,args') ->
                     let uu____4013 =
                       let uu____4014 =
                         FStar_List.map FStar_Pervasives_Native.fst args1  in
                       f1 uu____4014  in
                     iapp cfg uu____4013 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____4139)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____4183 = aux args us ts  in
            (match uu____4183 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____4319)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____4363 = aux args us ts  in
            (match uu____4363 with
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
                 let uu____4616 = test_args full_args ar_lst  in
                 match uu____4616 with
                 | (can_unfold,args1,res) ->
                     if
                       Prims.op_Negation
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                     then
                       (debug cfg
                          (fun uu____4633  ->
                             let uu____4634 =
                               FStar_Syntax_Print.lbname_to_string
                                 lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Util.print1
                               "Zeta is not set; will not unfold %s\n"
                               uu____4634);
                        FStar_TypeChecker_NBETerm.Rec
                          (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                            ar_lst, tr_lb))
                     else
                       if can_unfold
                       then
                         (debug cfg
                            (fun uu____4687  ->
                               let uu____4688 =
                                 FStar_Syntax_Print.lbname_to_string
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               FStar_Util.print1
                                 "Beta reducing recursive function %s\n"
                                 uu____4688);
                          (match res with
                           | [] ->
                               let uu____4695 =
                                 let uu____4696 = make_rec_env tr_lb lbs bs
                                    in
                                 tr_lb uu____4696 lb  in
                               iapp cfg uu____4695 args1
                           | uu____4699::uu____4700 ->
                               let t =
                                 let uu____4716 =
                                   let uu____4717 = make_rec_env tr_lb lbs bs
                                      in
                                   tr_lb uu____4717 lb  in
                                 iapp cfg uu____4716 args1  in
                               iapp cfg t res))
                       else
                         FStar_TypeChecker_NBETerm.Rec
                           (lb, lbs, bs, full_args, (Prims.parse_int "0"),
                             ar_lst, tr_lb))
        | FStar_TypeChecker_NBETerm.Quote uu____4766 ->
            let uu____4777 =
              let uu____4779 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____4779  in
            failwith uu____4777
        | FStar_TypeChecker_NBETerm.Reflect uu____4782 ->
            let uu____4783 =
              let uu____4785 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____4785  in
            failwith uu____4783
        | FStar_TypeChecker_NBETerm.Lazy uu____4788 ->
            let uu____4807 =
              let uu____4809 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____4809  in
            failwith uu____4807
        | FStar_TypeChecker_NBETerm.Constant uu____4812 ->
            let uu____4813 =
              let uu____4815 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____4815  in
            failwith uu____4813
        | FStar_TypeChecker_NBETerm.Univ uu____4818 ->
            let uu____4819 =
              let uu____4821 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____4821  in
            failwith uu____4819
        | FStar_TypeChecker_NBETerm.Type_t uu____4824 ->
            let uu____4825 =
              let uu____4827 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____4827  in
            failwith uu____4825
        | FStar_TypeChecker_NBETerm.Unknown  ->
            let uu____4830 =
              let uu____4832 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____4832  in
            failwith uu____4830
        | FStar_TypeChecker_NBETerm.Refinement uu____4835 ->
            let uu____4850 =
              let uu____4852 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____4852  in
            failwith uu____4850
        | FStar_TypeChecker_NBETerm.Arrow uu____4855 ->
            let uu____4876 =
              let uu____4878 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____4878  in
            failwith uu____4876

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
          let uu____4933 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____5042 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____4933 uu____5042  in
        let uu____5051 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____5051
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____5060 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____5062  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____5060 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____5104  ->
                     let uu____5105 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____5105);
                (let uu____5108 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____5108 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____5155  ->
                           let uu____5156 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n" uu____5156);
                      (let uu____5159 =
                         let uu____5197 =
                           let f uu____5225 uu____5226 =
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
                             let uu____5301 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 callbacks args'
                                in
                             match uu____5301 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____5312  ->
                                       let uu____5313 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____5315 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____5313 uu____5315);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____5323  ->
                                       let uu____5324 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____5324);
                                  (let uu____5327 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp cfg uu____5327 args'))), uu____5197,
                           arity, FStar_Pervasives_Native.None)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____5159))
                 | FStar_Pervasives_Native.Some uu____5342 ->
                     (debug1
                        (fun uu____5372  ->
                           let uu____5373 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____5373);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____5380 ->
                     (debug1
                        (fun uu____5400  ->
                           let uu____5401 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____5401);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____5411;
                        FStar_Syntax_Syntax.sigquals = uu____5412;
                        FStar_Syntax_Syntax.sigmeta = uu____5413;
                        FStar_Syntax_Syntax.sigattrs = uu____5414;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____5575  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____5585  ->
                                 let uu____5586 =
                                   let uu____5588 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____5588
                                    in
                                 let uu____5597 =
                                   let uu____5599 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____5599
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____5586 uu____5597);
                            debug1
                              (fun uu____5616  ->
                                 let uu____5617 =
                                   let uu____5619 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____5619
                                    in
                                 let uu____5628 =
                                   let uu____5630 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____5630
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____5617 uu____5628);
                            translate_letbinding cfg bs lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____5648 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____5656;
                        FStar_Syntax_Syntax.sigquals = uu____5657;
                        FStar_Syntax_Syntax.sigmeta = uu____5658;
                        FStar_Syntax_Syntax.sigattrs = uu____5659;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then mkRec cfg lb [] []
                         else
                           (debug1
                              (fun uu____5820  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____5830  ->
                                 let uu____5831 =
                                   let uu____5833 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____5833
                                    in
                                 let uu____5842 =
                                   let uu____5844 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____5844
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____5831 uu____5842);
                            debug1
                              (fun uu____5861  ->
                                 let uu____5862 =
                                   let uu____5864 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____5864
                                    in
                                 let uu____5873 =
                                   let uu____5875 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____5875
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____5862 uu____5873);
                            translate_letbinding cfg bs lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____5893 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        | uu____5984 ->
            let uu____5989 =
              let uu____6027 =
                FStar_List.map
                  (fun uu____6054  ->
                     fun _ts  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____6027,
                (FStar_List.length us), FStar_Pervasives_Native.None)
               in
            FStar_TypeChecker_NBETerm.Lam uu____5989

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
          let uu____6154 = FStar_Syntax_Util.let_rec_arity b  in
          match uu____6154 with
          | (ar,maybe_lst) ->
              let uu____6179 =
                match maybe_lst with
                | FStar_Pervasives_Native.None  ->
                    let uu____6199 =
                      FStar_Common.tabulate ar (fun uu____6205  -> true)  in
                    (ar, uu____6199)
                | FStar_Pervasives_Native.Some lst ->
                    let l = trim lst  in ((FStar_List.length l), l)
                 in
              (match uu____6179 with
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
              let uu____6472 =
                let uu____6475 = mkRec' callback lb lbs0 bs0  in uu____6475
                  :: bs1
                 in
              aux lbs' lbs0 uu____6472 bs0
           in
        aux lbs lbs bs bs

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____6492 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____6492
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____6501 ->
        let uu____6502 =
          let uu____6504 =
            let uu____6506 = FStar_Syntax_Print.const_to_string c  in
            Prims.op_Hat uu____6506 ": Not yet implemented"  in
          Prims.op_Hat "Tm_constant " uu____6504  in
        failwith uu____6502

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
          (fun uu____6569  ->
             let uu____6570 =
               let uu____6572 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____6572  in
             let uu____6581 =
               let uu____6583 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____6583  in
             FStar_Util.print2 "Term: %s - %s\n" uu____6570 uu____6581);
        debug1
          (fun uu____6598  ->
             let uu____6599 =
               let uu____6601 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____6601  in
             FStar_Util.print1 "BS list: %s\n" uu____6599);
        (let uu____6610 =
           let uu____6611 = FStar_Syntax_Subst.compress e  in
           uu____6611.FStar_Syntax_Syntax.n  in
         match uu____6610 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____6622,uu____6623) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____6678 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____6678
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then FStar_List.nth bs db.FStar_Syntax_Syntax.index
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____6710  ->
                   let uu____6711 = FStar_Syntax_Print.term_to_string t  in
                   let uu____6713 =
                     let uu____6715 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____6715
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____6711 uu____6713);
              (let uu____6726 = translate cfg bs t  in
               let uu____6727 =
                 FStar_List.map
                   (fun x  ->
                      let uu____6731 =
                        let uu____6732 = translate_univ bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____6732  in
                      FStar_TypeChecker_NBETerm.as_arg uu____6731) us
                  in
               iapp cfg uu____6726 uu____6727))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____6734 = translate_univ bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____6734
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____6775 =
               let uu____6796 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____6876 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____6876, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____6796)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____6775
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____6973  ->
                     let uu____6974 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____6974)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____6976,uu____6977) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____7100,uu____7101) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             let uu____7216 =
               let uu____7254 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____7334 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____7334, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               let uu____7373 =
                 FStar_Util.map_opt resc
                   (fun c  ->
                      fun uu____7413  -> translate_residual_comp cfg bs c)
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____7254, (FStar_List.length xs), uu____7373)
                in
             FStar_TypeChecker_NBETerm.Lam uu____7216
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____7462;
                FStar_Syntax_Syntax.vars = uu____7463;_},arg::more::args)
             ->
             let uu____7555 = FStar_Syntax_Util.head_and_args e  in
             (match uu____7555 with
              | (head1,uu____7581) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____7657 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____7657)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____7678);
                FStar_Syntax_Syntax.pos = uu____7679;
                FStar_Syntax_Syntax.vars = uu____7680;_},arg::more::args)
             ->
             let uu____7776 = FStar_Syntax_Util.head_and_args e  in
             (match uu____7776 with
              | (head1,uu____7802) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____7878 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____7878)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____7899);
                FStar_Syntax_Syntax.pos = uu____7900;
                FStar_Syntax_Syntax.vars = uu____7901;_},arg::[])
             when cfg.FStar_TypeChecker_Cfg.reifying ->
             let cfg1 =
               let uu___649_8040 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___649_8040.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___649_8040.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___649_8040.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___649_8040.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___649_8040.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___649_8040.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___649_8040.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___649_8040.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = false
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____8120);
                FStar_Syntax_Syntax.pos = uu____8121;
                FStar_Syntax_Syntax.vars = uu____8122;_},arg::[])
             ->
             let uu____8190 =
               translate cfg bs (FStar_Pervasives_Native.fst arg)  in
             FStar_TypeChecker_NBETerm.Reflect uu____8190
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____8199;
                FStar_Syntax_Syntax.vars = uu____8200;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___672_8336 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___672_8336.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___672_8336.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___672_8336.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___672_8336.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___672_8336.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___672_8336.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___672_8336.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___672_8336.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____8465  ->
                   let uu____8466 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____8468 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____8466
                     uu____8468);
              (let uu____8471 = translate cfg bs head1  in
               let uu____8472 =
                 FStar_List.map
                   (fun x  ->
                      let uu____8502 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____8502, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____8471 uu____8472))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches readback1 =
               let cfg1 =
                 let uu___688_8679 = cfg  in
                 {
                   FStar_TypeChecker_Cfg.steps =
                     (let uu___690_8752 = cfg.FStar_TypeChecker_Cfg.steps  in
                      {
                        FStar_TypeChecker_Cfg.beta =
                          (uu___690_8752.FStar_TypeChecker_Cfg.beta);
                        FStar_TypeChecker_Cfg.iota =
                          (uu___690_8752.FStar_TypeChecker_Cfg.iota);
                        FStar_TypeChecker_Cfg.zeta = false;
                        FStar_TypeChecker_Cfg.weak =
                          (uu___690_8752.FStar_TypeChecker_Cfg.weak);
                        FStar_TypeChecker_Cfg.hnf =
                          (uu___690_8752.FStar_TypeChecker_Cfg.hnf);
                        FStar_TypeChecker_Cfg.primops =
                          (uu___690_8752.FStar_TypeChecker_Cfg.primops);
                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                          (uu___690_8752.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                        FStar_TypeChecker_Cfg.unfold_until =
                          (uu___690_8752.FStar_TypeChecker_Cfg.unfold_until);
                        FStar_TypeChecker_Cfg.unfold_only =
                          (uu___690_8752.FStar_TypeChecker_Cfg.unfold_only);
                        FStar_TypeChecker_Cfg.unfold_fully =
                          (uu___690_8752.FStar_TypeChecker_Cfg.unfold_fully);
                        FStar_TypeChecker_Cfg.unfold_attr =
                          (uu___690_8752.FStar_TypeChecker_Cfg.unfold_attr);
                        FStar_TypeChecker_Cfg.unfold_tac =
                          (uu___690_8752.FStar_TypeChecker_Cfg.unfold_tac);
                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                          =
                          (uu___690_8752.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                        FStar_TypeChecker_Cfg.simplify =
                          (uu___690_8752.FStar_TypeChecker_Cfg.simplify);
                        FStar_TypeChecker_Cfg.erase_universes =
                          (uu___690_8752.FStar_TypeChecker_Cfg.erase_universes);
                        FStar_TypeChecker_Cfg.allow_unbound_universes =
                          (uu___690_8752.FStar_TypeChecker_Cfg.allow_unbound_universes);
                        FStar_TypeChecker_Cfg.reify_ =
                          (uu___690_8752.FStar_TypeChecker_Cfg.reify_);
                        FStar_TypeChecker_Cfg.compress_uvars =
                          (uu___690_8752.FStar_TypeChecker_Cfg.compress_uvars);
                        FStar_TypeChecker_Cfg.no_full_norm =
                          (uu___690_8752.FStar_TypeChecker_Cfg.no_full_norm);
                        FStar_TypeChecker_Cfg.check_no_uvars =
                          (uu___690_8752.FStar_TypeChecker_Cfg.check_no_uvars);
                        FStar_TypeChecker_Cfg.unmeta =
                          (uu___690_8752.FStar_TypeChecker_Cfg.unmeta);
                        FStar_TypeChecker_Cfg.unascribe =
                          (uu___690_8752.FStar_TypeChecker_Cfg.unascribe);
                        FStar_TypeChecker_Cfg.in_full_norm_request =
                          (uu___690_8752.FStar_TypeChecker_Cfg.in_full_norm_request);
                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                          (uu___690_8752.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                        FStar_TypeChecker_Cfg.nbe_step =
                          (uu___690_8752.FStar_TypeChecker_Cfg.nbe_step);
                        FStar_TypeChecker_Cfg.for_extraction =
                          (uu___690_8752.FStar_TypeChecker_Cfg.for_extraction)
                      });
                   FStar_TypeChecker_Cfg.tcenv =
                     (uu___688_8679.FStar_TypeChecker_Cfg.tcenv);
                   FStar_TypeChecker_Cfg.debug =
                     (uu___688_8679.FStar_TypeChecker_Cfg.debug);
                   FStar_TypeChecker_Cfg.delta_level =
                     (uu___688_8679.FStar_TypeChecker_Cfg.delta_level);
                   FStar_TypeChecker_Cfg.primitive_steps =
                     (uu___688_8679.FStar_TypeChecker_Cfg.primitive_steps);
                   FStar_TypeChecker_Cfg.strong =
                     (uu___688_8679.FStar_TypeChecker_Cfg.strong);
                   FStar_TypeChecker_Cfg.memoize_lazy =
                     (uu___688_8679.FStar_TypeChecker_Cfg.memoize_lazy);
                   FStar_TypeChecker_Cfg.normalize_pure_lets =
                     (uu___688_8679.FStar_TypeChecker_Cfg.normalize_pure_lets);
                   FStar_TypeChecker_Cfg.reifying =
                     (uu___688_8679.FStar_TypeChecker_Cfg.reifying)
                 }  in
               let rec process_pattern bs1 p =
                 let uu____8833 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____8881 =
                         FStar_List.fold_left
                           (fun uu____8922  ->
                              fun uu____8923  ->
                                match (uu____8922, uu____8923) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____9015 = process_pattern bs2 arg
                                       in
                                    (match uu____9015 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____8881 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____9135 =
                           let uu____9144 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____9144  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____9135
                          in
                       let uu____9145 =
                         let uu____9148 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____9148 :: bs1  in
                       (uu____9145, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____9168 =
                           let uu____9177 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____9177  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____9168
                          in
                       let uu____9178 =
                         let uu____9181 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____9181 :: bs1  in
                       (uu____9178, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____9219 =
                           let uu____9228 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____9228  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____9219
                          in
                       let uu____9229 =
                         let uu____9230 =
                           let uu____9246 =
                             let uu____9257 = translate cfg1 bs1 tm  in
                             readback1 uu____9257  in
                           (x, uu____9246)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____9230  in
                       (bs1, uu____9229)
                    in
                 match uu____8833 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___728_9286 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___728_9286.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____9313  ->
                    match uu____9313 with
                    | (pat,when_clause,e1) ->
                        let uu____9359 = process_pattern bs pat  in
                        (match uu____9359 with
                         | (bs',pat') ->
                             let uu____9372 =
                               let uu____9373 =
                                 let uu____9384 = translate cfg1 bs' e1  in
                                 readback1 uu____9384  in
                               (pat', when_clause, uu____9373)  in
                             FStar_Syntax_Util.branch uu____9372)) branches
                in
             let rec case scrut1 =
               debug1
                 (fun uu____9417  ->
                    let uu____9418 =
                      let uu____9420 = readback cfg scrut1  in
                      FStar_Syntax_Print.term_to_string uu____9420  in
                    let uu____9429 =
                      FStar_TypeChecker_NBETerm.t_to_string scrut1  in
                    FStar_Util.print2 "Match case: (%s) -- (%s)\n" uu____9418
                      uu____9429);
               (let scrut2 = unlazy scrut1  in
                match scrut2 with
                | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                    (debug1
                       (fun uu____9463  ->
                          let uu____9464 =
                            let uu____9466 =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____9492  ->
                                      match uu____9492 with
                                      | (x,q) ->
                                          let uu____9506 =
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              x
                                             in
                                          Prims.op_Hat
                                            (if FStar_Util.is_some q
                                             then "#"
                                             else "") uu____9506))
                               in
                            FStar_All.pipe_right uu____9466
                              (FStar_String.concat "; ")
                             in
                          FStar_Util.print1 "Match args: %s\n" uu____9464);
                     (let uu____9520 = pickBranch cfg scrut2 branches  in
                      match uu____9520 with
                      | FStar_Pervasives_Native.Some (branch1,args1) ->
                          let uu____9557 =
                            FStar_List.fold_left
                              (fun bs1  -> fun x  -> x :: bs1) bs args1
                             in
                          translate cfg uu____9557 branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                            make_branches))
                | FStar_TypeChecker_NBETerm.Constant c ->
                    (debug1
                       (fun uu____9584  ->
                          let uu____9585 =
                            FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                          FStar_Util.print1 "Match constant : %s\n"
                            uu____9585);
                     (let uu____9588 = pickBranch cfg scrut2 branches  in
                      match uu____9588 with
                      | FStar_Pervasives_Native.Some (branch1,[]) ->
                          translate cfg bs branch1
                      | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                          translate cfg (arg :: bs) branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                            make_branches
                      | FStar_Pervasives_Native.Some (uu____9654,hd1::tl1) ->
                          failwith
                            "Impossible: Matching on constants cannot bind more than one variable"))
                | uu____9680 ->
                    FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                      make_branches)
                in
             let uu____9681 = translate cfg bs scrut  in case uu____9681
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
             let uu____9908 = make_rec_env (translate_letbinding cfg) lbs bs
                in
             translate cfg uu____9908 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____9912) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____9975  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____10003 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____10033  ->
                      match uu____10033 with
                      | (bv,t1) ->
                          let uu____10055 =
                            let uu____10071 = readback cfg t1  in
                            (bv, uu____10071)  in
                          FStar_Syntax_Syntax.NT uu____10055) uu____10003
                  in
               let uu____10093 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____10093  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close1 qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close1 qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu____10138 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____10153  ->
                    let uu____10154 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____10154);
               translate cfg bs t  in
             let uu____10157 =
               let uu____10176 = FStar_Common.mk_thunk f  in
               ((FStar_Util.Inl li), uu____10176)  in
             FStar_TypeChecker_NBETerm.Lazy uu____10157)

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
            let uu____10263 =
              let uu____10270 = translate cfg bs typ  in
              let uu____10271 = fmap_opt (translate_univ bs) u  in
              (uu____10270, uu____10271)  in
            FStar_TypeChecker_NBETerm.Tot uu____10263
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____10294 =
              let uu____10301 = translate cfg bs typ  in
              let uu____10302 = fmap_opt (translate_univ bs) u  in
              (uu____10301, uu____10302)  in
            FStar_TypeChecker_NBETerm.GTot uu____10294
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____10313 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____10313

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____10372 =
              let uu____10385 = readback cfg typ  in (uu____10385, u)  in
            FStar_Syntax_Syntax.Total uu____10372
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____10410 =
              let uu____10423 = readback cfg typ  in (uu____10423, u)  in
            FStar_Syntax_Syntax.GTotal uu____10410
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____10448 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____10448
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
        let uu____10509 = c  in
        match uu____10509 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____10556 = FStar_List.map (translate_univ bs) comp_univs
               in
            let uu____10557 = translate cfg bs result_typ  in
            let uu____10558 =
              FStar_List.map
                (fun x  ->
                   let uu____10594 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____10594, (FStar_Pervasives_Native.snd x)))
                effect_args
               in
            let uu____10609 = FStar_List.map (translate_flag cfg bs) flags
               in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____10556;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____10557;
              FStar_TypeChecker_NBETerm.effect_args = uu____10558;
              FStar_TypeChecker_NBETerm.flags = uu____10609
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____10659 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____10670 =
        FStar_List.map
          (fun x  ->
             let uu____10704 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____10704, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____10717 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____10659;
        FStar_Syntax_Syntax.effect_args = uu____10670;
        FStar_Syntax_Syntax.flags = uu____10717
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
        let uu____10774 = c  in
        match uu____10774 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____10813 =
              FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____10822 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____10813;
              FStar_TypeChecker_NBETerm.residual_flags = uu____10822
            }

and (readback_residual_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____10876 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (readback cfg)
         in
      let uu____10891 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____10876;
        FStar_Syntax_Syntax.residual_flags = uu____10891
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
            let uu____10941 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____10941

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
          let uu____10980 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____10980

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____10991  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____10991 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____11143 =
                     let uu____11172 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____11172
                      in
                   (match uu____11143 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____11207 =
                          let uu____11209 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____11209
                           in
                        failwith uu____11207
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___936_11355 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___936_11355.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___936_11355.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___936_11355.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___936_11355.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___936_11355.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___936_11355.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___936_11355.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___936_11355.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____11459 =
                            let uu____11466 =
                              let uu____11467 =
                                let uu____11502 =
                                  let uu____11516 =
                                    let uu____11528 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____11528,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____11516]  in
                                (uu____11502, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____11467  in
                            FStar_Syntax_Syntax.mk uu____11466  in
                          uu____11459 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____11618 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____11618
                          then
                            let uu____11631 =
                              let uu____11636 =
                                let uu____11637 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____11637  in
                              (uu____11636, FStar_Pervasives_Native.None)  in
                            let uu____11646 =
                              let uu____11653 =
                                let uu____11658 =
                                  let uu____11659 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____11659  in
                                (uu____11658, FStar_Pervasives_Native.None)
                                 in
                              [uu____11653]  in
                            uu____11631 :: uu____11646
                          else []  in
                        let t =
                          let uu____11687 =
                            let uu____11688 =
                              let uu____11689 =
                                FStar_Syntax_Util.un_uinst
                                  (FStar_Pervasives_Native.snd
                                     ed.FStar_Syntax_Syntax.bind_repr)
                                 in
                              translate cfg' [] uu____11689  in
                            iapp cfg uu____11688
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____11720 =
                            let uu____11721 =
                              let uu____11728 =
                                let uu____11733 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____11733, FStar_Pervasives_Native.None)
                                 in
                              let uu____11734 =
                                let uu____11741 =
                                  let uu____11746 = translate cfg' bs ty  in
                                  (uu____11746, FStar_Pervasives_Native.None)
                                   in
                                [uu____11741]  in
                              uu____11728 :: uu____11734  in
                            let uu____11759 =
                              let uu____11766 =
                                let uu____11773 =
                                  let uu____11780 =
                                    let uu____11785 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____11785,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____11786 =
                                    let uu____11793 =
                                      let uu____11800 =
                                        let uu____11805 =
                                          translate cfg bs body_lam  in
                                        (uu____11805,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____11800]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____11793
                                     in
                                  uu____11780 :: uu____11786  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) ::
                                  uu____11773
                                 in
                              FStar_List.append maybe_range_arg uu____11766
                               in
                            FStar_List.append uu____11721 uu____11759  in
                          iapp cfg uu____11687 uu____11720  in
                        (debug cfg
                           (fun uu____11837  ->
                              let uu____11838 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____11838);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____11841);
                      FStar_Syntax_Syntax.pos = uu____11842;
                      FStar_Syntax_Syntax.vars = uu____11843;_},(e2,uu____11845)::[])
                   ->
                   translate
                     (let uu___958_11918 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___958_11918.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___958_11918.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___958_11918.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___958_11918.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___958_11918.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___958_11918.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___958_11918.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___958_11918.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   (debug cfg
                      (fun uu____12036  ->
                         let uu____12037 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____12039 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____12037
                           uu____12039);
                    (let fallback1 uu____12047 = translate cfg bs e1  in
                     let fallback2 uu____12053 =
                       let uu____12054 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           FStar_Pervasives_Native.None
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate
                         (let uu___970_12081 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___970_12081.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___970_12081.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___970_12081.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___970_12081.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___970_12081.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___970_12081.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___970_12081.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___970_12081.FStar_TypeChecker_Cfg.normalize_pure_lets);
                            FStar_TypeChecker_Cfg.reifying = false
                          }) bs uu____12054
                        in
                     let uu____12153 =
                       let uu____12154 = FStar_Syntax_Util.un_uinst head1  in
                       uu____12154.FStar_Syntax_Syntax.n  in
                     match uu____12153 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             cfg.FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____12179 =
                           let uu____12181 =
                             FStar_TypeChecker_Env.is_action
                               cfg.FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____12181  in
                         if uu____12179
                         then fallback1 ()
                         else
                           (let uu____12186 =
                              let uu____12188 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  cfg.FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____12188  in
                            if uu____12186
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____12225 =
                                   let uu____12230 =
                                     FStar_Syntax_Util.mk_reify head1  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____12230
                                     args
                                    in
                                 uu____12225 FStar_Pervasives_Native.None
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               translate
                                 (let uu___979_12241 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___979_12241.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___979_12241.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___979_12241.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___979_12241.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___979_12241.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong =
                                      (uu___979_12241.FStar_TypeChecker_Cfg.strong);
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___979_12241.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___979_12241.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying = false
                                  }) bs e2))
                     | uu____12313 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____12519  ->
                             match uu____12519 with
                             | (pat,wopt,tm) ->
                                 let uu____12608 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____12608)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   translate
                     (let uu___992_12684 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___992_12684.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___992_12684.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___992_12684.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___992_12684.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___992_12684.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___992_12684.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___992_12684.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___992_12684.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____12757) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____12852 ->
                   let uu____12853 =
                     let uu____12855 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____12855
                      in
                   failwith uu____12853)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____12858  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____12858 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____12965 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____12965
              then
                let ed =
                  let uu____13009 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____13009
                   in
                let ret1 =
                  let uu____13027 =
                    let uu____13028 =
                      FStar_Syntax_Subst.compress
                        (FStar_Pervasives_Native.snd
                           ed.FStar_Syntax_Syntax.return_repr)
                       in
                    uu____13028.FStar_Syntax_Syntax.n  in
                  match uu____13027 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret1,uu____13054::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret1, [FStar_Syntax_Syntax.U_unknown]))
                        FStar_Pervasives_Native.None
                        e1.FStar_Syntax_Syntax.pos
                  | uu____13073 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' =
                  let uu___1025_13150 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___1025_13150.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1025_13150.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1025_13150.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___1025_13150.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1025_13150.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1025_13150.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1025_13150.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1025_13150.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let t =
                  let uu____13223 =
                    let uu____13224 = translate cfg' [] ret1  in
                    iapp cfg' uu____13224
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____13233 =
                    let uu____13234 =
                      let uu____13239 = translate cfg' bs ty  in
                      (uu____13239, FStar_Pervasives_Native.None)  in
                    let uu____13240 =
                      let uu____13247 =
                        let uu____13252 = translate cfg' bs e1  in
                        (uu____13252, FStar_Pervasives_Native.None)  in
                      [uu____13247]  in
                    uu____13234 :: uu____13240  in
                  iapp cfg' uu____13223 uu____13233  in
                (debug cfg
                   (fun uu____13268  ->
                      let uu____13269 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____13269);
                 t)
              else
                (let uu____13274 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____13274 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____13291 =
                       let uu____13293 = FStar_Ident.text_of_lid msrc  in
                       let uu____13295 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____13293 uu____13295
                        in
                     failwith uu____13291
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____13298;
                       FStar_TypeChecker_Env.mtarget = uu____13299;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____13300;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____13365 =
                       let uu____13367 = FStar_Ident.text_of_lid msrc  in
                       let uu____13369 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____13367 uu____13369
                        in
                     failwith uu____13365
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____13372;
                       FStar_TypeChecker_Env.mtarget = uu____13373;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____13374;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____13490 =
                         let uu____13501 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____13501
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____13490
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___1049_13617 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___1049_13617.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1049_13617.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1049_13617.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___1049_13617.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1049_13617.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1049_13617.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1049_13617.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___1049_13617.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let t =
                       let uu____13690 = translate cfg' [] lift_lam  in
                       let uu____13691 =
                         let uu____13692 =
                           let uu____13697 = translate cfg bs e1  in
                           (uu____13697, FStar_Pervasives_Native.None)  in
                         [uu____13692]  in
                       iapp cfg uu____13690 uu____13691  in
                     (debug cfg
                        (fun uu____13709  ->
                           let uu____13710 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____13710);
                      t))

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____13767  ->
           let uu____13768 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____13768);
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
           let uu____13784 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____13784 FStar_Syntax_Util.exp_int
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
           let uu____13862 =
             FStar_List.fold_left
               (fun uu____13915  ->
                  fun tf  ->
                    match uu____13915 with
                    | (args_rev,accus_rev) ->
                        let uu____13987 = tf accus_rev  in
                        (match uu____13987 with
                         | (xt,q) ->
                             let x1 =
                               let uu____14022 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____14022
                                in
                             let uu____14031 =
                               let uu____14034 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____14034 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____14031))) ([], [])
               targs
              in
           (match uu____13862 with
            | (args_rev,accus_rev) ->
                let body =
                  let uu____14125 = f (FStar_List.rev accus_rev)  in
                  readback cfg uu____14125  in
                let uu____14126 =
                  FStar_Util.map_opt resc
                    (fun thunk1  ->
                       let uu____14165 = thunk1 ()  in
                       readback_residual_comp cfg uu____14165)
                   in
                FStar_Syntax_Util.abs (FStar_List.rev args_rev) body
                  uu____14126)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____14222 =
               let uu____14231 =
                 let uu____14232 = targ ()  in
                 FStar_Pervasives_Native.fst uu____14232  in
               readback cfg uu____14231  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____14222
              in
           let body =
             let uu____14246 =
               let uu____14247 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____14247  in
             readback cfg uu____14246  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t  in FStar_Syntax_Util.mk_reflect tm
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____14292 =
             FStar_List.fold_left
               (fun uu____14345  ->
                  fun tf  ->
                    match uu____14345 with
                    | (args_rev,accus_rev) ->
                        let uu____14417 = tf accus_rev  in
                        (match uu____14417 with
                         | (xt,q) ->
                             let x1 =
                               let uu____14452 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____14452
                                in
                             let uu____14461 =
                               let uu____14464 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____14464 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____14461))) ([], [])
               targs
              in
           (match uu____14292 with
            | (args_rev,accus_rev) ->
                let cmp =
                  let uu____14555 = f (FStar_List.rev accus_rev)  in
                  readback_comp cfg uu____14555  in
                FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____14617  ->
                  match uu____14617 with
                  | (x1,q) ->
                      let uu____14632 = readback cfg x1  in (uu____14632, q))
               args
              in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____14683 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____14698::uu____14699 ->
                let uu____14702 =
                  let uu____14713 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____14713
                    (FStar_List.rev us)
                   in
                apply1 uu____14702
            | [] ->
                let uu____14722 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply1 uu____14722)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____14785  ->
                  match uu____14785 with
                  | (x1,q) ->
                      let uu____14800 = readback cfg x1  in (uu____14800, q))
               args
              in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____14851 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____14866::uu____14867 ->
                let uu____14870 =
                  let uu____14881 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____14881
                    (FStar_List.rev us)
                   in
                apply1 uu____14870
            | [] ->
                let uu____14890 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply1 uu____14890)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____14963  ->
                  match uu____14963 with
                  | (x1,q) ->
                      let uu____14978 = readback cfg x1  in (uu____14978, q))
               ts
              in
           let uu____14991 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____14991 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____15075  ->
                  match uu____15075 with
                  | (x1,q) ->
                      let uu____15090 = readback cfg x1  in (uu____15090, q))
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
            | uu____15167 -> FStar_Syntax_Util.mk_app head1 args)
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
               (fun uu____15344  ->
                  match uu____15344 with
                  | (x1,q) ->
                      let uu____15359 = readback cfg x1  in (uu____15359, q))
               args
              in
           (match args1 with
            | [] -> head1
            | uu____15384 -> FStar_Syntax_Util.mk_app head1 args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____15418) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (uu____15447,thunk1) ->
           let uu____15477 = FStar_Common.force_thunk thunk1  in
           readback cfg uu____15477)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____15514 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____15526 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____15551 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____15594 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____15630 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____15641 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___1_15648  ->
    match uu___1_15648 with
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
            let uu___1247_15983 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1249_16056 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1249_16056.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1247_15983.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1247_15983.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1247_15983.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1247_15983.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1247_15983.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1247_15983.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1247_15983.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1247_15983.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____16113  ->
               let uu____16114 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with (%s) {\n" uu____16114);
          (let r =
             let uu____16126 = translate cfg1 [] e  in
             readback cfg1 uu____16126  in
           debug cfg1
             (fun uu____16130  ->
                let uu____16131 = FStar_Syntax_Print.term_to_string r  in
                FStar_Util.print1 "}\nNBE returned (%s)\n" uu____16131);
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
          let uu___1264_16420 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1266_16493 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1266_16493.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1264_16420.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1264_16420.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1264_16420.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1264_16420.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1264_16420.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1264_16420.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1264_16420.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1264_16420.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____16550  ->
             let uu____16551 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____16551);
        (let r =
           let uu____16563 = translate cfg1 [] e  in
           readback cfg1 uu____16563  in
         debug cfg1
           (fun uu____16567  ->
              let uu____16568 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____16568);
         r)
  