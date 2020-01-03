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
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding -> (Prims.int * Prims.bool Prims.list)) =
  fun b  ->
    let uu____414 = FStar_Syntax_Util.let_rec_arity b  in
    match uu____414 with
    | (ar,maybe_lst) ->
        (match maybe_lst with
         | FStar_Pervasives_Native.None  ->
             let uu____458 =
               FStar_Common.tabulate ar (fun uu____464  -> true)  in
             (ar, uu____458)
         | FStar_Pervasives_Native.Some lst -> (ar, lst))
  
let (debug : FStar_TypeChecker_Cfg.cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____498 =
        let uu____500 = FStar_TypeChecker_Cfg.cfg_env cfg  in
        FStar_TypeChecker_Env.debug uu____500 (FStar_Options.Other "NBE")  in
      if uu____498 then f () else ()
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____511 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____511
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____532 = FStar_Syntax_Print.sigelt_to_string_short v1  in
             FStar_Util.print2 "%s -> %%s\n" k uu____532) ()
  
let (unlazy : FStar_TypeChecker_NBETerm.t -> FStar_TypeChecker_NBETerm.t) =
  fun t  ->
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (uu____541,t1) -> FStar_Thunk.force t1
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
              (fun uu____669  ->
                 let uu____670 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0  in
                 let uu____672 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____670
                   uu____672);
            (let scrutinee = unlazy scrutinee0  in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____699 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____726  ->
                          let uu____727 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____729 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu____727
                            uu____729);
                     (match c with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____739 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____756 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____756
                           | uu____757 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____760))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____765) ->
                               st = p1
                           | uu____769 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____777 -> false)
                      | uu____779 -> false)
                      in
                   let uu____781 = matches_const scrutinee s  in
                   if uu____781
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____919)::rest_a,(p2,uu____922)::rest_p) ->
                         let uu____961 = matches_pat t p2  in
                         (match uu____961 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____990 -> FStar_Util.Inr false  in
                   (match scrutinee with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____1038 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                        if uu____1038
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____1058 -> FStar_Util.Inr true)
                in
             let res_to_string uu___0_1076 =
               match uu___0_1076 with
               | FStar_Util.Inr b ->
                   let uu____1090 = FStar_Util.string_of_bool b  in
                   Prims.op_Hat "Inr " uu____1090
               | FStar_Util.Inl bs ->
                   let uu____1099 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.op_Hat "Inl " uu____1099
                in
             debug cfg
               (fun uu____1107  ->
                  let uu____1108 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____1110 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____1112 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____1108
                    uu____1110 uu____1112);
             r)
             in
          match branches1 with
          | [] -> failwith "Branch not found"
          | (p,_wopt,e)::branches2 ->
              let uu____1154 = matches_pat scrut1 p  in
              (match uu____1154 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____1179  ->
                         let uu____1180 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____1180);
                    FStar_Pervasives_Native.Some (e, matches))
               | FStar_Util.Inr (false ) ->
                   pickBranch_aux scrut1 branches2 branches0
               | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
           in
        pickBranch_aux scrut branches branches
  
let (should_reduce_recursive_definition :
  FStar_TypeChecker_NBETerm.args ->
    Prims.bool Prims.list ->
      (Prims.bool * FStar_TypeChecker_NBETerm.args *
        FStar_TypeChecker_NBETerm.args))
  =
  fun arguments  ->
    fun formals_in_decreases  ->
      let rec aux ts ar_list acc =
        match (ts, ar_list) with
        | (uu____1329,[]) -> (true, acc, ts)
        | ([],uu____1360::uu____1361) -> (false, acc, [])
        | (t::ts1,in_decreases_clause::bs) ->
            let uu____1430 =
              in_decreases_clause &&
                (FStar_TypeChecker_NBETerm.isAccu
                   (FStar_Pervasives_Native.fst t))
               in
            if uu____1430
            then (false, (FStar_List.rev_append ts1 acc), [])
            else aux ts1 bs (t :: acc)
         in
      aux arguments formals_in_decreases []
  
let (find_sigelt_in_gamma :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.env ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lid  ->
        let mapper uu____1529 =
          match uu____1529 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1612  ->
                         let uu____1613 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1613);
                    FStar_Pervasives_Native.Some elt)
               | uu____1616 -> FStar_Pervasives_Native.None)
           in
        let uu____1631 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1631 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1678 -> true
    | uu____1680 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | t ->
        let uu____1690 =
          let uu____1692 = FStar_TypeChecker_NBETerm.t_to_string t  in
          Prims.op_Hat "Not a universe: " uu____1692  in
        failwith uu____1690
  
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
              (uu____1714,uu____1715,uu____1716,uu____1717,uu____1718,uu____1719);
            FStar_Syntax_Syntax.sigrng = uu____1720;
            FStar_Syntax_Syntax.sigquals = uu____1721;
            FStar_Syntax_Syntax.sigmeta = uu____1722;
            FStar_Syntax_Syntax.sigattrs = uu____1723;
            FStar_Syntax_Syntax.sigopts = uu____1724;_},uu____1725),uu____1726)
        -> true
    | uu____1786 -> false
  
let (translate_univ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun bs  ->
      fun u  ->
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar i ->
              if i < (FStar_List.length bs)
              then let u' = FStar_List.nth bs i  in un_univ u'
              else
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                then FStar_Syntax_Syntax.U_zero
                else failwith "Universe index out of bounds"
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1826 = aux u3  in
              FStar_Syntax_Syntax.U_succ uu____1826
          | FStar_Syntax_Syntax.U_max us ->
              let uu____1830 = FStar_List.map aux us  in
              FStar_Syntax_Syntax.U_max uu____1830
          | FStar_Syntax_Syntax.U_unknown  -> u2
          | FStar_Syntax_Syntax.U_name uu____1833 -> u2
          | FStar_Syntax_Syntax.U_unif uu____1834 -> u2
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
           | FStar_Util.Inl uu____1865 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1870 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1870
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
  
let rec (translate :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun e  ->
        let debug1 = debug cfg  in
        debug1
          (fun uu____2141  ->
             let uu____2142 =
               let uu____2144 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2144  in
             let uu____2145 =
               let uu____2147 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2147  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2142 uu____2145);
        (let uu____2149 =
           let uu____2150 = FStar_Syntax_Subst.compress e  in
           uu____2150.FStar_Syntax_Syntax.n  in
         match uu____2149 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2153,uu____2154) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2193 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____2193
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then
               let t = FStar_List.nth bs db.FStar_Syntax_Syntax.index  in
               (debug1
                  (fun uu____2202  ->
                     let uu____2203 = FStar_TypeChecker_NBETerm.t_to_string t
                        in
                     FStar_Util.print1 "Resolved bvar to %s\n" uu____2203);
                t)
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____2222  ->
                   let uu____2223 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2225 =
                     let uu____2227 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2227
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____2223 uu____2225);
              (let uu____2238 = translate cfg bs t  in
               let uu____2239 =
                 FStar_List.map
                   (fun x  ->
                      let uu____2243 =
                        let uu____2244 = translate_univ cfg bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____2244  in
                      FStar_TypeChecker_NBETerm.as_arg uu____2243) us
                  in
               iapp cfg uu____2238 uu____2239))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2246 = translate_univ cfg bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____2246
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____2269 =
               let uu____2290 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____2360 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____2360, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____2290)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____2269
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____2429  ->
                     let uu____2430 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____2430)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2432,uu____2433) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2495,uu____2496) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             let uu____2547 =
               let uu____2580 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____2650 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____2650, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               let uu____2679 =
                 FStar_Util.map_opt resc
                   (fun c  ->
                      fun formals  ->
                        translate_residual_comp cfg
                          (FStar_List.rev_append formals bs) c)
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____2580, (FStar_List.length xs), uu____2679)
                in
             FStar_TypeChecker_NBETerm.Lam uu____2547
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____2733;
                FStar_Syntax_Syntax.vars = uu____2734;_},arg::more::args)
             ->
             let uu____2794 = FStar_Syntax_Util.head_and_args e  in
             (match uu____2794 with
              | (head1,uu____2812) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____2856 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____2856)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____2865);
                FStar_Syntax_Syntax.pos = uu____2866;
                FStar_Syntax_Syntax.vars = uu____2867;_},arg::more::args)
             ->
             let uu____2927 = FStar_Syntax_Util.head_and_args e  in
             (match uu____2927 with
              | (head1,uu____2945) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____2989 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____2989)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____2998);
                FStar_Syntax_Syntax.pos = uu____2999;
                FStar_Syntax_Syntax.vars = uu____3000;_},arg::[])
             when cfg.FStar_TypeChecker_Cfg.reifying ->
             let cfg1 =
               let uu___418_3041 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___418_3041.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___418_3041.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___418_3041.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___418_3041.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___418_3041.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___418_3041.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___418_3041.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___418_3041.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = false
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3047);
                FStar_Syntax_Syntax.pos = uu____3048;
                FStar_Syntax_Syntax.vars = uu____3049;_},arg::[])
             ->
             let uu____3089 =
               translate cfg bs (FStar_Pervasives_Native.fst arg)  in
             FStar_TypeChecker_NBETerm.Reflect uu____3089
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3094;
                FStar_Syntax_Syntax.vars = uu____3095;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___441_3137 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___441_3137.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___441_3137.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___441_3137.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___441_3137.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___441_3137.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___441_3137.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___441_3137.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___441_3137.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____3176  ->
                   let uu____3177 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3179 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3177
                     uu____3179);
              (let uu____3182 = translate cfg bs head1  in
               let uu____3183 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3205 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3205, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3182 uu____3183))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches readback1 =
               let cfg1 =
                 let uu___457_3266 = cfg  in
                 {
                   FStar_TypeChecker_Cfg.steps =
                     (let uu___459_3269 = cfg.FStar_TypeChecker_Cfg.steps  in
                      {
                        FStar_TypeChecker_Cfg.beta =
                          (uu___459_3269.FStar_TypeChecker_Cfg.beta);
                        FStar_TypeChecker_Cfg.iota =
                          (uu___459_3269.FStar_TypeChecker_Cfg.iota);
                        FStar_TypeChecker_Cfg.zeta = false;
                        FStar_TypeChecker_Cfg.weak =
                          (uu___459_3269.FStar_TypeChecker_Cfg.weak);
                        FStar_TypeChecker_Cfg.hnf =
                          (uu___459_3269.FStar_TypeChecker_Cfg.hnf);
                        FStar_TypeChecker_Cfg.primops =
                          (uu___459_3269.FStar_TypeChecker_Cfg.primops);
                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                          (uu___459_3269.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                        FStar_TypeChecker_Cfg.unfold_until =
                          (uu___459_3269.FStar_TypeChecker_Cfg.unfold_until);
                        FStar_TypeChecker_Cfg.unfold_only =
                          (uu___459_3269.FStar_TypeChecker_Cfg.unfold_only);
                        FStar_TypeChecker_Cfg.unfold_fully =
                          (uu___459_3269.FStar_TypeChecker_Cfg.unfold_fully);
                        FStar_TypeChecker_Cfg.unfold_attr =
                          (uu___459_3269.FStar_TypeChecker_Cfg.unfold_attr);
                        FStar_TypeChecker_Cfg.unfold_tac =
                          (uu___459_3269.FStar_TypeChecker_Cfg.unfold_tac);
                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                          =
                          (uu___459_3269.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                        FStar_TypeChecker_Cfg.simplify =
                          (uu___459_3269.FStar_TypeChecker_Cfg.simplify);
                        FStar_TypeChecker_Cfg.erase_universes =
                          (uu___459_3269.FStar_TypeChecker_Cfg.erase_universes);
                        FStar_TypeChecker_Cfg.allow_unbound_universes =
                          (uu___459_3269.FStar_TypeChecker_Cfg.allow_unbound_universes);
                        FStar_TypeChecker_Cfg.reify_ =
                          (uu___459_3269.FStar_TypeChecker_Cfg.reify_);
                        FStar_TypeChecker_Cfg.compress_uvars =
                          (uu___459_3269.FStar_TypeChecker_Cfg.compress_uvars);
                        FStar_TypeChecker_Cfg.no_full_norm =
                          (uu___459_3269.FStar_TypeChecker_Cfg.no_full_norm);
                        FStar_TypeChecker_Cfg.check_no_uvars =
                          (uu___459_3269.FStar_TypeChecker_Cfg.check_no_uvars);
                        FStar_TypeChecker_Cfg.unmeta =
                          (uu___459_3269.FStar_TypeChecker_Cfg.unmeta);
                        FStar_TypeChecker_Cfg.unascribe =
                          (uu___459_3269.FStar_TypeChecker_Cfg.unascribe);
                        FStar_TypeChecker_Cfg.in_full_norm_request =
                          (uu___459_3269.FStar_TypeChecker_Cfg.in_full_norm_request);
                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                          (uu___459_3269.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                        FStar_TypeChecker_Cfg.nbe_step =
                          (uu___459_3269.FStar_TypeChecker_Cfg.nbe_step);
                        FStar_TypeChecker_Cfg.for_extraction =
                          (uu___459_3269.FStar_TypeChecker_Cfg.for_extraction)
                      });
                   FStar_TypeChecker_Cfg.tcenv =
                     (uu___457_3266.FStar_TypeChecker_Cfg.tcenv);
                   FStar_TypeChecker_Cfg.debug =
                     (uu___457_3266.FStar_TypeChecker_Cfg.debug);
                   FStar_TypeChecker_Cfg.delta_level =
                     (uu___457_3266.FStar_TypeChecker_Cfg.delta_level);
                   FStar_TypeChecker_Cfg.primitive_steps =
                     (uu___457_3266.FStar_TypeChecker_Cfg.primitive_steps);
                   FStar_TypeChecker_Cfg.strong =
                     (uu___457_3266.FStar_TypeChecker_Cfg.strong);
                   FStar_TypeChecker_Cfg.memoize_lazy =
                     (uu___457_3266.FStar_TypeChecker_Cfg.memoize_lazy);
                   FStar_TypeChecker_Cfg.normalize_pure_lets =
                     (uu___457_3266.FStar_TypeChecker_Cfg.normalize_pure_lets);
                   FStar_TypeChecker_Cfg.reifying =
                     (uu___457_3266.FStar_TypeChecker_Cfg.reifying)
                 }  in
               let rec process_pattern bs1 p =
                 let uu____3298 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____3334 =
                         FStar_List.fold_left
                           (fun uu____3375  ->
                              fun uu____3376  ->
                                match (uu____3375, uu____3376) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3468 = process_pattern bs2 arg
                                       in
                                    (match uu____3468 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3334 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____3567 =
                           let uu____3568 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3568  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3567
                          in
                       let uu____3569 =
                         let uu____3572 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3572 :: bs1  in
                       (uu____3569, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3577 =
                           let uu____3578 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3578  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3577
                          in
                       let uu____3579 =
                         let uu____3582 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3582 :: bs1  in
                       (uu____3579, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3592 =
                           let uu____3593 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3593  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3592
                          in
                       let uu____3594 =
                         let uu____3595 =
                           let uu____3602 =
                             let uu____3605 = translate cfg1 bs1 tm  in
                             readback1 uu____3605  in
                           (x, uu____3602)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3595  in
                       (bs1, uu____3594)
                    in
                 match uu____3298 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___497_3625 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___497_3625.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____3644  ->
                    match uu____3644 with
                    | (pat,when_clause,e1) ->
                        let uu____3666 = process_pattern bs pat  in
                        (match uu____3666 with
                         | (bs',pat') ->
                             let uu____3679 =
                               let uu____3680 =
                                 let uu____3683 = translate cfg1 bs' e1  in
                                 readback1 uu____3683  in
                               (pat', when_clause, uu____3680)  in
                             FStar_Syntax_Util.branch uu____3679)) branches
                in
             let rec case scrut1 =
               debug1
                 (fun uu____3705  ->
                    let uu____3706 =
                      let uu____3708 = readback cfg scrut1  in
                      FStar_Syntax_Print.term_to_string uu____3708  in
                    let uu____3709 =
                      FStar_TypeChecker_NBETerm.t_to_string scrut1  in
                    FStar_Util.print2 "Match case: (%s) -- (%s)\n" uu____3706
                      uu____3709);
               (let scrut2 = unlazy scrut1  in
                match scrut2 with
                | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                    (debug1
                       (fun uu____3737  ->
                          let uu____3738 =
                            let uu____3740 =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3766  ->
                                      match uu____3766 with
                                      | (x,q) ->
                                          let uu____3780 =
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              x
                                             in
                                          Prims.op_Hat
                                            (if FStar_Util.is_some q
                                             then "#"
                                             else "") uu____3780))
                               in
                            FStar_All.pipe_right uu____3740
                              (FStar_String.concat "; ")
                             in
                          FStar_Util.print1 "Match args: %s\n" uu____3738);
                     (let uu____3794 = pickBranch cfg scrut2 branches  in
                      match uu____3794 with
                      | FStar_Pervasives_Native.Some (branch1,args1) ->
                          let uu____3815 =
                            FStar_List.fold_left
                              (fun bs1  -> fun x  -> x :: bs1) bs args1
                             in
                          translate cfg uu____3815 branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                            make_branches))
                | FStar_TypeChecker_NBETerm.Constant c ->
                    (debug1
                       (fun uu____3838  ->
                          let uu____3839 =
                            FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                          FStar_Util.print1 "Match constant : %s\n"
                            uu____3839);
                     (let uu____3842 = pickBranch cfg scrut2 branches  in
                      match uu____3842 with
                      | FStar_Pervasives_Native.Some (branch1,[]) ->
                          translate cfg bs branch1
                      | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                          translate cfg (arg :: bs) branch1
                      | FStar_Pervasives_Native.None  ->
                          FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                            make_branches
                      | FStar_Pervasives_Native.Some (uu____3876,hd1::tl1) ->
                          failwith
                            "Impossible: Matching on constants cannot bind more than one variable"))
                | uu____3890 ->
                    FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case
                      make_branches)
                in
             let uu____3891 = translate cfg bs scrut  in case uu____3891
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic (m,t)) when
             cfg.FStar_TypeChecker_Cfg.reifying ->
             translate_monadic (m, t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t)) when
             cfg.FStar_TypeChecker_Cfg.reifying ->
             translate_monadic_lift (m, m', t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
             let uu____3936 =
               FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
             if uu____3936
             then
               let bs1 =
                 let uu____3942 = translate_letbinding cfg bs lb  in
                 uu____3942 :: bs  in
               translate cfg bs1 body
             else
               (let def = translate cfg bs lb.FStar_Syntax_Syntax.lbdef  in
                let typ = translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                let name =
                  let uu____3948 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.freshen_bv uu____3948  in
                let bs1 =
                  (FStar_TypeChecker_NBETerm.Accu
                     ((FStar_TypeChecker_NBETerm.Var name), []))
                  :: bs  in
                let body1 = translate cfg bs1 body  in
                FStar_TypeChecker_NBETerm.UnreducedLet
                  (name, typ, def, body1, lb))
         | FStar_Syntax_Syntax.Tm_let ((_rec,lbs),body) ->
             if
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations
             then
               let vars =
                 FStar_List.map
                   (fun lb  ->
                      let uu____3990 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.freshen_bv uu____3990) lbs
                  in
               let typs =
                 FStar_List.map
                   (fun lb  -> translate cfg bs lb.FStar_Syntax_Syntax.lbtyp)
                   lbs
                  in
               let rec_bs =
                 let uu____3999 =
                   FStar_List.map
                     (fun v1  ->
                        FStar_TypeChecker_NBETerm.Accu
                          ((FStar_TypeChecker_NBETerm.Var v1), [])) vars
                    in
                 FStar_List.append uu____3999 bs  in
               let defs =
                 FStar_List.map
                   (fun lb  ->
                      translate cfg rec_bs lb.FStar_Syntax_Syntax.lbdef) lbs
                  in
               let body1 = translate cfg rec_bs body  in
               let uu____4020 =
                 let uu____4037 = FStar_List.zip3 vars typs defs  in
                 (uu____4037, body1, lbs)  in
               FStar_TypeChecker_NBETerm.UnreducedLetRec uu____4020
             else
               (let uu____4058 = make_rec_env lbs bs  in
                translate cfg uu____4058 body)
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4062) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____4083  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____4096 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____4111  ->
                      match uu____4111 with
                      | (bv,t1) ->
                          let uu____4118 =
                            let uu____4125 = readback cfg t1  in
                            (bv, uu____4125)  in
                          FStar_Syntax_Syntax.NT uu____4118) uu____4096
                  in
               let uu____4130 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____4130  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close1 qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close1 qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu____4139 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____4146  ->
                    let uu____4147 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____4147);
               translate cfg bs t  in
             let uu____4150 =
               let uu____4165 = FStar_Thunk.mk f  in
               ((FStar_Util.Inl li), uu____4165)  in
             FStar_TypeChecker_NBETerm.Lazy uu____4150)

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
            let uu____4197 =
              let uu____4204 = translate cfg bs typ  in
              let uu____4205 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4204, uu____4205)  in
            FStar_TypeChecker_NBETerm.Tot uu____4197
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4220 =
              let uu____4227 = translate cfg bs typ  in
              let uu____4228 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4227, uu____4228)  in
            FStar_TypeChecker_NBETerm.GTot uu____4220
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4234 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4234

and (iapp :
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
              let uu____4296 = FStar_List.splitAt m targs  in
              (match uu____4296 with
               | (uu____4332,targs') ->
                   let targs'1 =
                     FStar_List.map
                       (fun targ  ->
                          fun l  ->
                            let uu____4423 =
                              let uu____4426 =
                                map_append FStar_Pervasives_Native.fst args l
                                 in
                              FStar_List.rev uu____4426  in
                            targ uu____4423) targs'
                      in
                   FStar_TypeChecker_NBETerm.Lam
                     (((fun l  ->
                          let uu____4462 =
                            map_append FStar_Pervasives_Native.fst args l  in
                          f1 uu____4462)), targs'1, (n1 - m), res))
            else
              if m = n1
              then
                (let uu____4473 =
                   FStar_List.map FStar_Pervasives_Native.fst args  in
                 f1 uu____4473)
              else
                (let uu____4482 = FStar_List.splitAt n1 args  in
                 match uu____4482 with
                 | (args1,args') ->
                     let uu____4529 =
                       let uu____4530 =
                         FStar_List.map FStar_Pervasives_Native.fst args1  in
                       f1 uu____4530  in
                     iapp cfg uu____4529 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____4649)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____4693 = aux args us ts  in
            (match uu____4693 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____4820)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____4864 = aux args us ts  in
            (match uu____4864 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
        | FStar_TypeChecker_NBETerm.TopLevelRec
            (lb,arity,decreases_list,args') ->
            let args1 = FStar_List.append args' args  in
            if (FStar_List.length args1) >= arity
            then
              let uu____4943 =
                should_reduce_recursive_definition args1 decreases_list  in
              (match uu____4943 with
               | (should_reduce,uu____4952,uu____4953) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                        in
                     (debug cfg
                        (fun uu____4961  ->
                           let uu____4962 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu____4962);
                      iapp cfg (FStar_TypeChecker_NBETerm.FV (fv, [], []))
                        args1)
                   else
                     (debug cfg
                        (fun uu____4982  ->
                           let uu____4983 =
                             let uu____4985 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Syntax_Print.fv_to_string uu____4985  in
                           FStar_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu____4983);
                      (let uu____4987 =
                         FStar_Util.first_N
                           (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
                           args1
                          in
                       match uu____4987 with
                       | (univs1,rest) ->
                           let uu____5034 =
                             let uu____5035 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 univs1
                                in
                             translate cfg uu____5035
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5034 rest)))
            else
              FStar_TypeChecker_NBETerm.TopLevelRec
                (lb, arity, decreases_list, args1)
        | FStar_TypeChecker_NBETerm.LocalLetRec
            (i,lb,mutual_lbs,local_env,acc_args,remaining_arity,decreases_list)
            ->
            if remaining_arity = Prims.int_zero
            then
              FStar_TypeChecker_NBETerm.LocalLetRec
                (i, lb, mutual_lbs, local_env,
                  (FStar_List.append acc_args args), remaining_arity,
                  decreases_list)
            else
              (let n_args = FStar_List.length args  in
               if n_args < remaining_arity
               then
                 FStar_TypeChecker_NBETerm.LocalLetRec
                   (i, lb, mutual_lbs, local_env,
                     (FStar_List.append acc_args args),
                     (remaining_arity - n_args), decreases_list)
               else
                 (let args1 = FStar_List.append acc_args args  in
                  let uu____5153 =
                    should_reduce_recursive_definition args1 decreases_list
                     in
                  match uu____5153 with
                  | (should_reduce,uu____5162,uu____5163) ->
                      if Prims.op_Negation should_reduce
                      then
                        FStar_TypeChecker_NBETerm.LocalLetRec
                          (i, lb, mutual_lbs, local_env, args1,
                            Prims.int_zero, decreases_list)
                      else
                        (let env = make_rec_env mutual_lbs local_env  in
                         debug cfg
                           (fun uu____5192  ->
                              (let uu____5194 =
                                 let uu____5196 =
                                   FStar_List.map
                                     FStar_TypeChecker_NBETerm.t_to_string
                                     env
                                    in
                                 FStar_String.concat ",\n\t " uu____5196  in
                               FStar_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu____5194);
                              (let uu____5203 =
                                 let uu____5205 =
                                   FStar_List.map
                                     (fun uu____5217  ->
                                        match uu____5217 with
                                        | (t,uu____5224) ->
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              t) args1
                                    in
                                 FStar_String.concat ",\n\t " uu____5205  in
                               FStar_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu____5203));
                         (let uu____5227 =
                            translate cfg env lb.FStar_Syntax_Syntax.lbdef
                             in
                          iapp cfg uu____5227 args1))))
        | FStar_TypeChecker_NBETerm.Quote uu____5228 ->
            let uu____5233 =
              let uu____5235 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____5235  in
            failwith uu____5233
        | FStar_TypeChecker_NBETerm.Reflect uu____5238 ->
            let uu____5239 =
              let uu____5241 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____5241  in
            failwith uu____5239
        | FStar_TypeChecker_NBETerm.Lazy uu____5244 ->
            let uu____5259 =
              let uu____5261 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____5261  in
            failwith uu____5259
        | FStar_TypeChecker_NBETerm.Constant uu____5264 ->
            let uu____5265 =
              let uu____5267 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____5267  in
            failwith uu____5265
        | FStar_TypeChecker_NBETerm.Univ uu____5270 ->
            let uu____5271 =
              let uu____5273 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____5273  in
            failwith uu____5271
        | FStar_TypeChecker_NBETerm.Type_t uu____5276 ->
            let uu____5277 =
              let uu____5279 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____5279  in
            failwith uu____5277
        | FStar_TypeChecker_NBETerm.Unknown  ->
            let uu____5282 =
              let uu____5284 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____5284  in
            failwith uu____5282
        | FStar_TypeChecker_NBETerm.Refinement uu____5287 ->
            let uu____5302 =
              let uu____5304 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____5304  in
            failwith uu____5302
        | FStar_TypeChecker_NBETerm.Arrow uu____5307 ->
            let uu____5328 =
              let uu____5330 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____5330  in
            failwith uu____5328

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
          let uu____5347 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____5348 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____5347 uu____5348  in
        let uu____5349 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____5349
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____5358 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____5360  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____5358 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____5367  ->
                     let uu____5368 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____5368);
                (let uu____5371 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____5371 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____5382  ->
                           let uu____5383 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n" uu____5383);
                      (let uu____5386 =
                         let uu____5419 =
                           let f uu____5447 uu____5448 =
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
                             let uu____5510 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 callbacks args'
                                in
                             match uu____5510 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____5521  ->
                                       let uu____5522 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____5524 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____5522 uu____5524);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____5532  ->
                                       let uu____5533 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____5533);
                                  (let uu____5536 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp cfg uu____5536 args'))), uu____5419,
                           arity, FStar_Pervasives_Native.None)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____5386))
                 | FStar_Pervasives_Native.Some uu____5546 ->
                     (debug1
                        (fun uu____5552  ->
                           let uu____5553 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____5553);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____5560 ->
                     (debug1
                        (fun uu____5568  ->
                           let uu____5569 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____5569);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               let is_qninfo_visible =
                 let uu____5578 =
                   FStar_TypeChecker_Env.lookup_definition_qninfo
                     cfg.FStar_TypeChecker_Cfg.delta_level
                     (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     qninfo
                    in
                 FStar_Option.isSome uu____5578  in
               if is_qninfo_visible
               then
                 (match qninfo with
                  | FStar_Pervasives_Native.Some
                      (FStar_Util.Inr
                       ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                          FStar_Syntax_Syntax.sigrng = uu____5593;
                          FStar_Syntax_Syntax.sigquals = uu____5594;
                          FStar_Syntax_Syntax.sigmeta = uu____5595;
                          FStar_Syntax_Syntax.sigattrs = uu____5596;
                          FStar_Syntax_Syntax.sigopts = uu____5597;_},_us_opt),_rng)
                      ->
                      (debug1
                         (fun uu____5667  ->
                            let uu____5668 =
                              FStar_Syntax_Print.fv_to_string fvar1  in
                            FStar_Util.print1 "(1) Decided to unfold %s\n"
                              uu____5668);
                       (let lbm = find_let lbs fvar1  in
                        match lbm with
                        | FStar_Pervasives_Native.Some lb ->
                            if
                              is_rec &&
                                (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                            then
                              let uu____5676 = let_rec_arity lb  in
                              (match uu____5676 with
                               | (ar,lst) ->
                                   FStar_TypeChecker_NBETerm.TopLevelRec
                                     (lb, ar, lst, []))
                            else translate_letbinding cfg bs lb
                        | FStar_Pervasives_Native.None  ->
                            failwith "Could not find let binding"))
                  | uu____5712 ->
                      (debug1
                         (fun uu____5718  ->
                            let uu____5719 =
                              FStar_Syntax_Print.fv_to_string fvar1  in
                            FStar_Util.print1 "(1) qninfo is None for (%s)\n"
                              uu____5719);
                       FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))
               else
                 (debug1
                    (fun uu____5733  ->
                       let uu____5734 = FStar_Syntax_Print.fv_to_string fvar1
                          in
                       FStar_Util.print1
                         "(1) qninfo is not visible at this level (%s)\n"
                         uu____5734);
                  FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               let is_qninfo_visible =
                 let uu____5743 =
                   FStar_TypeChecker_Env.lookup_definition_qninfo
                     cfg.FStar_TypeChecker_Cfg.delta_level
                     (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     qninfo
                    in
                 FStar_Option.isSome uu____5743  in
               if is_qninfo_visible
               then
                 (match qninfo with
                  | FStar_Pervasives_Native.Some
                      (FStar_Util.Inr
                       ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                          FStar_Syntax_Syntax.sigrng = uu____5758;
                          FStar_Syntax_Syntax.sigquals = uu____5759;
                          FStar_Syntax_Syntax.sigmeta = uu____5760;
                          FStar_Syntax_Syntax.sigattrs = uu____5761;
                          FStar_Syntax_Syntax.sigopts = uu____5762;_},_us_opt),_rng)
                      ->
                      (debug1
                         (fun uu____5832  ->
                            let uu____5833 =
                              FStar_Syntax_Print.fv_to_string fvar1  in
                            FStar_Util.print1 "(1) Decided to unfold %s\n"
                              uu____5833);
                       (let lbm = find_let lbs fvar1  in
                        match lbm with
                        | FStar_Pervasives_Native.Some lb ->
                            if
                              is_rec &&
                                (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                            then
                              let uu____5841 = let_rec_arity lb  in
                              (match uu____5841 with
                               | (ar,lst) ->
                                   FStar_TypeChecker_NBETerm.TopLevelRec
                                     (lb, ar, lst, []))
                            else translate_letbinding cfg bs lb
                        | FStar_Pervasives_Native.None  ->
                            failwith "Could not find let binding"))
                  | uu____5877 ->
                      (debug1
                         (fun uu____5883  ->
                            let uu____5884 =
                              FStar_Syntax_Print.fv_to_string fvar1  in
                            FStar_Util.print1 "(1) qninfo is None for (%s)\n"
                              uu____5884);
                       FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))
               else
                 (debug1
                    (fun uu____5898  ->
                       let uu____5899 = FStar_Syntax_Print.fv_to_string fvar1
                          in
                       FStar_Util.print1
                         "(1) qninfo is not visible at this level (%s)\n"
                         uu____5899);
                  FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

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
        | uu____5946 ->
            let uu____5949 =
              let uu____5982 =
                FStar_List.map
                  (fun uu____6007  ->
                     fun _ts  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____5982,
                (FStar_List.length us), FStar_Pervasives_Native.None)
               in
            FStar_TypeChecker_NBETerm.Lam uu____5949

and (mkRec :
  Prims.int ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        FStar_TypeChecker_NBETerm.t Prims.list -> FStar_TypeChecker_NBETerm.t)
  =
  fun i  ->
    fun b  ->
      fun bs  ->
        fun env  ->
          let uu____6067 = let_rec_arity b  in
          match uu____6067 with
          | (ar,ar_lst) ->
              FStar_TypeChecker_NBETerm.LocalLetRec
                (i, b, bs, env, [], ar, ar_lst)

and (make_rec_env :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_TypeChecker_NBETerm.t Prims.list)
  =
  fun all_lbs  ->
    fun all_outer_bs  ->
      let rec_bindings =
        FStar_List.mapi
          (fun i  -> fun lb  -> mkRec i lb all_lbs all_outer_bs) all_lbs
         in
      FStar_List.rev_append rec_bindings all_outer_bs

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____6137 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____6137
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____6146 ->
        let uu____6147 =
          let uu____6149 =
            let uu____6151 = FStar_Syntax_Print.const_to_string c  in
            Prims.op_Hat uu____6151 ": Not yet implemented"  in
          Prims.op_Hat "Tm_constant " uu____6149  in
        failwith uu____6147

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____6164 =
              let uu____6173 = readback cfg typ  in (uu____6173, u)  in
            FStar_Syntax_Syntax.Total uu____6164
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____6186 =
              let uu____6195 = readback cfg typ  in (uu____6195, u)  in
            FStar_Syntax_Syntax.GTotal uu____6186
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____6203 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____6203
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
        let uu____6209 = c  in
        match uu____6209 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____6229 =
              FStar_List.map (translate_univ cfg bs) comp_univs  in
            let uu____6230 = translate cfg bs result_typ  in
            let uu____6231 =
              FStar_List.map
                (fun x  ->
                   let uu____6259 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____6259, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____6266 = FStar_List.map (translate_flag cfg bs) flags  in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____6229;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____6230;
              FStar_TypeChecker_NBETerm.effect_args = uu____6231;
              FStar_TypeChecker_NBETerm.flags = uu____6266
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____6271 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____6274 =
        FStar_List.map
          (fun x  ->
             let uu____6300 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____6300, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____6301 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____6271;
        FStar_Syntax_Syntax.effect_args = uu____6274;
        FStar_Syntax_Syntax.flags = uu____6301
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
        let uu____6309 = c  in
        match uu____6309 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____6319 =
              FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____6324 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____6319;
              FStar_TypeChecker_NBETerm.residual_flags = uu____6324
            }

and (readback_residual_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____6329 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (readback cfg)
         in
      let uu____6336 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____6329;
        FStar_Syntax_Syntax.residual_flags = uu____6336
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
            let uu____6347 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____6347

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
          let uu____6351 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____6351

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____6354  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____6354 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____6392 =
                     let uu____6401 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____6401
                      in
                   (match uu____6392 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6408 =
                          let uu____6410 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____6410
                           in
                        failwith uu____6408
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___966_6426 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___966_6426.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___966_6426.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___966_6426.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___966_6426.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___966_6426.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___966_6426.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___966_6426.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___966_6426.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____6434 =
                            let uu____6441 =
                              let uu____6442 =
                                let uu____6461 =
                                  let uu____6470 =
                                    let uu____6477 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____6477,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____6470]  in
                                (uu____6461, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____6442  in
                            FStar_Syntax_Syntax.mk uu____6441  in
                          uu____6434 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____6511 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____6511
                          then
                            let uu____6520 =
                              let uu____6525 =
                                let uu____6526 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____6526  in
                              (uu____6525, FStar_Pervasives_Native.None)  in
                            let uu____6527 =
                              let uu____6534 =
                                let uu____6539 =
                                  let uu____6540 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____6540  in
                                (uu____6539, FStar_Pervasives_Native.None)
                                 in
                              [uu____6534]  in
                            uu____6520 :: uu____6527
                          else []  in
                        let t =
                          let uu____6560 =
                            let uu____6561 =
                              let uu____6562 =
                                let uu____6563 =
                                  let uu____6564 =
                                    let uu____6571 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____6571
                                      FStar_Util.must
                                     in
                                  FStar_All.pipe_right uu____6564
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Syntax_Util.un_uinst uu____6563  in
                              translate cfg' [] uu____6562  in
                            iapp cfg uu____6561
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____6604 =
                            let uu____6605 =
                              let uu____6612 =
                                let uu____6617 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____6617, FStar_Pervasives_Native.None)
                                 in
                              let uu____6618 =
                                let uu____6625 =
                                  let uu____6630 = translate cfg' bs ty  in
                                  (uu____6630, FStar_Pervasives_Native.None)
                                   in
                                [uu____6625]  in
                              uu____6612 :: uu____6618  in
                            let uu____6643 =
                              let uu____6650 =
                                let uu____6657 =
                                  let uu____6664 =
                                    let uu____6669 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____6669,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____6670 =
                                    let uu____6677 =
                                      let uu____6684 =
                                        let uu____6689 =
                                          translate cfg bs body_lam  in
                                        (uu____6689,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____6684]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____6677
                                     in
                                  uu____6664 :: uu____6670  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____6657
                                 in
                              FStar_List.append maybe_range_arg uu____6650
                               in
                            FStar_List.append uu____6605 uu____6643  in
                          iapp cfg uu____6560 uu____6604  in
                        (debug cfg
                           (fun uu____6721  ->
                              let uu____6722 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____6722);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____6725);
                      FStar_Syntax_Syntax.pos = uu____6726;
                      FStar_Syntax_Syntax.vars = uu____6727;_},(e2,uu____6729)::[])
                   ->
                   translate
                     (let uu___988_6770 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___988_6770.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___988_6770.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___988_6770.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___988_6770.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___988_6770.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___988_6770.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___988_6770.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___988_6770.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   (debug cfg
                      (fun uu____6802  ->
                         let uu____6803 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____6805 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____6803
                           uu____6805);
                    (let fallback1 uu____6813 = translate cfg bs e1  in
                     let fallback2 uu____6819 =
                       let uu____6820 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           FStar_Pervasives_Native.None
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate
                         (let uu___1000_6827 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___1000_6827.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___1000_6827.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___1000_6827.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___1000_6827.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___1000_6827.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___1000_6827.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___1000_6827.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___1000_6827.FStar_TypeChecker_Cfg.normalize_pure_lets);
                            FStar_TypeChecker_Cfg.reifying = false
                          }) bs uu____6820
                        in
                     let uu____6829 =
                       let uu____6830 = FStar_Syntax_Util.un_uinst head1  in
                       uu____6830.FStar_Syntax_Syntax.n  in
                     match uu____6829 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             cfg.FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____6836 =
                           let uu____6838 =
                             FStar_TypeChecker_Env.is_action
                               cfg.FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____6838  in
                         if uu____6836
                         then fallback1 ()
                         else
                           (let uu____6843 =
                              let uu____6845 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  cfg.FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____6845  in
                            if uu____6843
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____6862 =
                                   let uu____6867 =
                                     FStar_Syntax_Util.mk_reify head1  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____6867
                                     args
                                    in
                                 uu____6862 FStar_Pervasives_Native.None
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               translate
                                 (let uu___1009_6870 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1009_6870.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1009_6870.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1009_6870.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1009_6870.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1009_6870.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong =
                                      (uu___1009_6870.FStar_TypeChecker_Cfg.strong);
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1009_6870.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1009_6870.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying = false
                                  }) bs e2))
                     | uu____6872 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____6993  ->
                             match uu____6993 with
                             | (pat,wopt,tm) ->
                                 let uu____7041 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____7041)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   translate
                     (let uu___1022_7075 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___1022_7075.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1022_7075.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1022_7075.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___1022_7075.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1022_7075.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1022_7075.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1022_7075.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___1022_7075.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____7078) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____7105 ->
                   let uu____7106 =
                     let uu____7108 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____7108
                      in
                   failwith uu____7106)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7111  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7111 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____7135 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____7135
              then
                let ed =
                  let uu____7139 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____7139
                   in
                let ret1 =
                  let uu____7141 =
                    let uu____7142 =
                      let uu____7145 =
                        let uu____7146 =
                          let uu____7153 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_return_repr
                             in
                          FStar_All.pipe_right uu____7153 FStar_Util.must  in
                        FStar_All.pipe_right uu____7146
                          FStar_Pervasives_Native.snd
                         in
                      FStar_Syntax_Subst.compress uu____7145  in
                    uu____7142.FStar_Syntax_Syntax.n  in
                  match uu____7141 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret1,uu____7199::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret1, [FStar_Syntax_Syntax.U_unknown]))
                        FStar_Pervasives_Native.None
                        e1.FStar_Syntax_Syntax.pos
                  | uu____7206 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' =
                  let uu___1055_7209 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___1055_7209.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1055_7209.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1055_7209.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___1055_7209.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1055_7209.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1055_7209.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1055_7209.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1055_7209.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let t =
                  let uu____7212 =
                    let uu____7213 = translate cfg' [] ret1  in
                    iapp cfg' uu____7213
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____7222 =
                    let uu____7223 =
                      let uu____7228 = translate cfg' bs ty  in
                      (uu____7228, FStar_Pervasives_Native.None)  in
                    let uu____7229 =
                      let uu____7236 =
                        let uu____7241 = translate cfg' bs e1  in
                        (uu____7241, FStar_Pervasives_Native.None)  in
                      [uu____7236]  in
                    uu____7223 :: uu____7229  in
                  iapp cfg' uu____7212 uu____7222  in
                (debug cfg
                   (fun uu____7257  ->
                      let uu____7258 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____7258);
                 t)
              else
                (let uu____7263 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____7263 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____7266 =
                       let uu____7268 = FStar_Ident.text_of_lid msrc  in
                       let uu____7270 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____7268 uu____7270
                        in
                     failwith uu____7266
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7273;
                       FStar_TypeChecker_Env.mtarget = uu____7274;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7275;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____7295 =
                       let uu____7297 = FStar_Ident.text_of_lid msrc  in
                       let uu____7299 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____7297 uu____7299
                        in
                     failwith uu____7295
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7302;
                       FStar_TypeChecker_Env.mtarget = uu____7303;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7304;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____7338 =
                         let uu____7341 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty uu____7341  in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____7338
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___1079_7357 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___1079_7357.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1079_7357.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1079_7357.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___1079_7357.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1079_7357.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1079_7357.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1079_7357.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___1079_7357.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let t =
                       let uu____7360 = translate cfg' [] lift_lam  in
                       let uu____7361 =
                         let uu____7362 =
                           let uu____7367 = translate cfg bs e1  in
                           (uu____7367, FStar_Pervasives_Native.None)  in
                         [uu____7362]  in
                       iapp cfg uu____7360 uu____7361  in
                     (debug cfg
                        (fun uu____7379  ->
                           let uu____7380 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____7380);
                      t))

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____7398  ->
           let uu____7399 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____7399);
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
           let uu____7407 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____7407 FStar_Syntax_Util.exp_int
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
           let uu____7471 =
             FStar_List.fold_left
               (fun uu____7514  ->
                  fun tf  ->
                    match uu____7514 with
                    | (args_rev,accus_rev) ->
                        let uu____7566 = tf accus_rev  in
                        (match uu____7566 with
                         | (xt,q) ->
                             let x1 =
                               let uu____7586 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____7586
                                in
                             let uu____7587 =
                               let uu____7590 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____7590 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____7587))) ([], [])
               targs
              in
           (match uu____7471 with
            | (args_rev,accus_rev) ->
                let accus = FStar_List.rev accus_rev  in
                let body =
                  let uu____7637 = f accus  in readback cfg uu____7637  in
                let uu____7638 =
                  FStar_Util.map_opt resc
                    (fun thunk1  ->
                       let uu____7653 = thunk1 accus  in
                       readback_residual_comp cfg uu____7653)
                   in
                FStar_Syntax_Util.abs (FStar_List.rev args_rev) body
                  uu____7638)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____7681 =
               let uu____7682 =
                 let uu____7683 = targ ()  in
                 FStar_Pervasives_Native.fst uu____7683  in
               readback cfg uu____7682  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____7681
              in
           let body =
             let uu____7689 =
               let uu____7690 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____7690  in
             readback cfg uu____7689  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t  in FStar_Syntax_Util.mk_reflect tm
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____7727 =
             FStar_List.fold_left
               (fun uu____7770  ->
                  fun tf  ->
                    match uu____7770 with
                    | (args_rev,accus_rev) ->
                        let uu____7822 = tf accus_rev  in
                        (match uu____7822 with
                         | (xt,q) ->
                             let x1 =
                               let uu____7842 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____7842
                                in
                             let uu____7843 =
                               let uu____7846 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____7846 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____7843))) ([], [])
               targs
              in
           (match uu____7727 with
            | (args_rev,accus_rev) ->
                let cmp =
                  let uu____7890 = f (FStar_List.rev accus_rev)  in
                  readback_comp cfg uu____7890  in
                FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____7933  ->
                  match uu____7933 with
                  | (x1,q) ->
                      let uu____7944 = readback cfg x1  in (uu____7944, q))
               args
              in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____7963 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____7970::uu____7971 ->
                let uu____7974 =
                  let uu____7977 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____7977
                    (FStar_List.rev us)
                   in
                apply1 uu____7974
            | [] ->
                let uu____7978 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply1 uu____7978)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____8019  ->
                  match uu____8019 with
                  | (x1,q) ->
                      let uu____8030 = readback cfg x1  in (uu____8030, q))
               args
              in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____8049 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____8056::uu____8057 ->
                let uu____8060 =
                  let uu____8063 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____8063
                    (FStar_List.rev us)
                   in
                apply1 uu____8060
            | [] ->
                let uu____8064 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply1 uu____8064)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____8111  ->
                  match uu____8111 with
                  | (x1,q) ->
                      let uu____8122 = readback cfg x1  in (uu____8122, q))
               ts
              in
           let uu____8123 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____8123 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____8183  ->
                  match uu____8183 with
                  | (x1,q) ->
                      let uu____8194 = readback cfg x1  in (uu____8194, q))
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
            | uu____8224 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.TopLevelRec
           (lb,uu____8232,uu____8233,args) ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let head1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 =
             FStar_List.map
               (fun uu____8278  ->
                  match uu____8278 with
                  | (t,q) ->
                      let uu____8289 = readback cfg t  in (uu____8289, q))
               args
              in
           FStar_Syntax_Util.mk_app head1 args1
       | FStar_TypeChecker_NBETerm.LocalLetRec
           (i,uu____8291,lbs,bs,args,_ar,_ar_lst) ->
           let lbnames =
             FStar_List.map
               (fun lb  ->
                  let uu____8333 =
                    let uu____8335 =
                      let uu____8336 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      uu____8336.FStar_Syntax_Syntax.ppname  in
                    FStar_Ident.text_of_id uu____8335  in
                  FStar_Syntax_Syntax.gen_bv uu____8333
                    FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp)
               lbs
              in
           let let_rec_env =
             let uu____8340 =
               FStar_List.map
                 (fun x1  ->
                    FStar_TypeChecker_NBETerm.Accu
                      ((FStar_TypeChecker_NBETerm.Var x1), [])) lbnames
                in
             FStar_List.rev_append uu____8340 bs  in
           let lbs1 =
             FStar_List.map2
               (fun lb  ->
                  fun lbname  ->
                    let lbdef =
                      let uu____8366 =
                        translate cfg let_rec_env
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      readback cfg uu____8366  in
                    let lbtyp =
                      let uu____8368 =
                        translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                      readback cfg uu____8368  in
                    let uu___1256_8369 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = (FStar_Util.Inl lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___1256_8369.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___1256_8369.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbdef;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___1256_8369.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___1256_8369.FStar_Syntax_Syntax.lbpos)
                    }) lbs lbnames
              in
           let body =
             let uu____8371 = FStar_List.nth lbnames i  in
             FStar_Syntax_Syntax.bv_to_name uu____8371  in
           let uu____8372 = FStar_Syntax_Subst.close_let_rec lbs1 body  in
           (match uu____8372 with
            | (lbs2,body1) ->
                let head1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body1))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                let args1 =
                  FStar_List.map
                    (fun uu____8420  ->
                       match uu____8420 with
                       | (x1,q) ->
                           let uu____8431 = readback cfg x1  in
                           (uu____8431, q)) args
                   in
                FStar_Syntax_Util.mk_app head1 args1)
       | FStar_TypeChecker_NBETerm.UnreducedLet (var,typ,defn,body,lb) ->
           let typ1 = readback cfg typ  in
           let defn1 = readback cfg defn  in
           let body1 =
             let uu____8440 = readback cfg body  in
             FStar_Syntax_Subst.close [(var, FStar_Pervasives_Native.None)]
               uu____8440
              in
           let lbname =
             let uu____8460 =
               let uu___1278_8461 =
                 FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___1278_8461.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___1278_8461.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = typ1
               }  in
             FStar_Util.Inl uu____8460  in
           let lb1 =
             let uu___1281_8463 = lb  in
             {
               FStar_Syntax_Syntax.lbname = lbname;
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1281_8463.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = typ1;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1281_8463.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef = defn1;
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1281_8463.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1281_8463.FStar_Syntax_Syntax.lbpos)
             }  in
           FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.UnreducedLetRec (vars_typs_defns,body,lbs)
           ->
           let lbs1 =
             FStar_List.map2
               (fun uu____8518  ->
                  fun lb  ->
                    match uu____8518 with
                    | (v1,t,d) ->
                        let t1 = readback cfg t  in
                        let def = readback cfg d  in
                        let v2 =
                          let uu___1296_8532 = v1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1296_8532.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1296_8532.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        let uu___1299_8533 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl v2);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1299_8533.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = t1;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1299_8533.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1299_8533.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1299_8533.FStar_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs
              in
           let body1 = readback cfg body  in
           let uu____8535 = FStar_Syntax_Subst.close_let_rec lbs1 body1  in
           (match uu____8535 with
            | (lbs2,body2) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body2))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____8566) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (uu____8583,thunk1) ->
           let uu____8605 = FStar_Thunk.force thunk1  in
           readback cfg uu____8605)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____8634 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____8646 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____8667 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____8694 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____8718 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____8729 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___1_8736  ->
    match uu___1_8736 with
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
            let uu___1337_8775 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1339_8778 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1339_8778.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1337_8775.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1337_8775.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1337_8775.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1337_8775.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1337_8775.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1337_8775.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1337_8775.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1337_8775.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____8783  ->
               let uu____8784 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with (%s) {\n" uu____8784);
          (let r =
             let uu____8788 = translate cfg1 [] e  in
             readback cfg1 uu____8788  in
           debug cfg1
             (fun uu____8792  ->
                let uu____8793 = FStar_Syntax_Print.term_to_string r  in
                FStar_Util.print1 "}\nNBE returned (%s)\n" uu____8793);
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
          let uu___1354_8818 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1356_8821 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1356_8821.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1354_8818.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1354_8818.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1354_8818.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1354_8818.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1354_8818.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1354_8818.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1354_8818.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1354_8818.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____8826  ->
             let uu____8827 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____8827);
        (let r =
           let uu____8831 = translate cfg1 [] e  in readback cfg1 uu____8831
            in
         debug cfg1
           (fun uu____8835  ->
              let uu____8836 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____8836);
         r)
  