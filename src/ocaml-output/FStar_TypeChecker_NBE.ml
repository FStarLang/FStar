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
        let all_branches = branches  in
        let rec pickBranch_aux scrut1 branches1 branches0 =
          let rec matches_pat scrutinee0 p =
            debug cfg
              (fun uu____672  ->
                 let uu____673 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0  in
                 let uu____675 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____673
                   uu____675);
            (let scrutinee = unlazy scrutinee0  in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____702 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____729  ->
                          let uu____730 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____732 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu____730
                            uu____732);
                     (match c with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____742 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____759 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____759
                           | uu____760 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____763))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____768) ->
                               st = p1
                           | uu____772 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____780 -> false)
                      | uu____782 -> false)
                      in
                   let uu____784 = matches_const scrutinee s  in
                   if uu____784
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____922)::rest_a,(p2,uu____925)::rest_p) ->
                         let uu____964 = matches_pat t p2  in
                         (match uu____964 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____993 -> FStar_Util.Inr false  in
                   (match scrutinee with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____1041 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                        if uu____1041
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____1061 -> FStar_Util.Inr true)
                in
             let res_to_string uu___0_1079 =
               match uu___0_1079 with
               | FStar_Util.Inr b ->
                   let uu____1093 = FStar_Util.string_of_bool b  in
                   Prims.op_Hat "Inr " uu____1093
               | FStar_Util.Inl bs ->
                   let uu____1102 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.op_Hat "Inl " uu____1102
                in
             debug cfg
               (fun uu____1110  ->
                  let uu____1111 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____1113 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____1115 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____1111
                    uu____1113 uu____1115);
             r)
             in
          match branches1 with
          | [] -> FStar_Pervasives_Native.None
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
                  (fun uu____2204  ->
                     let uu____2205 = FStar_TypeChecker_NBETerm.t_to_string t
                        in
                     let uu____2207 =
                       let uu____2209 =
                         FStar_List.map FStar_TypeChecker_NBETerm.t_to_string
                           bs
                          in
                       FStar_All.pipe_right uu____2209
                         (FStar_String.concat "; ")
                        in
                     FStar_Util.print2
                       "Resolved bvar to %s\n\tcontext is [%s]\n" uu____2205
                       uu____2207);
                t)
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____2236  ->
                   let uu____2237 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2239 =
                     let uu____2241 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2241
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____2237 uu____2239);
              (let uu____2252 = translate cfg bs t  in
               let uu____2253 =
                 FStar_List.map
                   (fun x  ->
                      let uu____2257 =
                        let uu____2258 = translate_univ cfg bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____2258  in
                      FStar_TypeChecker_NBETerm.as_arg uu____2257) us
                  in
               iapp cfg uu____2252 uu____2253))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2260 = translate_univ cfg bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____2260
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let uu____2283 =
               let uu____2304 =
                 FStar_List.fold_right
                   (fun x  ->
                      fun formals  ->
                        let next_formal prefix_of_xs_rev =
                          let uu____2374 =
                            translate cfg
                              (FStar_List.append prefix_of_xs_rev bs)
                              (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                             in
                          (uu____2374, (FStar_Pervasives_Native.snd x))  in
                        next_formal :: formals) xs []
                  in
               ((fun ys  ->
                   translate_comp cfg (FStar_List.rev_append ys bs) c),
                 uu____2304)
                in
             FStar_TypeChecker_NBETerm.Arrow uu____2283
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             if
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
             then translate cfg bs bv.FStar_Syntax_Syntax.sort
             else
               FStar_TypeChecker_NBETerm.Refinement
                 (((fun y  -> translate cfg (y :: bs) tm)),
                   ((fun uu____2446  ->
                       let uu____2447 =
                         translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                       FStar_TypeChecker_NBETerm.as_arg uu____2447)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2449,uu____2450) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2512,uu____2513) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             (debug1
                (fun uu____2569  ->
                   let uu____2570 =
                     match resc with
                     | FStar_Pervasives_Native.Some
                         { FStar_Syntax_Syntax.residual_effect = uu____2573;
                           FStar_Syntax_Syntax.residual_typ =
                             FStar_Pervasives_Native.Some t;
                           FStar_Syntax_Syntax.residual_flags = uu____2575;_}
                         -> FStar_Syntax_Print.term_to_string t
                     | uu____2582 -> "None"  in
                   FStar_Util.print1
                     "Translating lambda with residual type %s\n" uu____2570);
              (let arity = FStar_List.length xs  in
               let uu____2594 =
                 let uu____2627 =
                   FStar_List.fold_right
                     (fun x  ->
                        fun formals  ->
                          let next_formal prefix_of_xs_rev =
                            let uu____2697 =
                              translate cfg
                                (FStar_List.append prefix_of_xs_rev bs)
                                (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                               in
                            (uu____2697, (FStar_Pervasives_Native.snd x))  in
                          next_formal :: formals) xs []
                    in
                 let uu____2726 =
                   FStar_Util.map_opt resc
                     (fun c  ->
                        fun formals  ->
                          translate_residual_comp cfg
                            (FStar_List.rev_append formals bs) c)
                    in
                 ((fun ys  ->
                     translate cfg (FStar_List.rev_append ys bs) body),
                   uu____2627, arity, uu____2726)
                  in
               FStar_TypeChecker_NBETerm.Lam uu____2594))
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____2774;
                FStar_Syntax_Syntax.vars = uu____2775;_},arg::more::args)
             ->
             let uu____2835 = FStar_Syntax_Util.head_and_args e  in
             (match uu____2835 with
              | (head1,uu____2853) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____2897 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____2897)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____2906);
                FStar_Syntax_Syntax.pos = uu____2907;
                FStar_Syntax_Syntax.vars = uu____2908;_},arg::more::args)
             ->
             let uu____2968 = FStar_Syntax_Util.head_and_args e  in
             (match uu____2968 with
              | (head1,uu____2986) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3030 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3030)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3039);
                FStar_Syntax_Syntax.pos = uu____3040;
                FStar_Syntax_Syntax.vars = uu____3041;_},arg::[])
             when cfg.FStar_TypeChecker_Cfg.reifying ->
             let cfg1 =
               let uu___430_3082 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___430_3082.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___430_3082.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___430_3082.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___430_3082.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___430_3082.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___430_3082.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___430_3082.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___430_3082.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = false
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3088);
                FStar_Syntax_Syntax.pos = uu____3089;
                FStar_Syntax_Syntax.vars = uu____3090;_},arg::[])
             ->
             let uu____3130 =
               translate cfg bs (FStar_Pervasives_Native.fst arg)  in
             FStar_TypeChecker_NBETerm.Reflect uu____3130
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3135;
                FStar_Syntax_Syntax.vars = uu____3136;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___453_3178 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___453_3178.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___453_3178.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___453_3178.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___453_3178.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___453_3178.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___453_3178.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___453_3178.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___453_3178.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____3217  ->
                   let uu____3218 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3220 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3218
                     uu____3220);
              (let uu____3223 = translate cfg bs head1  in
               let uu____3224 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3246 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3246, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3223 uu____3224))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches uu____3298 =
               let cfg1 =
                 let uu___469_3302 = cfg  in
                 {
                   FStar_TypeChecker_Cfg.steps =
                     (let uu___471_3305 = cfg.FStar_TypeChecker_Cfg.steps  in
                      {
                        FStar_TypeChecker_Cfg.beta =
                          (uu___471_3305.FStar_TypeChecker_Cfg.beta);
                        FStar_TypeChecker_Cfg.iota =
                          (uu___471_3305.FStar_TypeChecker_Cfg.iota);
                        FStar_TypeChecker_Cfg.zeta = false;
                        FStar_TypeChecker_Cfg.weak =
                          (uu___471_3305.FStar_TypeChecker_Cfg.weak);
                        FStar_TypeChecker_Cfg.hnf =
                          (uu___471_3305.FStar_TypeChecker_Cfg.hnf);
                        FStar_TypeChecker_Cfg.primops =
                          (uu___471_3305.FStar_TypeChecker_Cfg.primops);
                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                          (uu___471_3305.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                        FStar_TypeChecker_Cfg.unfold_until =
                          (uu___471_3305.FStar_TypeChecker_Cfg.unfold_until);
                        FStar_TypeChecker_Cfg.unfold_only =
                          (uu___471_3305.FStar_TypeChecker_Cfg.unfold_only);
                        FStar_TypeChecker_Cfg.unfold_fully =
                          (uu___471_3305.FStar_TypeChecker_Cfg.unfold_fully);
                        FStar_TypeChecker_Cfg.unfold_attr =
                          (uu___471_3305.FStar_TypeChecker_Cfg.unfold_attr);
                        FStar_TypeChecker_Cfg.unfold_tac =
                          (uu___471_3305.FStar_TypeChecker_Cfg.unfold_tac);
                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                          =
                          (uu___471_3305.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                        FStar_TypeChecker_Cfg.simplify =
                          (uu___471_3305.FStar_TypeChecker_Cfg.simplify);
                        FStar_TypeChecker_Cfg.erase_universes =
                          (uu___471_3305.FStar_TypeChecker_Cfg.erase_universes);
                        FStar_TypeChecker_Cfg.allow_unbound_universes =
                          (uu___471_3305.FStar_TypeChecker_Cfg.allow_unbound_universes);
                        FStar_TypeChecker_Cfg.reify_ =
                          (uu___471_3305.FStar_TypeChecker_Cfg.reify_);
                        FStar_TypeChecker_Cfg.compress_uvars =
                          (uu___471_3305.FStar_TypeChecker_Cfg.compress_uvars);
                        FStar_TypeChecker_Cfg.no_full_norm =
                          (uu___471_3305.FStar_TypeChecker_Cfg.no_full_norm);
                        FStar_TypeChecker_Cfg.check_no_uvars =
                          (uu___471_3305.FStar_TypeChecker_Cfg.check_no_uvars);
                        FStar_TypeChecker_Cfg.unmeta =
                          (uu___471_3305.FStar_TypeChecker_Cfg.unmeta);
                        FStar_TypeChecker_Cfg.unascribe =
                          (uu___471_3305.FStar_TypeChecker_Cfg.unascribe);
                        FStar_TypeChecker_Cfg.in_full_norm_request =
                          (uu___471_3305.FStar_TypeChecker_Cfg.in_full_norm_request);
                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                          (uu___471_3305.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                        FStar_TypeChecker_Cfg.nbe_step =
                          (uu___471_3305.FStar_TypeChecker_Cfg.nbe_step);
                        FStar_TypeChecker_Cfg.for_extraction =
                          (uu___471_3305.FStar_TypeChecker_Cfg.for_extraction)
                      });
                   FStar_TypeChecker_Cfg.tcenv =
                     (uu___469_3302.FStar_TypeChecker_Cfg.tcenv);
                   FStar_TypeChecker_Cfg.debug =
                     (uu___469_3302.FStar_TypeChecker_Cfg.debug);
                   FStar_TypeChecker_Cfg.delta_level =
                     (uu___469_3302.FStar_TypeChecker_Cfg.delta_level);
                   FStar_TypeChecker_Cfg.primitive_steps =
                     (uu___469_3302.FStar_TypeChecker_Cfg.primitive_steps);
                   FStar_TypeChecker_Cfg.strong =
                     (uu___469_3302.FStar_TypeChecker_Cfg.strong);
                   FStar_TypeChecker_Cfg.memoize_lazy =
                     (uu___469_3302.FStar_TypeChecker_Cfg.memoize_lazy);
                   FStar_TypeChecker_Cfg.normalize_pure_lets =
                     (uu___469_3302.FStar_TypeChecker_Cfg.normalize_pure_lets);
                   FStar_TypeChecker_Cfg.reifying =
                     (uu___469_3302.FStar_TypeChecker_Cfg.reifying)
                 }  in
               let rec process_pattern bs1 p =
                 let uu____3334 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____3370 =
                         FStar_List.fold_left
                           (fun uu____3411  ->
                              fun uu____3412  ->
                                match (uu____3411, uu____3412) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3504 = process_pattern bs2 arg
                                       in
                                    (match uu____3504 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3370 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____3603 =
                           let uu____3604 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3604  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3603
                          in
                       let uu____3605 =
                         let uu____3608 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3608 :: bs1  in
                       (uu____3605, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3613 =
                           let uu____3614 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3614  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3613
                          in
                       let uu____3615 =
                         let uu____3618 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3618 :: bs1  in
                       (uu____3615, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3628 =
                           let uu____3629 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3629  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3628
                          in
                       let uu____3630 =
                         let uu____3631 =
                           let uu____3638 =
                             let uu____3641 = translate cfg1 bs1 tm  in
                             readback cfg1 uu____3641  in
                           (x, uu____3638)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3631  in
                       (bs1, uu____3630)
                    in
                 match uu____3334 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___509_3661 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___509_3661.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____3680  ->
                    match uu____3680 with
                    | (pat,when_clause,e1) ->
                        let uu____3702 = process_pattern bs pat  in
                        (match uu____3702 with
                         | (bs',pat') ->
                             let uu____3715 =
                               let uu____3716 =
                                 let uu____3719 = translate cfg1 bs' e1  in
                                 readback cfg1 uu____3719  in
                               (pat', when_clause, uu____3716)  in
                             FStar_Syntax_Util.branch uu____3715)) branches
                in
             let scrut1 = translate cfg bs scrut  in
             (debug1
                (fun uu____3736  ->
                   let uu____3737 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3739 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.print2 "%s: Translating match %s\n" uu____3737
                     uu____3739);
              (let scrut2 = unlazy scrut1  in
               match scrut2 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3767  ->
                         let uu____3768 =
                           let uu____3770 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3796  ->
                                     match uu____3796 with
                                     | (x,q) ->
                                         let uu____3810 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.op_Hat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3810))
                              in
                           FStar_All.pipe_right uu____3770
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3768);
                    (let uu____3824 = pickBranch cfg scrut2 branches  in
                     match uu____3824 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____3845 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____3845 branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   (debug1
                      (fun uu____3868  ->
                         let uu____3869 =
                           FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                         FStar_Util.print1 "Match constant : %s\n" uu____3869);
                    (let uu____3872 = pickBranch cfg scrut2 branches  in
                     match uu____3872 with
                     | FStar_Pervasives_Native.Some (branch1,[]) ->
                         translate cfg bs branch1
                     | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                         translate cfg (arg :: bs) branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches
                     | FStar_Pervasives_Native.Some (uu____3906,hd1::tl1) ->
                         failwith
                           "Impossible: Matching on constants cannot bind more than one variable"))
               | uu____3920 ->
                   FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 make_branches))
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic (m,t)) when
             cfg.FStar_TypeChecker_Cfg.reifying ->
             translate_monadic (m, t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t)) when
             cfg.FStar_TypeChecker_Cfg.reifying ->
             translate_monadic_lift (m, m', t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
             let uu____3965 =
               FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
             if uu____3965
             then
               let uu____3968 =
                 ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    &&
                    (FStar_Syntax_Util.is_unit lb.FStar_Syntax_Syntax.lbtyp))
                   &&
                   (FStar_Syntax_Util.is_pure_or_ghost_effect
                      lb.FStar_Syntax_Syntax.lbeff)
                  in
               (if uu____3968
                then
                  let bs1 =
                    (FStar_TypeChecker_NBETerm.Constant
                       FStar_TypeChecker_NBETerm.Unit)
                    :: bs  in
                  translate cfg bs1 body
                else
                  (let bs1 =
                     let uu____3979 = translate_letbinding cfg bs lb  in
                     uu____3979 :: bs  in
                   translate cfg bs1 body))
             else
               (let def uu____3987 =
                  let uu____3988 =
                    ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                       &&
                       (FStar_Syntax_Util.is_unit
                          lb.FStar_Syntax_Syntax.lbtyp))
                      &&
                      (FStar_Syntax_Util.is_pure_or_ghost_effect
                         lb.FStar_Syntax_Syntax.lbeff)
                     in
                  if uu____3988
                  then
                    FStar_TypeChecker_NBETerm.Constant
                      FStar_TypeChecker_NBETerm.Unit
                  else translate cfg bs lb.FStar_Syntax_Syntax.lbdef  in
                let typ uu____3998 =
                  translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                let name =
                  let uu____4000 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.freshen_bv uu____4000  in
                let bs1 =
                  (FStar_TypeChecker_NBETerm.Accu
                     ((FStar_TypeChecker_NBETerm.Var name), []))
                  :: bs  in
                let body1 uu____4019 = translate cfg bs1 body  in
                let uu____4020 =
                  let uu____4031 =
                    let uu____4032 =
                      let uu____4049 = FStar_Thunk.mk typ  in
                      let uu____4052 = FStar_Thunk.mk def  in
                      let uu____4055 = FStar_Thunk.mk body1  in
                      (name, uu____4049, uu____4052, uu____4055, lb)  in
                    FStar_TypeChecker_NBETerm.UnreducedLet uu____4032  in
                  (uu____4031, [])  in
                FStar_TypeChecker_NBETerm.Accu uu____4020)
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
                      let uu____4101 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.freshen_bv uu____4101) lbs
                  in
               let typs =
                 FStar_List.map
                   (fun lb  -> translate cfg bs lb.FStar_Syntax_Syntax.lbtyp)
                   lbs
                  in
               let rec_bs =
                 let uu____4110 =
                   FStar_List.map
                     (fun v1  ->
                        FStar_TypeChecker_NBETerm.Accu
                          ((FStar_TypeChecker_NBETerm.Var v1), [])) vars
                    in
                 FStar_List.append uu____4110 bs  in
               let defs =
                 FStar_List.map
                   (fun lb  ->
                      translate cfg rec_bs lb.FStar_Syntax_Syntax.lbdef) lbs
                  in
               let body1 = translate cfg rec_bs body  in
               let uu____4131 =
                 let uu____4142 =
                   let uu____4143 =
                     let uu____4160 = FStar_List.zip3 vars typs defs  in
                     (uu____4160, body1, lbs)  in
                   FStar_TypeChecker_NBETerm.UnreducedLetRec uu____4143  in
                 (uu____4142, [])  in
               FStar_TypeChecker_NBETerm.Accu uu____4131
             else
               (let uu____4191 = make_rec_env lbs bs  in
                translate cfg uu____4191 body)
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4195) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____4216  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____4229 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____4244  ->
                      match uu____4244 with
                      | (bv,t1) ->
                          let uu____4251 =
                            let uu____4258 = readback cfg t1  in
                            (bv, uu____4258)  in
                          FStar_Syntax_Syntax.NT uu____4251) uu____4229
                  in
               let uu____4263 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____4263  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close1 qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close1 qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu____4272 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____4279  ->
                    let uu____4280 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____4280);
               translate cfg bs t  in
             let uu____4283 =
               let uu____4298 = FStar_Thunk.mk f  in
               ((FStar_Util.Inl li), uu____4298)  in
             FStar_TypeChecker_NBETerm.Lazy uu____4283)

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
            let uu____4330 =
              let uu____4337 = translate cfg bs typ  in
              let uu____4338 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4337, uu____4338)  in
            FStar_TypeChecker_NBETerm.Tot uu____4330
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4353 =
              let uu____4360 = translate cfg bs typ  in
              let uu____4361 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4360, uu____4361)  in
            FStar_TypeChecker_NBETerm.GTot uu____4353
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4367 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4367

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
              let uu____4429 = FStar_List.splitAt m targs  in
              (match uu____4429 with
               | (uu____4465,targs') ->
                   let targs'1 =
                     FStar_List.map
                       (fun targ  ->
                          fun l  ->
                            let uu____4556 =
                              let uu____4559 =
                                map_append FStar_Pervasives_Native.fst args l
                                 in
                              FStar_List.rev uu____4559  in
                            targ uu____4556) targs'
                      in
                   let res1 =
                     match res with
                     | FStar_Pervasives_Native.None  ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some f2 ->
                         FStar_Pervasives_Native.Some
                           ((fun l  ->
                               let uu____4612 =
                                 map_append FStar_Pervasives_Native.fst args
                                   l
                                  in
                               f2 uu____4612))
                      in
                   FStar_TypeChecker_NBETerm.Lam
                     (((fun l  ->
                          let uu____4648 =
                            map_append FStar_Pervasives_Native.fst args l  in
                          f1 uu____4648)), targs'1, (n1 - m), res1))
            else
              if m = n1
              then
                (let uu____4659 =
                   FStar_List.map FStar_Pervasives_Native.fst args  in
                 f1 uu____4659)
              else
                (let uu____4668 = FStar_List.splitAt n1 args  in
                 match uu____4668 with
                 | (args1,args') ->
                     let uu____4715 =
                       let uu____4716 =
                         FStar_List.map FStar_Pervasives_Native.fst args1  in
                       f1 uu____4716  in
                     iapp cfg uu____4715 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____4835)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____4879 = aux args us ts  in
            (match uu____4879 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____5006)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5050 = aux args us ts  in
            (match uu____5050 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
        | FStar_TypeChecker_NBETerm.TopLevelRec
            (lb,arity,decreases_list,args') ->
            let args1 = FStar_List.append args' args  in
            if (FStar_List.length args1) >= arity
            then
              let uu____5129 =
                should_reduce_recursive_definition args1 decreases_list  in
              (match uu____5129 with
               | (should_reduce,uu____5138,uu____5139) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                        in
                     (debug cfg
                        (fun uu____5147  ->
                           let uu____5148 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu____5148);
                      iapp cfg (FStar_TypeChecker_NBETerm.FV (fv, [], []))
                        args1)
                   else
                     (debug cfg
                        (fun uu____5168  ->
                           let uu____5169 =
                             let uu____5171 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Syntax_Print.fv_to_string uu____5171  in
                           FStar_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu____5169);
                      (let uu____5173 =
                         FStar_Util.first_N
                           (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
                           args1
                          in
                       match uu____5173 with
                       | (univs1,rest) ->
                           let uu____5220 =
                             let uu____5221 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 univs1
                                in
                             translate cfg uu____5221
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5220 rest)))
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
                  let uu____5339 =
                    should_reduce_recursive_definition args1 decreases_list
                     in
                  match uu____5339 with
                  | (should_reduce,uu____5348,uu____5349) ->
                      if Prims.op_Negation should_reduce
                      then
                        FStar_TypeChecker_NBETerm.LocalLetRec
                          (i, lb, mutual_lbs, local_env, args1,
                            Prims.int_zero, decreases_list)
                      else
                        (let env = make_rec_env mutual_lbs local_env  in
                         debug cfg
                           (fun uu____5378  ->
                              (let uu____5380 =
                                 let uu____5382 =
                                   FStar_List.map
                                     FStar_TypeChecker_NBETerm.t_to_string
                                     env
                                    in
                                 FStar_String.concat ",\n\t " uu____5382  in
                               FStar_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu____5380);
                              (let uu____5389 =
                                 let uu____5391 =
                                   FStar_List.map
                                     (fun uu____5403  ->
                                        match uu____5403 with
                                        | (t,uu____5410) ->
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              t) args1
                                    in
                                 FStar_String.concat ",\n\t " uu____5391  in
                               FStar_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu____5389));
                         (let uu____5413 =
                            translate cfg env lb.FStar_Syntax_Syntax.lbdef
                             in
                          iapp cfg uu____5413 args1))))
        | uu____5414 ->
            let uu____5415 =
              let uu____5417 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____5417  in
            failwith uu____5415

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
          let uu____5434 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____5435 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____5434 uu____5435  in
        let uu____5436 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____5436
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____5445 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____5447  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____5445 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____5454  ->
                     let uu____5455 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____5455);
                (let uu____5458 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____5458 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____5469  ->
                           let uu____5470 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n" uu____5470);
                      (let uu____5473 =
                         let uu____5506 =
                           let f uu____5534 uu____5535 =
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
                             let uu____5597 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 callbacks args'
                                in
                             match uu____5597 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____5608  ->
                                       let uu____5609 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____5611 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____5609 uu____5611);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____5619  ->
                                       let uu____5620 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____5620);
                                  (let uu____5623 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp cfg uu____5623 args'))), uu____5506,
                           arity, FStar_Pervasives_Native.None)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____5473))
                 | FStar_Pervasives_Native.Some uu____5633 ->
                     (debug1
                        (fun uu____5639  ->
                           let uu____5640 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____5640);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____5647 ->
                     (debug1
                        (fun uu____5655  ->
                           let uu____5656 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____5656);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               let is_qninfo_visible =
                 let uu____5665 =
                   FStar_TypeChecker_Env.lookup_definition_qninfo
                     cfg.FStar_TypeChecker_Cfg.delta_level
                     (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     qninfo
                    in
                 FStar_Option.isSome uu____5665  in
               if is_qninfo_visible
               then
                 (match qninfo with
                  | FStar_Pervasives_Native.Some
                      (FStar_Util.Inr
                       ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                          FStar_Syntax_Syntax.sigrng = uu____5680;
                          FStar_Syntax_Syntax.sigquals = uu____5681;
                          FStar_Syntax_Syntax.sigmeta = uu____5682;
                          FStar_Syntax_Syntax.sigattrs = uu____5683;
                          FStar_Syntax_Syntax.sigopts = uu____5684;_},_us_opt),_rng)
                      ->
                      (debug1
                         (fun uu____5754  ->
                            let uu____5755 =
                              FStar_Syntax_Print.fv_to_string fvar1  in
                            FStar_Util.print1 "(1) Decided to unfold %s\n"
                              uu____5755);
                       (let lbm = find_let lbs fvar1  in
                        match lbm with
                        | FStar_Pervasives_Native.Some lb ->
                            if
                              is_rec &&
                                (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                            then
                              let uu____5763 = let_rec_arity lb  in
                              (match uu____5763 with
                               | (ar,lst) ->
                                   FStar_TypeChecker_NBETerm.TopLevelRec
                                     (lb, ar, lst, []))
                            else translate_letbinding cfg bs lb
                        | FStar_Pervasives_Native.None  ->
                            failwith "Could not find let binding"))
                  | uu____5799 ->
                      (debug1
                         (fun uu____5805  ->
                            let uu____5806 =
                              FStar_Syntax_Print.fv_to_string fvar1  in
                            FStar_Util.print1 "(1) qninfo is None for (%s)\n"
                              uu____5806);
                       FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))
               else
                 (debug1
                    (fun uu____5820  ->
                       let uu____5821 = FStar_Syntax_Print.fv_to_string fvar1
                          in
                       FStar_Util.print1
                         "(1) qninfo is not visible at this level (%s)\n"
                         uu____5821);
                  FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               let is_qninfo_visible =
                 let uu____5830 =
                   FStar_TypeChecker_Env.lookup_definition_qninfo
                     cfg.FStar_TypeChecker_Cfg.delta_level
                     (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     qninfo
                    in
                 FStar_Option.isSome uu____5830  in
               if is_qninfo_visible
               then
                 (match qninfo with
                  | FStar_Pervasives_Native.Some
                      (FStar_Util.Inr
                       ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                          FStar_Syntax_Syntax.sigrng = uu____5845;
                          FStar_Syntax_Syntax.sigquals = uu____5846;
                          FStar_Syntax_Syntax.sigmeta = uu____5847;
                          FStar_Syntax_Syntax.sigattrs = uu____5848;
                          FStar_Syntax_Syntax.sigopts = uu____5849;_},_us_opt),_rng)
                      ->
                      (debug1
                         (fun uu____5919  ->
                            let uu____5920 =
                              FStar_Syntax_Print.fv_to_string fvar1  in
                            FStar_Util.print1 "(1) Decided to unfold %s\n"
                              uu____5920);
                       (let lbm = find_let lbs fvar1  in
                        match lbm with
                        | FStar_Pervasives_Native.Some lb ->
                            if
                              is_rec &&
                                (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                            then
                              let uu____5928 = let_rec_arity lb  in
                              (match uu____5928 with
                               | (ar,lst) ->
                                   FStar_TypeChecker_NBETerm.TopLevelRec
                                     (lb, ar, lst, []))
                            else translate_letbinding cfg bs lb
                        | FStar_Pervasives_Native.None  ->
                            failwith "Could not find let binding"))
                  | uu____5964 ->
                      (debug1
                         (fun uu____5970  ->
                            let uu____5971 =
                              FStar_Syntax_Print.fv_to_string fvar1  in
                            FStar_Util.print1 "(1) qninfo is None for (%s)\n"
                              uu____5971);
                       FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))
               else
                 (debug1
                    (fun uu____5985  ->
                       let uu____5986 = FStar_Syntax_Print.fv_to_string fvar1
                          in
                       FStar_Util.print1
                         "(1) qninfo is not visible at this level (%s)\n"
                         uu____5986);
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
        | uu____6033 ->
            let uu____6036 =
              let uu____6069 =
                FStar_List.map
                  (fun uu____6094  ->
                     fun _ts  ->
                       FStar_All.pipe_left id1
                         ((FStar_TypeChecker_NBETerm.Constant
                             FStar_TypeChecker_NBETerm.Unit),
                           FStar_Pervasives_Native.None)) us
                 in
              ((fun us1  ->
                  translate cfg (FStar_List.rev_append us1 bs)
                    lb.FStar_Syntax_Syntax.lbdef), uu____6069,
                (FStar_List.length us), FStar_Pervasives_Native.None)
               in
            FStar_TypeChecker_NBETerm.Lam uu____6036

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
          let uu____6154 = let_rec_arity b  in
          match uu____6154 with
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
        let uu____6224 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____6224
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____6233 ->
        let uu____6234 =
          let uu____6236 =
            let uu____6238 = FStar_Syntax_Print.const_to_string c  in
            Prims.op_Hat uu____6238 ": Not yet implemented"  in
          Prims.op_Hat "Tm_constant " uu____6236  in
        failwith uu____6234

and (readback_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____6251 =
              let uu____6260 = readback cfg typ  in (uu____6260, u)  in
            FStar_Syntax_Syntax.Total uu____6251
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____6273 =
              let uu____6282 = readback cfg typ  in (uu____6282, u)  in
            FStar_Syntax_Syntax.GTotal uu____6273
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____6290 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____6290
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
        let uu____6296 = c  in
        match uu____6296 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____6316 =
              FStar_List.map (translate_univ cfg bs) comp_univs  in
            let uu____6317 = translate cfg bs result_typ  in
            let uu____6318 =
              FStar_List.map
                (fun x  ->
                   let uu____6346 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____6346, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____6353 = FStar_List.map (translate_flag cfg bs) flags  in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____6316;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____6317;
              FStar_TypeChecker_NBETerm.effect_args = uu____6318;
              FStar_TypeChecker_NBETerm.flags = uu____6353
            }

and (readback_comp_typ :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____6358 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____6361 =
        FStar_List.map
          (fun x  ->
             let uu____6387 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____6387, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____6388 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____6358;
        FStar_Syntax_Syntax.effect_args = uu____6361;
        FStar_Syntax_Syntax.flags = uu____6388
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
        let uu____6396 = c  in
        match uu____6396 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____6406 =
              if
                (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
              then FStar_Pervasives_Native.None
              else FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____6416 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____6406;
              FStar_TypeChecker_NBETerm.residual_flags = uu____6416
            }

and (readback_residual_comp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____6421 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (fun x  ->
             debug cfg
               (fun uu____6432  ->
                  let uu____6433 = FStar_TypeChecker_NBETerm.t_to_string x
                     in
                  FStar_Util.print1 "Reading back residualtype %s\n"
                    uu____6433);
             readback cfg x)
         in
      let uu____6436 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____6421;
        FStar_Syntax_Syntax.residual_flags = uu____6436
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
            let uu____6447 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____6447

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
          let uu____6451 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____6451

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____6454  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____6454 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____6492 =
                     let uu____6501 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____6501
                      in
                   (match uu____6492 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6508 =
                          let uu____6510 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____6510
                           in
                        failwith uu____6508
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___976_6526 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___976_6526.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___976_6526.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___976_6526.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___976_6526.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___976_6526.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___976_6526.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___976_6526.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___976_6526.FStar_TypeChecker_Cfg.normalize_pure_lets);
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
                          let uu____6534 =
                            let uu____6541 =
                              let uu____6542 =
                                let uu____6561 =
                                  let uu____6570 =
                                    let uu____6577 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____6577,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____6570]  in
                                (uu____6561, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____6542  in
                            FStar_Syntax_Syntax.mk uu____6541  in
                          uu____6534 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____6611 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____6611
                          then
                            let uu____6620 =
                              let uu____6625 =
                                let uu____6626 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____6626  in
                              (uu____6625, FStar_Pervasives_Native.None)  in
                            let uu____6627 =
                              let uu____6634 =
                                let uu____6639 =
                                  let uu____6640 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____6640  in
                                (uu____6639, FStar_Pervasives_Native.None)
                                 in
                              [uu____6634]  in
                            uu____6620 :: uu____6627
                          else []  in
                        let t =
                          let uu____6660 =
                            let uu____6661 =
                              let uu____6662 =
                                let uu____6663 =
                                  let uu____6664 =
                                    let uu____6671 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____6671
                                      FStar_Util.must
                                     in
                                  FStar_All.pipe_right uu____6664
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Syntax_Util.un_uinst uu____6663  in
                              translate cfg' [] uu____6662  in
                            iapp cfg uu____6661
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____6704 =
                            let uu____6705 =
                              let uu____6712 =
                                let uu____6717 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____6717, FStar_Pervasives_Native.None)
                                 in
                              let uu____6718 =
                                let uu____6725 =
                                  let uu____6730 = translate cfg' bs ty  in
                                  (uu____6730, FStar_Pervasives_Native.None)
                                   in
                                [uu____6725]  in
                              uu____6712 :: uu____6718  in
                            let uu____6743 =
                              let uu____6750 =
                                let uu____6757 =
                                  let uu____6764 =
                                    let uu____6769 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____6769,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____6770 =
                                    let uu____6777 =
                                      let uu____6784 =
                                        let uu____6789 =
                                          translate cfg bs body_lam  in
                                        (uu____6789,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____6784]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____6777
                                     in
                                  uu____6764 :: uu____6770  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____6757
                                 in
                              FStar_List.append maybe_range_arg uu____6750
                               in
                            FStar_List.append uu____6705 uu____6743  in
                          iapp cfg uu____6660 uu____6704  in
                        (debug cfg
                           (fun uu____6821  ->
                              let uu____6822 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____6822);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____6825);
                      FStar_Syntax_Syntax.pos = uu____6826;
                      FStar_Syntax_Syntax.vars = uu____6827;_},(e2,uu____6829)::[])
                   ->
                   translate
                     (let uu___998_6870 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___998_6870.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___998_6870.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___998_6870.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___998_6870.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___998_6870.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___998_6870.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___998_6870.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___998_6870.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   (debug cfg
                      (fun uu____6902  ->
                         let uu____6903 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____6905 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____6903
                           uu____6905);
                    (let fallback1 uu____6913 = translate cfg bs e1  in
                     let fallback2 uu____6919 =
                       let uu____6920 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           FStar_Pervasives_Native.None
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate
                         (let uu___1010_6927 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___1010_6927.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___1010_6927.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___1010_6927.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___1010_6927.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___1010_6927.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___1010_6927.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___1010_6927.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___1010_6927.FStar_TypeChecker_Cfg.normalize_pure_lets);
                            FStar_TypeChecker_Cfg.reifying = false
                          }) bs uu____6920
                        in
                     let uu____6929 =
                       let uu____6930 = FStar_Syntax_Util.un_uinst head1  in
                       uu____6930.FStar_Syntax_Syntax.n  in
                     match uu____6929 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             cfg.FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____6936 =
                           let uu____6938 =
                             FStar_TypeChecker_Env.is_action
                               cfg.FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____6938  in
                         if uu____6936
                         then fallback1 ()
                         else
                           (let uu____6943 =
                              let uu____6945 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  cfg.FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____6945  in
                            if uu____6943
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____6962 =
                                   let uu____6967 =
                                     FStar_Syntax_Util.mk_reify head1  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____6967
                                     args
                                    in
                                 uu____6962 FStar_Pervasives_Native.None
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               translate
                                 (let uu___1019_6970 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1019_6970.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1019_6970.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1019_6970.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1019_6970.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1019_6970.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong =
                                      (uu___1019_6970.FStar_TypeChecker_Cfg.strong);
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1019_6970.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1019_6970.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying = false
                                  }) bs e2))
                     | uu____6972 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____7093  ->
                             match uu____7093 with
                             | (pat,wopt,tm) ->
                                 let uu____7141 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____7141)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   translate
                     (let uu___1032_7175 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___1032_7175.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1032_7175.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1032_7175.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___1032_7175.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1032_7175.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1032_7175.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1032_7175.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___1032_7175.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____7178) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____7205 ->
                   let uu____7206 =
                     let uu____7208 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____7208
                      in
                   failwith uu____7206)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7211  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7211 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____7235 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____7235
              then
                let ed =
                  let uu____7239 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____7239
                   in
                let ret1 =
                  let uu____7241 =
                    let uu____7242 =
                      let uu____7245 =
                        let uu____7246 =
                          let uu____7253 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_return_repr
                             in
                          FStar_All.pipe_right uu____7253 FStar_Util.must  in
                        FStar_All.pipe_right uu____7246
                          FStar_Pervasives_Native.snd
                         in
                      FStar_Syntax_Subst.compress uu____7245  in
                    uu____7242.FStar_Syntax_Syntax.n  in
                  match uu____7241 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret1,uu____7299::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret1, [FStar_Syntax_Syntax.U_unknown]))
                        FStar_Pervasives_Native.None
                        e1.FStar_Syntax_Syntax.pos
                  | uu____7306 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' =
                  let uu___1065_7309 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___1065_7309.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1065_7309.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1065_7309.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___1065_7309.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1065_7309.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1065_7309.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1065_7309.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1065_7309.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let t =
                  let uu____7312 =
                    let uu____7313 = translate cfg' [] ret1  in
                    iapp cfg' uu____7313
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____7322 =
                    let uu____7323 =
                      let uu____7328 = translate cfg' bs ty  in
                      (uu____7328, FStar_Pervasives_Native.None)  in
                    let uu____7329 =
                      let uu____7336 =
                        let uu____7341 = translate cfg' bs e1  in
                        (uu____7341, FStar_Pervasives_Native.None)  in
                      [uu____7336]  in
                    uu____7323 :: uu____7329  in
                  iapp cfg' uu____7312 uu____7322  in
                (debug cfg
                   (fun uu____7357  ->
                      let uu____7358 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____7358);
                 t)
              else
                (let uu____7363 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____7363 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____7366 =
                       let uu____7368 = FStar_Ident.text_of_lid msrc  in
                       let uu____7370 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____7368 uu____7370
                        in
                     failwith uu____7366
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7373;
                       FStar_TypeChecker_Env.mtarget = uu____7374;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7375;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____7395 =
                       let uu____7397 = FStar_Ident.text_of_lid msrc  in
                       let uu____7399 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____7397 uu____7399
                        in
                     failwith uu____7395
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7402;
                       FStar_TypeChecker_Env.mtarget = uu____7403;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7404;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____7438 =
                         let uu____7441 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty uu____7441  in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____7438
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___1089_7457 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___1089_7457.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1089_7457.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1089_7457.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___1089_7457.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1089_7457.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1089_7457.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1089_7457.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___1089_7457.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let t =
                       let uu____7460 = translate cfg' [] lift_lam  in
                       let uu____7461 =
                         let uu____7462 =
                           let uu____7467 = translate cfg bs e1  in
                           (uu____7467, FStar_Pervasives_Native.None)  in
                         [uu____7462]  in
                       iapp cfg uu____7460 uu____7461  in
                     (debug cfg
                        (fun uu____7479  ->
                           let uu____7480 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____7480);
                      t))

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____7498  ->
           let uu____7499 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____7499);
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
           let uu____7507 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____7507 FStar_Syntax_Util.exp_int
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
           let uu____7571 =
             FStar_List.fold_left
               (fun uu____7614  ->
                  fun tf  ->
                    match uu____7614 with
                    | (args_rev,accus_rev) ->
                        let uu____7666 = tf accus_rev  in
                        (match uu____7666 with
                         | (xt,q) ->
                             let x1 =
                               let uu____7686 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____7686
                                in
                             let uu____7687 =
                               let uu____7690 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____7690 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____7687))) ([], [])
               targs
              in
           (match uu____7571 with
            | (args_rev,accus_rev) ->
                let accus = FStar_List.rev accus_rev  in
                let body =
                  let uu____7737 = f accus  in readback cfg uu____7737  in
                let uu____7738 =
                  FStar_Util.map_opt resc
                    (fun thunk1  ->
                       let uu____7753 = thunk1 accus  in
                       readback_residual_comp cfg uu____7753)
                   in
                FStar_Syntax_Util.abs (FStar_List.rev args_rev) body
                  uu____7738)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           if
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
           then
             let uu____7781 =
               let uu____7782 = targ ()  in
               FStar_Pervasives_Native.fst uu____7782  in
             readback cfg uu____7781
           else
             (let x1 =
                let uu____7790 =
                  let uu____7791 =
                    let uu____7792 = targ ()  in
                    FStar_Pervasives_Native.fst uu____7792  in
                  readback cfg uu____7791  in
                FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  uu____7790
                 in
              let body =
                let uu____7798 =
                  let uu____7799 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                  f uu____7799  in
                readback cfg uu____7798  in
              FStar_Syntax_Util.refine x1 body)
       | FStar_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t  in FStar_Syntax_Util.mk_reflect tm
       | FStar_TypeChecker_NBETerm.Arrow (f,targs) ->
           let uu____7836 =
             FStar_List.fold_left
               (fun uu____7879  ->
                  fun tf  ->
                    match uu____7879 with
                    | (args_rev,accus_rev) ->
                        let uu____7931 = tf accus_rev  in
                        (match uu____7931 with
                         | (xt,q) ->
                             let x1 =
                               let uu____7951 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____7951
                                in
                             let uu____7952 =
                               let uu____7955 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____7955 :: accus_rev  in
                             (((x1, q) :: args_rev), uu____7952))) ([], [])
               targs
              in
           (match uu____7836 with
            | (args_rev,accus_rev) ->
                let cmp =
                  let uu____7999 = f (FStar_List.rev accus_rev)  in
                  readback_comp cfg uu____7999  in
                FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp)
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____8042  ->
                  match uu____8042 with
                  | (x1,q) ->
                      let uu____8053 = readback cfg x1  in (uu____8053, q))
               args
              in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____8072 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____8079::uu____8080 ->
                let uu____8083 =
                  let uu____8086 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____8086
                    (FStar_List.rev us)
                   in
                apply1 uu____8083
            | [] ->
                let uu____8087 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply1 uu____8087)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____8128  ->
                  match uu____8128 with
                  | (x1,q) ->
                      let uu____8139 = readback cfg x1  in (uu____8139, q))
               args
              in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____8158 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____8165::uu____8166 ->
                let uu____8169 =
                  let uu____8172 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____8172
                    (FStar_List.rev us)
                   in
                apply1 uu____8169
            | [] ->
                let uu____8173 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply1 uu____8173)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____8220  ->
                  match uu____8220 with
                  | (x1,q) ->
                      let uu____8231 = readback cfg x1  in (uu____8231, q))
               ts
              in
           let uu____8232 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____8232 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,make_branches),ts) ->
           let args =
             map_rev
               (fun uu____8279  ->
                  match uu____8279 with
                  | (x1,q) ->
                      let uu____8290 = readback cfg x1  in (uu____8290, q))
               ts
              in
           let head1 =
             let scrut_new = readback cfg scrut  in
             let branches_new = make_branches ()  in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_match (scrut_new, branches_new))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           FStar_Syntax_Util.mk_app head1 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLet
            (var,typ,defn,body,lb),args)
           ->
           let typ1 =
             let uu____8347 = FStar_Thunk.force typ  in
             readback cfg uu____8347  in
           let defn1 =
             let uu____8349 = FStar_Thunk.force defn  in
             readback cfg uu____8349  in
           let body1 =
             let uu____8351 =
               let uu____8352 = FStar_Thunk.force body  in
               readback cfg uu____8352  in
             FStar_Syntax_Subst.close [(var, FStar_Pervasives_Native.None)]
               uu____8351
              in
           let lbname =
             let uu____8372 =
               let uu___1248_8373 =
                 FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___1248_8373.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___1248_8373.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = typ1
               }  in
             FStar_Util.Inl uu____8372  in
           let lb1 =
             let uu___1251_8375 = lb  in
             {
               FStar_Syntax_Syntax.lbname = lbname;
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1251_8375.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = typ1;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1251_8375.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef = defn1;
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1251_8375.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1251_8375.FStar_Syntax_Syntax.lbpos)
             }  in
           let hd1 =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 =
             map_rev
               (fun uu____8411  ->
                  match uu____8411 with
                  | (x1,q) ->
                      let uu____8422 = readback cfg x1  in (uu____8422, q))
               args
              in
           FStar_Syntax_Util.mk_app hd1 args1
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLetRec
            (vars_typs_defns,body,lbs),args)
           ->
           let lbs1 =
             FStar_List.map2
               (fun uu____8477  ->
                  fun lb  ->
                    match uu____8477 with
                    | (v1,t,d) ->
                        let t1 = readback cfg t  in
                        let def = readback cfg d  in
                        let v2 =
                          let uu___1274_8491 = v1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1274_8491.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1274_8491.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        let uu___1277_8492 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl v2);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1277_8492.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = t1;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1277_8492.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1277_8492.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1277_8492.FStar_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs
              in
           let body1 = readback cfg body  in
           let uu____8494 = FStar_Syntax_Subst.close_let_rec lbs1 body1  in
           (match uu____8494 with
            | (lbs2,body2) ->
                let hd1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body2))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                let args1 =
                  map_rev
                    (fun uu____8542  ->
                       match uu____8542 with
                       | (x1,q) ->
                           let uu____8553 = readback cfg x1  in
                           (uu____8553, q)) args
                   in
                FStar_Syntax_Util.mk_app hd1 args1)
       | FStar_TypeChecker_NBETerm.TopLevelRec
           (lb,uu____8555,uu____8556,args) ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let head1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 =
             FStar_List.map
               (fun uu____8601  ->
                  match uu____8601 with
                  | (t,q) ->
                      let uu____8612 = readback cfg t  in (uu____8612, q))
               args
              in
           FStar_Syntax_Util.mk_app head1 args1
       | FStar_TypeChecker_NBETerm.LocalLetRec
           (i,uu____8614,lbs,bs,args,_ar,_ar_lst) ->
           let lbnames =
             FStar_List.map
               (fun lb  ->
                  let uu____8656 =
                    let uu____8658 =
                      let uu____8659 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      uu____8659.FStar_Syntax_Syntax.ppname  in
                    FStar_Ident.text_of_id uu____8658  in
                  FStar_Syntax_Syntax.gen_bv uu____8656
                    FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp)
               lbs
              in
           let let_rec_env =
             let uu____8663 =
               FStar_List.map
                 (fun x1  ->
                    FStar_TypeChecker_NBETerm.Accu
                      ((FStar_TypeChecker_NBETerm.Var x1), [])) lbnames
                in
             FStar_List.rev_append uu____8663 bs  in
           let lbs1 =
             FStar_List.map2
               (fun lb  ->
                  fun lbname  ->
                    let lbdef =
                      let uu____8689 =
                        translate cfg let_rec_env
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      readback cfg uu____8689  in
                    let lbtyp =
                      let uu____8691 =
                        translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                      readback cfg uu____8691  in
                    let uu___1318_8692 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = (FStar_Util.Inl lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___1318_8692.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___1318_8692.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbdef;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___1318_8692.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___1318_8692.FStar_Syntax_Syntax.lbpos)
                    }) lbs lbnames
              in
           let body =
             let uu____8694 = FStar_List.nth lbnames i  in
             FStar_Syntax_Syntax.bv_to_name uu____8694  in
           let uu____8695 = FStar_Syntax_Subst.close_let_rec lbs1 body  in
           (match uu____8695 with
            | (lbs2,body1) ->
                let head1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body1))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                let args1 =
                  FStar_List.map
                    (fun uu____8743  ->
                       match uu____8743 with
                       | (x1,q) ->
                           let uu____8754 = readback cfg x1  in
                           (uu____8754, q)) args
                   in
                FStar_Syntax_Util.mk_app head1 args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____8760) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (uu____8777,thunk1) ->
           let uu____8799 = FStar_Thunk.force thunk1  in
           readback cfg uu____8799)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____8828 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____8840 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____8861 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____8888 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____8912 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____8923 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___1_8930  ->
    match uu___1_8930 with
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
            let uu___1361_8969 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1363_8972 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1363_8972.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1361_8969.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1361_8969.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1361_8969.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1361_8969.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1361_8969.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1361_8969.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1361_8969.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1361_8969.FStar_TypeChecker_Cfg.reifying)
            }  in
          debug cfg1
            (fun uu____8977  ->
               let uu____8978 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print1 "Calling NBE with (%s) {\n" uu____8978);
          (let r =
             let uu____8982 = translate cfg1 [] e  in
             readback cfg1 uu____8982  in
           debug cfg1
             (fun uu____8986  ->
                let uu____8987 = FStar_Syntax_Print.term_to_string r  in
                FStar_Util.print1 "}\nNBE returned (%s)\n" uu____8987);
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
          let uu___1378_9012 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1380_9015 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1380_9015.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1378_9012.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1378_9012.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1378_9012.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1378_9012.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1378_9012.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1378_9012.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1378_9012.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1378_9012.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____9020  ->
             let uu____9021 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____9021);
        (let r =
           let uu____9025 = translate cfg1 [] e  in readback cfg1 uu____9025
            in
         debug cfg1
           (fun uu____9029  ->
              let uu____9030 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____9030);
         r)
  