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
  
let rec drop : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p  ->
    fun l  ->
      match l with
      | [] -> []
      | x::xs ->
          let uu____107 = p x  in if uu____107 then x :: xs else drop p xs
  
let (debug : (unit -> unit) -> unit) =
  fun f  ->
    let uu____121 =
      FStar_Options.debug_at_level "Test" (FStar_Options.Other "NBE")  in
    if uu____121 then f () else ()
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____128 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____128
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____145 = FStar_Syntax_Print.sigelt_to_string_short v1  in
             FStar_Util.print2 "%s -> %%s\n" k uu____145) ()
  
type var = FStar_Syntax_Syntax.bv
type sort = Prims.int
type constant =
  | Unit 
  | Bool of Prims.bool 
  | Int of FStar_BigInt.t 
  | String of (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  
  | Char of FStar_Char.char 
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____176 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____183 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____197 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____215 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____242 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
type atom =
  | Var of var 
  | Match of
  (t,(t -> FStar_Syntax_Syntax.term) -> FStar_Syntax_Syntax.branch Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Rec of
  (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
  t Prims.list) FStar_Pervasives_Native.tuple3 
and t =
  | Lam of (t -> t,unit -> t,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple3 
  | Accu of
  (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
          Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Construct of
  (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
  FStar_Pervasives_Native.tuple3 
  | Constant of constant 
  | Type_t of FStar_Syntax_Syntax.universe 
  | Univ of FStar_Syntax_Syntax.universe 
  | Unknown 
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____366 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____392 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,(t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Rec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____452 -> false
  
let (__proj__Rec__item___0 :
  atom ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____508 -> false
  
let (__proj__Lam__item___0 :
  t ->
    (t -> t,unit -> t,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____568 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____626 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____682 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____696 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____710 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____723 -> false
  
type args =
  (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____743) -> FStar_Util.format1 "\"%s\"" s
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam uu____753 -> "Lam"
    | Accu (a,l) ->
        let uu____780 =
          let uu____781 = atom_to_string a  in
          let uu____782 =
            let uu____783 =
              let uu____784 =
                let uu____785 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____785  in
              Prims.strcat uu____784 ")"  in
            Prims.strcat ") (" uu____783  in
          Prims.strcat uu____781 uu____782  in
        Prims.strcat "Accu (" uu____780
    | Construct (fv,us,l) ->
        let uu____817 =
          let uu____818 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____819 =
            let uu____820 =
              let uu____821 =
                let uu____822 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____822  in
              let uu____825 =
                let uu____826 =
                  let uu____827 =
                    let uu____828 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____828  in
                  Prims.strcat uu____827 ")"  in
                Prims.strcat "] (" uu____826  in
              Prims.strcat uu____821 uu____825  in
            Prims.strcat ") [" uu____820  in
          Prims.strcat uu____818 uu____819  in
        Prims.strcat "Construct (" uu____817
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____843 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____843
    | Type_t u ->
        let uu____845 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____845
    | Unknown  -> "Unknown"

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____848 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____848
    | Match (t,uu____850) ->
        let uu____867 = t_to_string t  in Prims.strcat "Match " uu____867
    | Rec (uu____868,uu____869,l) ->
        let uu____879 =
          let uu____880 =
            let uu____881 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____881  in
          Prims.strcat uu____880 ")"  in
        Prims.strcat "Rec (" uu____879

let (is_not_accu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____889,uu____890) -> false | uu____903 -> true
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
        -> t)
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts) 
let (mkAccuVar : var -> t) = fun v1  -> Accu ((Var v1), []) 
let (mkAccuMatch :
  t ->
    ((t -> FStar_Syntax_Syntax.term) -> FStar_Syntax_Syntax.branch Prims.list)
      -> t)
  = fun s  -> fun bs  -> Accu ((Match (s, bs)), []) 
let (mkAccuRec :
  FStar_Syntax_Syntax.letbinding ->
    FStar_Syntax_Syntax.letbinding Prims.list -> t Prims.list -> t)
  = fun b  -> fun bs  -> fun env  -> Accu ((Rec (b, bs, env)), []) 
let (isAccu : t -> Prims.bool) =
  fun trm  -> match trm with | Accu uu____1042 -> true | uu____1053 -> false 
let (pickBranch :
  t ->
    FStar_Syntax_Syntax.branch Prims.list ->
      (FStar_Syntax_Syntax.term,t Prims.list) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun scrut  ->
    fun branches  ->
      let rec pickBranch_aux scrut1 branches1 branches0 =
        let rec matches_pat scrutinee p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var bv -> FStar_Util.Inl [scrutinee]
          | FStar_Syntax_Syntax.Pat_wild bv -> FStar_Util.Inl [scrutinee]
          | FStar_Syntax_Syntax.Pat_dot_term uu____1153 -> FStar_Util.Inl []
          | FStar_Syntax_Syntax.Pat_constant s ->
              let matches_const c s1 =
                match c with
                | Constant (Unit ) -> s1 = FStar_Const.Const_unit
                | Constant (Bool b) ->
                    (match s1 with
                     | FStar_Const.Const_bool p1 -> b = p1
                     | uu____1176 -> false)
                | Constant (Int i) ->
                    (match s1 with
                     | FStar_Const.Const_int
                         (p1,FStar_Pervasives_Native.None ) ->
                         let uu____1189 = FStar_BigInt.big_int_of_string p1
                            in
                         i = uu____1189
                     | uu____1190 -> false)
                | Constant (String (st,uu____1192)) ->
                    (match s1 with
                     | FStar_Const.Const_string (p1,uu____1194) -> st = p1
                     | uu____1195 -> false)
                | Constant (Char c1) ->
                    (match s1 with
                     | FStar_Const.Const_char p1 -> c1 = p1
                     | uu____1201 -> false)
                | uu____1202 -> false  in
              let uu____1203 = matches_const scrutinee s  in
              if uu____1203 then FStar_Util.Inl [] else FStar_Util.Inr false
          | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
              let rec matches_args out a p1 =
                match (a, p1) with
                | ([],[]) -> FStar_Util.Inl out
                | ((t,uu____1324)::rest_a,(p2,uu____1327)::rest_p) ->
                    let uu____1361 = matches_pat t p2  in
                    (match uu____1361 with
                     | FStar_Util.Inl s ->
                         matches_args (FStar_List.append out s) rest_a rest_p
                     | m -> m)
                | uu____1386 -> FStar_Util.Inr false  in
              (match scrutinee with
               | Construct (fv',_us,args_rev) ->
                   let uu____1430 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                   if uu____1430
                   then matches_args [] (FStar_List.rev args_rev) arg_pats
                   else FStar_Util.Inr false
               | uu____1444 -> FStar_Util.Inr true)
           in
        match branches1 with
        | [] -> failwith "Branch not found"
        | (p,_wopt,e)::branches2 ->
            let uu____1485 = matches_pat scrut1 p  in
            (match uu____1485 with
             | FStar_Util.Inl matches ->
                 FStar_Pervasives_Native.Some (e, matches)
             | FStar_Util.Inr (false ) ->
                 pickBranch_aux scrut1 branches2 branches0
             | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
         in
      pickBranch_aux scrut branches branches
  
let rec test_args :
  'Auu____1530 .
    (t,'Auu____1530) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int -> Prims.bool
  =
  fun ts  ->
    fun cnt  ->
      match ts with
      | [] -> cnt <= (Prims.parse_int "0")
      | t::ts1 ->
          (Prims.op_Negation (isAccu (FStar_Pervasives_Native.fst t))) &&
            (test_args ts1 (cnt - (Prims.parse_int "1")))
  
let rec (count_abstractions : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    let uu____1578 =
      let uu____1579 = FStar_Syntax_Subst.compress t  in
      uu____1579.FStar_Syntax_Syntax.n  in
    match uu____1578 with
    | FStar_Syntax_Syntax.Tm_delayed uu____1582 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____1605 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_name uu____1606 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_fvar uu____1607 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_constant uu____1608 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_type uu____1609 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_arrow uu____1610 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uvar uu____1623 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_refine uu____1636 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_unknown  -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1644) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1651) ->
        let uu____1672 = count_abstractions body  in
        (FStar_List.length xs) + uu____1672
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1699 =
          let uu____1700 = count_abstractions head1  in
          uu____1700 - (FStar_List.length args)  in
        max uu____1699 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____1759,uu____1760,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____1809,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1828) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1834,uu____1835) ->
        count_abstractions t1
  
let (find_sigelt_in_gamma :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let mapper uu____1915 =
        match uu____1915 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                 FStar_Pervasives_Native.Some elt
             | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                 (debug
                    (fun uu____2000  ->
                       let uu____2001 = FStar_Syntax_Print.univs_to_string us
                          in
                       FStar_Util.print1
                         "Universes in local declaration: %s\n" uu____2001);
                  FStar_Pervasives_Native.Some elt)
             | uu____2002 -> FStar_Pervasives_Native.None)
         in
      let uu____2017 = FStar_TypeChecker_Env.lookup_qname env lid  in
      FStar_Util.bind_opt uu____2017 mapper
  
let (translate_univ : t Prims.list -> FStar_Syntax_Syntax.universe -> t) =
  fun bs  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar i ->
            let uu____2078 = FStar_List.nth bs i  in
            (match uu____2078 with | Univ u3 -> u3)
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2081 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2081
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2085 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2085
        | FStar_Syntax_Syntax.U_name uu____2088 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_unif uu____2089 ->
            failwith "Unknown or unconstrained universe"
        | FStar_Syntax_Syntax.U_unknown  ->
            failwith "Unknown or unconstrained universe"
         in
      let uu____2098 = aux u  in Univ uu____2098
  
let (is_univ : t -> Prims.bool) =
  fun tm  -> match tm with | Univ uu____2104 -> true | uu____2105 -> false 
let (un_univ : t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with | Univ u -> u | uu____2112 -> failwith "Not a universe"
  
let (make_rec_env :
  FStar_Syntax_Syntax.letbinding Prims.list -> t Prims.list -> t Prims.list)
  =
  fun lbs  ->
    fun bs  ->
      let rec aux lbs1 lbs0 bs1 bs0 =
        match lbs1 with
        | [] -> bs1
        | lb::lbs' -> aux lbs' lbs0 ((mkAccuRec lb lbs0 bs0) :: bs1) bs0  in
      aux lbs lbs bs bs
  
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
           | FStar_Util.Inl uu____2201 -> failwith "impossible"
           | FStar_Util.Inr name ->
               let uu____2205 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____2205
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
  
let rec (app : t -> t -> FStar_Syntax_Syntax.aqual -> t) =
  fun f  ->
    fun x  ->
      fun q  ->
        debug
          (fun uu____2303  ->
             let uu____2304 = t_to_string f  in
             let uu____2305 = t_to_string x  in
             FStar_Util.print2 "When creating app: %s applied to %s\n"
               uu____2304 uu____2305);
        (match f with
         | Lam (f1,uu____2307,uu____2308) -> f1 x
         | Accu (a,ts) -> Accu (a, ((x, q) :: ts))
         | Construct (i,us,ts) ->
             (match x with
              | Univ u -> Construct (i, (u :: us), ts)
              | uu____2373 -> Construct (i, us, ((x, q) :: ts)))
         | Constant uu____2386 -> failwith "Ill-typed application"
         | Univ uu____2387 -> failwith "Ill-typed application"
         | Type_t uu____2388 -> failwith "Ill-typed application"
         | Unknown  -> failwith "Ill-typed application")

and (iapp :
  t ->
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
      -> t)
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____2401 ->
          let uu____2408 =
            let uu____2409 =
              let uu____2410 = FStar_List.hd args  in
              FStar_Pervasives_Native.fst uu____2410  in
            let uu____2419 =
              let uu____2420 = FStar_List.hd args  in
              FStar_Pervasives_Native.snd uu____2420  in
            app f uu____2409 uu____2419  in
          let uu____2429 = FStar_List.tl args  in iapp uu____2408 uu____2429

and (translate_fv :
  FStar_TypeChecker_Env.env -> t Prims.list -> FStar_Syntax_Syntax.fv -> t) =
  fun env  ->
    fun bs  ->
      fun fvar1  ->
        let find_in_sigtab env1 lid =
          let uu____2460 = FStar_Ident.text_of_lid lid  in
          FStar_Util.smap_try_find env1.FStar_TypeChecker_Env.sigtab
            uu____2460
           in
        let uu____2461 =
          let uu____2466 =
            let uu____2471 =
              find_sigelt_in_gamma env
                (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____2474 =
              let uu____2479 =
                find_in_sigtab env
                  (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              [uu____2479]  in
            uu____2471 :: uu____2474  in
          FStar_List.find FStar_Util.is_some uu____2466  in
        match uu____2461 with
        | FStar_Pervasives_Native.Some elt ->
            (match elt with
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,lbs),names1);
                   FStar_Syntax_Syntax.sigrng = uu____2498;
                   FStar_Syntax_Syntax.sigquals = uu____2499;
                   FStar_Syntax_Syntax.sigmeta = uu____2500;
                   FStar_Syntax_Syntax.sigattrs = uu____2501;_}
                 ->
                 let lbm = find_let lbs fvar1  in
                 (match lbm with
                  | FStar_Pervasives_Native.Some lb ->
                      if is_rec
                      then mkAccuRec lb [] []
                      else
                        (debug
                           (fun uu____2522  ->
                              FStar_Util.print
                                "Translate fv: it's a Sig_let\n" []);
                         debug
                           (fun uu____2530  ->
                              let uu____2531 =
                                let uu____2532 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                FStar_Syntax_Print.tag_of_term uu____2532  in
                              let uu____2533 =
                                let uu____2534 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                FStar_Syntax_Print.term_to_string uu____2534
                                 in
                              FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                uu____2531 uu____2533);
                         debug
                           (fun uu____2542  ->
                              let uu____2543 =
                                let uu____2544 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                FStar_Syntax_Print.tag_of_term uu____2544  in
                              let uu____2545 =
                                let uu____2546 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                FStar_Syntax_Print.term_to_string uu____2546
                                 in
                              FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                uu____2543 uu____2545);
                         translate_letbinding env [] lb)
                  | FStar_Pervasives_Native.None  ->
                      failwith "Could not find mutually recursive definition")
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel =
                     FStar_Syntax_Syntax.Sig_datacon
                     (uu____2547,uu____2548,uu____2549,lid,uu____2551,[]);
                   FStar_Syntax_Syntax.sigrng = uu____2552;
                   FStar_Syntax_Syntax.sigquals = uu____2553;
                   FStar_Syntax_Syntax.sigmeta = uu____2554;
                   FStar_Syntax_Syntax.sigattrs = uu____2555;_}
                 ->
                 (debug
                    (fun uu____2567  ->
                       let uu____2568 = FStar_Syntax_Print.lid_to_string lid
                          in
                       FStar_Util.print1
                         "Translate fv %s: it's a Sig_datacon\n" uu____2568);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel =
                     FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,univs1,bs1,ty,uu____2577,uu____2578);
                   FStar_Syntax_Syntax.sigrng = uu____2579;
                   FStar_Syntax_Syntax.sigquals = uu____2580;
                   FStar_Syntax_Syntax.sigmeta = uu____2581;
                   FStar_Syntax_Syntax.sigattrs = uu____2582;_}
                 ->
                 (debug
                    (fun uu____2600  ->
                       let uu____2601 = FStar_Syntax_Print.lid_to_string lid
                          in
                       FStar_Util.print1
                         "Translate fv %s: it's a Sig_inductive_type\n"
                         uu____2601);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel =
                     FStar_Syntax_Syntax.Sig_declare_typ
                     (lid,uu____2607,uu____2608);
                   FStar_Syntax_Syntax.sigrng = uu____2609;
                   FStar_Syntax_Syntax.sigquals = uu____2610;
                   FStar_Syntax_Syntax.sigmeta = uu____2611;
                   FStar_Syntax_Syntax.sigattrs = uu____2612;_}
                 ->
                 (debug
                    (fun uu____2622  ->
                       let uu____2623 = FStar_Syntax_Print.lid_to_string lid
                          in
                       FStar_Util.print1
                         "Translate fv %s: it's a Sig_declare_typ\n"
                         uu____2623);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.None  ->
                 (debug
                    (fun uu____2631  ->
                       FStar_Util.print
                         "Translate fv: it's not in the environment\n" []);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.Some s ->
                 let uu____2637 =
                   let uu____2638 = FStar_Syntax_Print.sigelt_to_string s  in
                   FStar_Util.format1 "Sig %s\n" uu____2638  in
                 FStar_All.pipe_right uu____2637 failwith)
        | FStar_Pervasives_Native.None  -> mkConstruct fvar1 [] []

and (translate_letbinding :
  FStar_TypeChecker_Env.env ->
    t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)
  =
  fun env  ->
    fun bs  ->
      fun lb  ->
        let rec make_univ_abst us bs1 def =
          match us with
          | [] -> translate env bs1 def
          | u::us' ->
              Lam
                (((fun u1  -> make_univ_abst us' (u1 :: bs1) def)),
                  ((fun uu____2687  -> Constant Unit)),
                  FStar_Pervasives_Native.None)
           in
        make_univ_abst lb.FStar_Syntax_Syntax.lbunivs bs
          lb.FStar_Syntax_Syntax.lbdef

and (translate_constant : FStar_Syntax_Syntax.sconst -> constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> Unit
    | FStar_Const.Const_bool b -> Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____2701 = FStar_BigInt.big_int_of_string s  in Int uu____2701
    | FStar_Const.Const_string (s,r) -> String (s, r)
    | FStar_Const.Const_char c1 -> Char c1
    | uu____2706 ->
        let uu____2707 =
          let uu____2708 =
            let uu____2709 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____2709 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____2708  in
        failwith uu____2707

and (translate_pat : FStar_Syntax_Syntax.pat -> t) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2712 = translate_constant c  in Constant uu____2712
    | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
        let uu____2731 =
          FStar_List.map
            (fun uu____2752  ->
               match uu____2752 with
               | (p1,uu____2764) ->
                   let uu____2765 = translate_pat p1  in
                   (uu____2765, FStar_Pervasives_Native.None)) pats
           in
        iapp (mkConstruct cfv [] []) uu____2731
    | FStar_Syntax_Syntax.Pat_var bvar -> mkAccuVar bvar
    | FStar_Syntax_Syntax.Pat_wild bvar -> mkAccuVar bvar
    | FStar_Syntax_Syntax.Pat_dot_term (bvar,t) ->
        failwith "Pat_dot_term not implemented"

and (translate :
  FStar_TypeChecker_Env.env -> t Prims.list -> FStar_Syntax_Syntax.term -> t)
  =
  fun env  ->
    fun bs  ->
      fun e  ->
        debug
          (fun uu____2792  ->
             let uu____2793 =
               let uu____2794 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2794  in
             let uu____2795 =
               let uu____2796 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2796  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2793 uu____2795);
        debug
          (fun uu____2802  ->
             let uu____2803 =
               let uu____2804 = FStar_List.map (fun x  -> t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____2804  in
             FStar_Util.print1 "BS list: %s\n" uu____2803);
        (let uu____2809 =
           let uu____2810 = FStar_Syntax_Subst.compress e  in
           uu____2810.FStar_Syntax_Syntax.n  in
         match uu____2809 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2813,uu____2814) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  -> Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2852 = translate_constant c  in Constant uu____2852
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug
                (fun uu____2869  ->
                   let uu____2870 = FStar_Syntax_Print.tag_of_term t  in
                   let uu____2871 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2872 =
                     let uu____2873 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2873
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print3 "Term with univs: %s - %s\nUniv %s\n"
                     uu____2870 uu____2871 uu____2872);
              (let uu____2878 = translate env bs t  in
               let uu____2879 = FStar_List.map (translate_univ bs) us  in
               FStar_List.fold_left
                 (fun head1  ->
                    fun u  -> app head1 u FStar_Pervasives_Native.None)
                 uu____2878 uu____2879))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2887 =
               let uu____2888 = translate_univ bs u  in un_univ uu____2888
                in
             Type_t uu____2887
         | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
             (debug_term e; failwith "Tm_arrow: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_refine uu____2908 ->
             (debug_term e; failwith "Tm_refine: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2917,uu____2918) ->
             translate env bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____2979) -> translate env bs e1
         | FStar_Syntax_Syntax.Tm_name x -> mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2985,uu____2986) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (x::[],body,uu____3007) ->
             (debug
                (fun uu____3041  ->
                   let uu____3042 = FStar_Syntax_Print.tag_of_term body  in
                   let uu____3043 = FStar_Syntax_Print.term_to_string body
                      in
                   FStar_Util.print2 "Tm_abs body : %s - %s\n" uu____3042
                     uu____3043);
              (let x1 = FStar_Pervasives_Native.fst x  in
               Lam
                 ((fun y  -> translate env (y :: bs) body),
                   (fun uu____3054  ->
                      translate env bs x1.FStar_Syntax_Syntax.sort),
                   (FStar_Pervasives_Native.snd x))))
         | FStar_Syntax_Syntax.Tm_abs (x::xs,body,uu____3058) ->
             let rest =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_abs
                    (xs, body, FStar_Pervasives_Native.None))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             let tm =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_abs
                    ([x], rest, FStar_Pervasives_Native.None))
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                in
             translate env bs tm
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv env bs fvar1
         | FStar_Syntax_Syntax.Tm_app (e1,[]) ->
             failwith "Impossible: application with no arguments"
         | FStar_Syntax_Syntax.Tm_app (e1,arg::[]) ->
             (debug
                (fun uu____3180  ->
                   let uu____3181 = FStar_Syntax_Print.term_to_string e1  in
                   let uu____3182 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg)
                      in
                   FStar_Util.print2 "Application %s / %s\n" uu____3181
                     uu____3182);
              (let uu____3185 = translate env bs e1  in
               let uu____3186 =
                 translate env bs (FStar_Pervasives_Native.fst arg)  in
               app uu____3185 uu____3186 (FStar_Pervasives_Native.snd arg)))
         | FStar_Syntax_Syntax.Tm_app (head1,arg::args) ->
             (debug
                (fun uu____3233  ->
                   let uu____3234 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3235 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg)
                      in
                   FStar_Util.print2 "Application %s / %s (...more agrs)\n"
                     uu____3234 uu____3235);
              (let first =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange
                  in
               let tm =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (first, args))
                   FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                  in
               translate env bs tm))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | Construct (c,us,args) ->
                   (debug
                      (fun uu____3354  ->
                         let uu____3355 =
                           let uu____3356 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3379  ->
                                     match uu____3379 with
                                     | (x,q) ->
                                         let uu____3392 = t_to_string x  in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3392))
                              in
                           FStar_All.pipe_right uu____3356
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3355);
                    (let uu____3396 = pickBranch scrut1 branches  in
                     match uu____3396 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____3417 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate env uu____3417 branch1
                     | FStar_Pervasives_Native.None  ->
                         mkAccuMatch scrut1 patterns))
               | Constant c ->
                   let uu____3435 = pickBranch scrut1 branches  in
                   (match uu____3435 with
                    | FStar_Pervasives_Native.Some (branch1,[]) ->
                        translate env bs branch1
                    | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                        translate env (arg :: bs) branch1
                    | FStar_Pervasives_Native.None  ->
                        mkAccuMatch scrut1 patterns
                    | FStar_Pervasives_Native.Some (uu____3469,hd1::tl1) ->
                        failwith
                          "Impossible: Matching on constants cannot bind more than one variable")
               | uu____3482 -> mkAccuMatch scrut1 patterns
             
             and patterns readback1 =
               let rec process_pattern p =
                 let p_new =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       FStar_Syntax_Syntax.Pat_constant c
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____3514 =
                         let uu____3527 =
                           FStar_List.map
                             (fun uu____3548  ->
                                match uu____3548 with
                                | (p1,b) ->
                                    let uu____3559 = process_pattern p1  in
                                    (uu____3559, b)) args
                            in
                         (fvar1, uu____3527)  in
                       FStar_Syntax_Syntax.Pat_cons uu____3514
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let uu____3569 =
                         let uu___218_3570 = bvar  in
                         let uu____3571 =
                           let uu____3574 =
                             translate env bs bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3574  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___218_3570.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___218_3570.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____3571
                         }  in
                       FStar_Syntax_Syntax.Pat_var uu____3569
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let uu____3576 =
                         let uu___219_3577 = bvar  in
                         let uu____3578 =
                           let uu____3581 =
                             translate env bs bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3581  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___219_3577.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___219_3577.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____3578
                         }  in
                       FStar_Syntax_Syntax.Pat_wild uu____3576
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let uu____3588 =
                         let uu____3595 =
                           let uu___220_3596 = bvar  in
                           let uu____3597 =
                             let uu____3600 =
                               translate env bs bvar.FStar_Syntax_Syntax.sort
                                in
                             readback1 uu____3600  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___220_3596.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___220_3596.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3597
                           }  in
                         let uu____3601 =
                           let uu____3604 = translate env bs tm  in
                           readback1 uu____3604  in
                         (uu____3595, uu____3601)  in
                       FStar_Syntax_Syntax.Pat_dot_term uu____3588
                    in
                 let uu___221_3607 = p  in
                 {
                   FStar_Syntax_Syntax.v = p_new;
                   FStar_Syntax_Syntax.p =
                     (uu___221_3607.FStar_Syntax_Syntax.p)
                 }  in
               FStar_List.map
                 (fun uu____3636  ->
                    match uu____3636 with
                    | (pat,when_clause,uu____3661) ->
                        let uu____3674 = process_pattern pat  in
                        let uu____3675 =
                          let uu____3676 =
                            let uu____3677 = translate_pat pat  in
                            case uu____3677  in
                          readback1 uu____3676  in
                        (uu____3674, when_clause, uu____3675)) branches
              in let uu____3682 = translate env bs scrut  in case uu____3682
         | FStar_Syntax_Syntax.Tm_let ((false ,lbs),body) ->
             let bs' =
               FStar_List.fold_left
                 (fun bs'  ->
                    fun lb  ->
                      let b = translate_letbinding env bs lb  in b :: bs') bs
                 lbs
                in
             translate env bs' body
         | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) ->
             let uu____3728 = make_rec_env lbs bs  in
             translate env uu____3728 body)

and (readback : FStar_TypeChecker_Env.env -> t -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun x  ->
      debug
        (fun uu____3738  ->
           let uu____3739 = t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____3739);
      (match x with
       | Univ u -> failwith "Readback of universes should not occur"
       | Unknown  ->
           FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | Constant (Unit ) -> FStar_Syntax_Syntax.unit_const
       | Constant (Bool (true )) -> FStar_Syntax_Util.exp_true_bool
       | Constant (Bool (false )) -> FStar_Syntax_Util.exp_false_bool
       | Constant (Int i) ->
           let uu____3742 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____3742 FStar_Syntax_Util.exp_int
       | Constant (String (s,r)) ->
           FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, r)))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | Constant (Char c) -> FStar_Syntax_Util.exp_char c
       | Type_t u ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | Lam (f,t,q) ->
           let x1 =
             let uu____3764 =
               let uu____3765 = t ()  in readback env uu____3765  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____3764
              in
           let body =
             let uu____3767 = f (mkAccuVar x1)  in readback env uu____3767
              in
           FStar_Syntax_Util.abs [(x1, q)] body FStar_Pervasives_Native.None
       | Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____3814  ->
                  match uu____3814 with
                  | (x1,q) ->
                      let uu____3825 = readback env x1  in (uu____3825, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____3844 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____3851::uu____3852 ->
                let uu____3855 =
                  let uu____3858 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____3858
                    (FStar_List.rev us)
                   in
                apply uu____3855
            | [] ->
                let uu____3859 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____3859)
       | Accu (Var bv,[]) -> FStar_Syntax_Syntax.bv_to_name bv
       | Accu (Var bv,ts) ->
           let args =
             map_rev
               (fun uu____3906  ->
                  match uu____3906 with
                  | (x1,q) ->
                      let uu____3917 = readback env x1  in (uu____3917, q))
               ts
              in
           let uu____3918 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____3918 args
       | Accu (Match (scrut,patterns),ts) ->
           let args =
             map_rev
               (fun uu____3971  ->
                  match uu____3971 with
                  | (x1,q) ->
                      let uu____3982 = readback env x1  in (uu____3982, q))
               ts
              in
           let head1 =
             let scrut_new = readback env scrut  in
             let branches_new = patterns (readback env)  in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_match (scrut_new, branches_new))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           (match ts with
            | [] -> head1
            | uu____4012 -> FStar_Syntax_Util.mk_app head1 args)
       | Accu (Rec (lb,lbs,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____4099 = curry hd1 args1  in
                 app uu____4099 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
              in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef  in
           let uu____4101 = test_args ts args_no  in
           if uu____4101
           then
             let uu____4102 =
               let uu____4103 =
                 let uu____4104 = make_rec_env lbs bs  in
                 translate_letbinding env uu____4104 lb  in
               curry uu____4103 ts  in
             readback env uu____4102
           else
             (let head1 =
                let f =
                  match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inl bv -> FStar_Syntax_Syntax.bv_to_name bv
                  | FStar_Util.Inr fv -> failwith "Not yet implemented"  in
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((true, lbs), f))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              let args =
                map_rev
                  (fun uu____4149  ->
                     match uu____4149 with
                     | (x1,q) ->
                         let uu____4160 = readback env x1  in (uu____4160, q))
                  ts
                 in
              match ts with
              | [] -> head1
              | uu____4165 -> FStar_Syntax_Util.mk_app head1 args))

let (normalize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  -> let uu____4182 = translate env [] e  in readback env uu____4182
  