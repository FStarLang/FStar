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
  FStar_TypeChecker_Normalize.cfg ->
    t Prims.list -> FStar_Syntax_Syntax.fv -> t)
  =
  fun cfg  ->
    fun bs  ->
      fun fvar1  ->
        let qninfo =
          let uu____2446 = FStar_TypeChecker_Normalize.cfg_env cfg  in
          let uu____2447 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2446 uu____2447  in
        let uu____2448 =
          FStar_TypeChecker_Normalize.should_unfold cfg
            (fun uu____2450  -> false) fvar1 qninfo
           in
        match uu____2448 with
        | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
            failwith "Not yet handled"
        | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
            failwith "Not yet handled"
        | FStar_TypeChecker_Normalize.Should_unfold_no  ->
            mkConstruct fvar1 [] []
        | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
            (match qninfo with
             | FStar_Pervasives_Native.Some
                 (FStar_Util.Inr
                  ({
                     FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                       ((is_rec,lbs),names1);
                     FStar_Syntax_Syntax.sigrng = uu____2458;
                     FStar_Syntax_Syntax.sigquals = uu____2459;
                     FStar_Syntax_Syntax.sigmeta = uu____2460;
                     FStar_Syntax_Syntax.sigattrs = uu____2461;_},_us_opt),_rng)
                 ->
                 let lbm = find_let lbs fvar1  in
                 (match lbm with
                  | FStar_Pervasives_Native.Some lb ->
                      if is_rec
                      then mkAccuRec lb [] []
                      else
                        (debug
                           (fun uu____2530  ->
                              FStar_Util.print
                                "Translate fv: it's a Sig_let\n" []);
                         debug
                           (fun uu____2538  ->
                              let uu____2539 =
                                let uu____2540 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                FStar_Syntax_Print.tag_of_term uu____2540  in
                              let uu____2541 =
                                let uu____2542 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                FStar_Syntax_Print.term_to_string uu____2542
                                 in
                              FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                uu____2539 uu____2541);
                         debug
                           (fun uu____2550  ->
                              let uu____2551 =
                                let uu____2552 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                FStar_Syntax_Print.tag_of_term uu____2552  in
                              let uu____2553 =
                                let uu____2554 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                FStar_Syntax_Print.term_to_string uu____2554
                                 in
                              FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                uu____2551 uu____2553);
                         translate_letbinding cfg [] lb)
                  | FStar_Pervasives_Native.None  ->
                      failwith "Could not find mutually recursive definition")
             | uu____2555 -> mkConstruct fvar1 [] [])

and (translate_letbinding :
  FStar_TypeChecker_Normalize.cfg ->
    t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)
  =
  fun cfg  ->
    fun bs  ->
      fun lb  ->
        let rec make_univ_abst us bs1 def =
          match us with
          | [] -> translate cfg bs1 def
          | u::us' ->
              Lam
                (((fun u1  -> make_univ_abst us' (u1 :: bs1) def)),
                  ((fun uu____2602  -> Constant Unit)),
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
        let uu____2616 = FStar_BigInt.big_int_of_string s  in Int uu____2616
    | FStar_Const.Const_string (s,r) -> String (s, r)
    | FStar_Const.Const_char c1 -> Char c1
    | uu____2621 ->
        let uu____2622 =
          let uu____2623 =
            let uu____2624 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____2624 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____2623  in
        failwith uu____2622

and (translate_pat : FStar_Syntax_Syntax.pat -> t) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2627 = translate_constant c  in Constant uu____2627
    | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
        let uu____2646 =
          FStar_List.map
            (fun uu____2667  ->
               match uu____2667 with
               | (p1,uu____2679) ->
                   let uu____2680 = translate_pat p1  in
                   (uu____2680, FStar_Pervasives_Native.None)) pats
           in
        iapp (mkConstruct cfv [] []) uu____2646
    | FStar_Syntax_Syntax.Pat_var bvar -> mkAccuVar bvar
    | FStar_Syntax_Syntax.Pat_wild bvar -> mkAccuVar bvar
    | FStar_Syntax_Syntax.Pat_dot_term (bvar,t) ->
        failwith "Pat_dot_term not implemented"

and (translate :
  FStar_TypeChecker_Normalize.cfg ->
    t Prims.list -> FStar_Syntax_Syntax.term -> t)
  =
  fun cfg  ->
    fun bs  ->
      fun e  ->
        debug
          (fun uu____2707  ->
             let uu____2708 =
               let uu____2709 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2709  in
             let uu____2710 =
               let uu____2711 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2711  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2708 uu____2710);
        debug
          (fun uu____2717  ->
             let uu____2718 =
               let uu____2719 = FStar_List.map (fun x  -> t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____2719  in
             FStar_Util.print1 "BS list: %s\n" uu____2718);
        (let uu____2724 =
           let uu____2725 = FStar_Syntax_Subst.compress e  in
           uu____2725.FStar_Syntax_Syntax.n  in
         match uu____2724 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2728,uu____2729) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  -> Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2767 = translate_constant c  in Constant uu____2767
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug
                (fun uu____2784  ->
                   let uu____2785 = FStar_Syntax_Print.tag_of_term t  in
                   let uu____2786 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2787 =
                     let uu____2788 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2788
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print3 "Term with univs: %s - %s\nUniv %s\n"
                     uu____2785 uu____2786 uu____2787);
              (let uu____2793 = translate cfg bs t  in
               let uu____2794 = FStar_List.map (translate_univ bs) us  in
               FStar_List.fold_left
                 (fun head1  ->
                    fun u  -> app head1 u FStar_Pervasives_Native.None)
                 uu____2793 uu____2794))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2802 =
               let uu____2803 = translate_univ bs u  in un_univ uu____2803
                in
             Type_t uu____2802
         | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
             (debug_term e; failwith "Tm_arrow: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_refine uu____2823 ->
             (debug_term e; failwith "Tm_refine: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2832,uu____2833) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____2894) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_name x -> mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2900,uu____2901) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (x::[],body,uu____2922) ->
             (debug
                (fun uu____2956  ->
                   let uu____2957 = FStar_Syntax_Print.tag_of_term body  in
                   let uu____2958 = FStar_Syntax_Print.term_to_string body
                      in
                   FStar_Util.print2 "Tm_abs body : %s - %s\n" uu____2957
                     uu____2958);
              (let x1 = FStar_Pervasives_Native.fst x  in
               Lam
                 ((fun y  -> translate cfg (y :: bs) body),
                   (fun uu____2969  ->
                      translate cfg bs x1.FStar_Syntax_Syntax.sort),
                   (FStar_Pervasives_Native.snd x))))
         | FStar_Syntax_Syntax.Tm_abs (x::xs,body,uu____2973) ->
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
             translate cfg bs tm
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app (e1,[]) ->
             failwith "Impossible: application with no arguments"
         | FStar_Syntax_Syntax.Tm_app (e1,arg::[]) ->
             (debug
                (fun uu____3095  ->
                   let uu____3096 = FStar_Syntax_Print.term_to_string e1  in
                   let uu____3097 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg)
                      in
                   FStar_Util.print2 "Application %s / %s\n" uu____3096
                     uu____3097);
              (let uu____3100 = translate cfg bs e1  in
               let uu____3101 =
                 translate cfg bs (FStar_Pervasives_Native.fst arg)  in
               app uu____3100 uu____3101 (FStar_Pervasives_Native.snd arg)))
         | FStar_Syntax_Syntax.Tm_app (head1,arg::args) ->
             (debug
                (fun uu____3148  ->
                   let uu____3149 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3150 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg)
                      in
                   FStar_Util.print2 "Application %s / %s (...more agrs)\n"
                     uu____3149 uu____3150);
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
               translate cfg bs tm))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | Construct (c,us,args) ->
                   (debug
                      (fun uu____3269  ->
                         let uu____3270 =
                           let uu____3271 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3294  ->
                                     match uu____3294 with
                                     | (x,q) ->
                                         let uu____3307 = t_to_string x  in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3307))
                              in
                           FStar_All.pipe_right uu____3271
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3270);
                    (let uu____3311 = pickBranch scrut1 branches  in
                     match uu____3311 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____3332 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____3332 branch1
                     | FStar_Pervasives_Native.None  ->
                         mkAccuMatch scrut1 patterns))
               | Constant c ->
                   let uu____3350 = pickBranch scrut1 branches  in
                   (match uu____3350 with
                    | FStar_Pervasives_Native.Some (branch1,[]) ->
                        translate cfg bs branch1
                    | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                        translate cfg (arg :: bs) branch1
                    | FStar_Pervasives_Native.None  ->
                        mkAccuMatch scrut1 patterns
                    | FStar_Pervasives_Native.Some (uu____3384,hd1::tl1) ->
                        failwith
                          "Impossible: Matching on constants cannot bind more than one variable")
               | uu____3397 -> mkAccuMatch scrut1 patterns
             
             and patterns readback1 =
               let rec process_pattern p =
                 let p_new =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       FStar_Syntax_Syntax.Pat_constant c
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____3429 =
                         let uu____3442 =
                           FStar_List.map
                             (fun uu____3463  ->
                                match uu____3463 with
                                | (p1,b) ->
                                    let uu____3474 = process_pattern p1  in
                                    (uu____3474, b)) args
                            in
                         (fvar1, uu____3442)  in
                       FStar_Syntax_Syntax.Pat_cons uu____3429
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let uu____3484 =
                         let uu___240_3485 = bvar  in
                         let uu____3486 =
                           let uu____3489 =
                             translate cfg bs bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3489  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___240_3485.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___240_3485.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____3486
                         }  in
                       FStar_Syntax_Syntax.Pat_var uu____3484
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let uu____3491 =
                         let uu___241_3492 = bvar  in
                         let uu____3493 =
                           let uu____3496 =
                             translate cfg bs bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3496  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___241_3492.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___241_3492.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____3493
                         }  in
                       FStar_Syntax_Syntax.Pat_wild uu____3491
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let uu____3503 =
                         let uu____3510 =
                           let uu___242_3511 = bvar  in
                           let uu____3512 =
                             let uu____3515 =
                               translate cfg bs bvar.FStar_Syntax_Syntax.sort
                                in
                             readback1 uu____3515  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___242_3511.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___242_3511.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3512
                           }  in
                         let uu____3516 =
                           let uu____3519 = translate cfg bs tm  in
                           readback1 uu____3519  in
                         (uu____3510, uu____3516)  in
                       FStar_Syntax_Syntax.Pat_dot_term uu____3503
                    in
                 let uu___243_3522 = p  in
                 {
                   FStar_Syntax_Syntax.v = p_new;
                   FStar_Syntax_Syntax.p =
                     (uu___243_3522.FStar_Syntax_Syntax.p)
                 }  in
               FStar_List.map
                 (fun uu____3551  ->
                    match uu____3551 with
                    | (pat,when_clause,uu____3576) ->
                        let uu____3589 = process_pattern pat  in
                        let uu____3590 =
                          let uu____3591 =
                            let uu____3592 = translate_pat pat  in
                            case uu____3592  in
                          readback1 uu____3591  in
                        (uu____3589, when_clause, uu____3590)) branches
              in let uu____3597 = translate cfg bs scrut  in case uu____3597
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
             let uu____3643 = make_rec_env lbs bs  in
             translate cfg uu____3643 body)

and (readback :
  FStar_TypeChecker_Normalize.cfg -> t -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun x  ->
      debug
        (fun uu____3653  ->
           let uu____3654 = t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____3654);
      (match x with
       | Univ u -> failwith "Readback of universes should not occur"
       | Unknown  ->
           FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | Constant (Unit ) -> FStar_Syntax_Syntax.unit_const
       | Constant (Bool (true )) -> FStar_Syntax_Util.exp_true_bool
       | Constant (Bool (false )) -> FStar_Syntax_Util.exp_false_bool
       | Constant (Int i) ->
           let uu____3657 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____3657 FStar_Syntax_Util.exp_int
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
             let uu____3679 =
               let uu____3680 = t ()  in readback cfg uu____3680  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____3679
              in
           let body =
             let uu____3682 = f (mkAccuVar x1)  in readback cfg uu____3682
              in
           FStar_Syntax_Util.abs [(x1, q)] body FStar_Pervasives_Native.None
       | Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____3729  ->
                  match uu____3729 with
                  | (x1,q) ->
                      let uu____3740 = readback cfg x1  in (uu____3740, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____3759 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____3766::uu____3767 ->
                let uu____3770 =
                  let uu____3773 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____3773
                    (FStar_List.rev us)
                   in
                apply uu____3770
            | [] ->
                let uu____3774 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____3774)
       | Accu (Var bv,[]) -> FStar_Syntax_Syntax.bv_to_name bv
       | Accu (Var bv,ts) ->
           let args =
             map_rev
               (fun uu____3821  ->
                  match uu____3821 with
                  | (x1,q) ->
                      let uu____3832 = readback cfg x1  in (uu____3832, q))
               ts
              in
           let uu____3833 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____3833 args
       | Accu (Match (scrut,patterns),ts) ->
           let args =
             map_rev
               (fun uu____3886  ->
                  match uu____3886 with
                  | (x1,q) ->
                      let uu____3897 = readback cfg x1  in (uu____3897, q))
               ts
              in
           let head1 =
             let scrut_new = readback cfg scrut  in
             let branches_new = patterns (readback cfg)  in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_match (scrut_new, branches_new))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           (match ts with
            | [] -> head1
            | uu____3927 -> FStar_Syntax_Util.mk_app head1 args)
       | Accu (Rec (lb,lbs,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____4014 = curry hd1 args1  in
                 app uu____4014 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
              in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef  in
           let uu____4016 = test_args ts args_no  in
           if uu____4016
           then
             let uu____4017 =
               let uu____4018 =
                 let uu____4019 = make_rec_env lbs bs  in
                 translate_letbinding cfg uu____4019 lb  in
               curry uu____4018 ts  in
             readback cfg uu____4017
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
                  (fun uu____4064  ->
                     match uu____4064 with
                     | (x1,q) ->
                         let uu____4075 = readback cfg x1  in (uu____4075, q))
                  ts
                 in
              match ts with
              | [] -> head1
              | uu____4080 -> FStar_Syntax_Util.mk_app head1 args))

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____4109 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____4116 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____4132 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____4152 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____4165 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____4171 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Normalize.step) =
  fun uu___239_4176  ->
    match uu___239_4176 with
    | Primops  -> FStar_TypeChecker_Normalize.Primops
    | UnfoldUntil d -> FStar_TypeChecker_Normalize.UnfoldUntil d
    | UnfoldOnly lids -> FStar_TypeChecker_Normalize.UnfoldOnly lids
    | UnfoldAttr attr -> FStar_TypeChecker_Normalize.UnfoldAttr attr
    | UnfoldTac  -> FStar_TypeChecker_Normalize.UnfoldTac
    | Reify  -> FStar_TypeChecker_Normalize.Reify
  
let (normalize :
  step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg =
          let uu____4202 = FStar_List.map step_as_normalizer_step steps  in
          FStar_TypeChecker_Normalize.config uu____4202 env  in
        let uu____4205 = translate cfg [] e  in readback cfg uu____4205
  