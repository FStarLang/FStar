open Prims
let max: Prims.int -> Prims.int -> Prims.int =
  fun a  -> fun b  -> if a > b then a else b
let map_rev: 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____56 = let uu____59 = f x in uu____59 :: acc in
            aux xs uu____56 in
      aux l []
let rec drop: 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p  ->
    fun l  ->
      match l with
      | [] -> []
      | x::xs ->
          let uu____88 = p x in if uu____88 then x :: xs else drop p xs
let debug: (Prims.unit -> Prims.unit) -> Prims.unit =
  fun f  ->
    let uu____100 =
      FStar_Options.debug_at_level "Test" (FStar_Options.Other "NBE") in
    if uu____100 then f () else ()
let debug_term: FStar_Syntax_Syntax.term -> Prims.unit =
  fun t  ->
    let uu____105 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.print1 "%s\n" uu____105
let debug_sigmap: FStar_Syntax_Syntax.sigelt FStar_Util.smap -> Prims.unit =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____120 = FStar_Syntax_Print.sigelt_to_string_short v1 in
             FStar_Util.print2 "%s -> %%s\n" k uu____120) ()
type var = FStar_Syntax_Syntax.bv[@@deriving show]
type sort = Prims.int[@@deriving show]
type atom =
  | Var of var
  | Match of (t,t -> t) FStar_Pervasives_Native.tuple2
  | Rec of (FStar_Syntax_Syntax.letbinding,t Prims.list)
  FStar_Pervasives_Native.tuple2[@@deriving show]
and t =
  | Lam of (t -> t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
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
  | Unit
  | Bool of Prims.bool
  | Int of FStar_BigInt.t
  | Type_t of FStar_Syntax_Syntax.universe
  | Univ of FStar_Syntax_Syntax.universe[@@deriving show]
let uu___is_Var: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____211 -> false
let __proj__Var__item___0: atom -> var =
  fun projectee  -> match projectee with | Var _0 -> _0
let uu___is_Match: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____229 -> false
let __proj__Match__item___0:
  atom -> (t,t -> t) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Rec: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____265 -> false
let __proj__Rec__item___0:
  atom ->
    (FStar_Syntax_Syntax.letbinding,t Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Rec _0 -> _0
let uu___is_Lam: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____301 -> false
let __proj__Lam__item___0:
  t -> (t -> t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Lam _0 -> _0
let uu___is_Accu: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____341 -> false
let __proj__Accu__item___0:
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Accu _0 -> _0
let uu___is_Construct: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____397 -> false
let __proj__Construct__item___0:
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Construct _0 -> _0
let uu___is_Unit: t -> Prims.bool =
  fun projectee  -> match projectee with | Unit  -> true | uu____450 -> false
let uu___is_Bool: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____455 -> false
let __proj__Bool__item___0: t -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
let uu___is_Int: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____467 -> false
let __proj__Int__item___0: t -> FStar_BigInt.t =
  fun projectee  -> match projectee with | Int _0 -> _0
let uu___is_Type_t: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____479 -> false
let __proj__Type_t__item___0: t -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Type_t _0 -> _0
let uu___is_Univ: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____491 -> false
let __proj__Univ__item___0: t -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
type head = t[@@deriving show]
type annot = t FStar_Pervasives_Native.option[@@deriving show]
let rec t_to_string: t -> Prims.string =
  fun x  ->
    match x with
    | Lam uu____506 -> "Lam"
    | Accu (a,l) ->
        let uu____527 =
          let uu____528 = atom_to_string a in
          let uu____529 =
            let uu____530 =
              let uu____531 =
                let uu____532 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l in
                FStar_String.concat "; " uu____532 in
              Prims.strcat uu____531 ")" in
            Prims.strcat ") (" uu____530 in
          Prims.strcat uu____528 uu____529 in
        Prims.strcat "Accu (" uu____527
    | Construct (fv,us,l) ->
        let uu____564 =
          let uu____565 = FStar_Syntax_Print.fv_to_string fv in
          let uu____566 =
            let uu____567 =
              let uu____568 =
                let uu____569 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us in
                FStar_String.concat "; " uu____569 in
              let uu____572 =
                let uu____573 =
                  let uu____574 =
                    let uu____575 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l in
                    FStar_String.concat "; " uu____575 in
                  Prims.strcat uu____574 ")" in
                Prims.strcat "] (" uu____573 in
              Prims.strcat uu____568 uu____572 in
            Prims.strcat ") [" uu____567 in
          Prims.strcat uu____565 uu____566 in
        Prims.strcat "Construct (" uu____564
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Univ u ->
        let uu____592 = FStar_Syntax_Print.univ_to_string u in
        Prims.strcat "Universe " uu____592
    | Type_t u ->
        let uu____594 = FStar_Syntax_Print.univ_to_string u in
        Prims.strcat "Type_t " uu____594
and atom_to_string: atom -> Prims.string =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____597 = FStar_Syntax_Print.bv_to_string v1 in
        Prims.strcat "Var " uu____597
    | Match (t,uu____599) ->
        let uu____604 = t_to_string t in Prims.strcat "Match " uu____604
    | Rec (uu____605,l) ->
        let uu____611 =
          let uu____612 =
            let uu____613 = FStar_List.map t_to_string l in
            FStar_String.concat "; " uu____613 in
          Prims.strcat uu____612 ")" in
        Prims.strcat "Rec (" uu____611
let is_not_accu: t -> Prims.bool =
  fun x  ->
    match x with | Accu (uu____619,uu____620) -> false | uu____633 -> true
let mkConstruct:
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
        -> t
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts)
let mkAccuVar: var -> t = fun v1  -> Accu ((Var v1), [])
let mkAccuMatch: t -> (t -> t) -> t =
  fun s  -> fun c  -> Accu ((Match (s, c)), [])
let mkAccuRec: FStar_Syntax_Syntax.letbinding -> t Prims.list -> t =
  fun b  -> fun env  -> Accu ((Rec (b, env)), [])
let isAccu: t -> Prims.bool =
  fun trm  -> match trm with | Accu uu____728 -> true | uu____739 -> false
let rec pickBranch:
  t ->
    FStar_Syntax_Syntax.branch Prims.list ->
      (FStar_Syntax_Syntax.term,t Prims.list) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun scrut  ->
    fun branches  ->
      let rec matches_pat scrutinee p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_var bv -> FStar_Util.Inl [scrutinee]
        | FStar_Syntax_Syntax.Pat_wild bv -> FStar_Util.Inl [scrutinee]
        | FStar_Syntax_Syntax.Pat_dot_term uu____791 -> FStar_Util.Inl []
        | FStar_Syntax_Syntax.Pat_constant s ->
            failwith
              "Constant patterns are not yet supported; should be easy"
        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
            let rec matches_args out a p1 =
              match (a, p1) with
              | ([],[]) -> FStar_Util.Inl out
              | ((t,uu____910)::rest_a,(p2,uu____913)::rest_p) ->
                  let uu____947 = matches_pat t p2 in
                  (match uu____947 with
                   | FStar_Util.Inl s ->
                       matches_args (FStar_List.append out s) rest_a rest_p
                   | m -> m)
              | uu____972 -> FStar_Util.Inr false in
            (match scrutinee with
             | Construct (fv',_us,args_rev) ->
                 let uu____1016 = FStar_Syntax_Syntax.fv_eq fv fv' in
                 if uu____1016
                 then matches_args [] (FStar_List.rev args_rev) arg_pats
                 else FStar_Util.Inr false
             | uu____1030 -> FStar_Util.Inr true) in
      match branches with
      | [] -> failwith "Branch not found"
      | (p,_wopt,e)::branches1 ->
          let uu____1099 = matches_pat scrut p in
          (match uu____1099 with
           | FStar_Util.Inl matches ->
               FStar_Pervasives_Native.Some (e, matches)
           | FStar_Util.Inr (false ) -> pickBranch scrut branches1
           | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
let rec test_args:
  'Auu____1146 .
    (t,'Auu____1146) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int -> Prims.bool
  =
  fun ts  ->
    fun cnt  ->
      match ts with
      | [] -> cnt <= (Prims.parse_int "0")
      | t::ts1 ->
          (Prims.op_Negation (isAccu (FStar_Pervasives_Native.fst t))) &&
            (test_args ts1 (cnt - (Prims.parse_int "1")))
let rec count_abstractions: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    let uu____1190 =
      let uu____1191 = FStar_Syntax_Subst.compress t in
      uu____1191.FStar_Syntax_Syntax.n in
    match uu____1190 with
    | FStar_Syntax_Syntax.Tm_delayed uu____1194 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____1219 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_name uu____1220 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_fvar uu____1221 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_constant uu____1222 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_type uu____1223 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_arrow uu____1224 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_uvar uu____1237 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_refine uu____1254 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_unknown  -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1262) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1269) ->
        let uu____1290 = count_abstractions body in
        (FStar_List.length xs) + uu____1290
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1317 =
          let uu____1318 = count_abstractions head1 in
          uu____1318 - (FStar_List.length args) in
        max uu____1317 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____1377,uu____1378,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____1427,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1446) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1452,uu____1453) ->
        count_abstractions t1
let find_sigelt_in_gamma:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____1527 =
        match uu____1527 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                 FStar_Pervasives_Native.Some elt
             | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                 (debug
                    (fun uu____1612  ->
                       let uu____1613 = FStar_Syntax_Print.univs_to_string us in
                       FStar_Util.print1
                         "Universes in local declaration: %s\n" uu____1613);
                  FStar_Pervasives_Native.Some elt)
             | uu____1614 -> FStar_Pervasives_Native.None) in
      let uu____1629 = FStar_TypeChecker_Env.lookup_qname env lid in
      FStar_Util.bind_opt uu____1629 mapper
let translate_univ: t Prims.list -> FStar_Syntax_Syntax.universe -> t =
  fun bs  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar i ->
            let uu____1684 = FStar_List.nth bs i in
            (match uu____1684 with | Univ u3 -> u3)
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1687 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1687
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1691 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1691
        | FStar_Syntax_Syntax.U_name uu____1694 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_unif uu____1695 ->
            failwith "Unknown or unconstrained universe"
        | FStar_Syntax_Syntax.U_unknown  ->
            failwith "Unknown or unconstrained universe" in
      let uu____1704 = aux u in Univ uu____1704
let is_univ: t -> Prims.bool =
  fun tm  -> match tm with | Univ uu____1708 -> true | uu____1709 -> false
let un_univ: t -> FStar_Syntax_Syntax.universe =
  fun tm  ->
    match tm with | Univ u -> u | uu____1714 -> failwith "Not a universe"
let rec app: t -> t -> FStar_Syntax_Syntax.aqual -> t =
  fun f  ->
    fun x  ->
      fun q  ->
        debug
          (fun uu____1769  ->
             let uu____1770 = t_to_string f in
             let uu____1771 = t_to_string x in
             FStar_Util.print2 "When creating app: %s applied to %s\n"
               uu____1770 uu____1771);
        (match f with
         | Lam (f1,uu____1773) -> f1 x
         | Accu (a,ts) -> Accu (a, ((x, q) :: ts))
         | Construct (i,us,ts) ->
             (match x with
              | Univ u -> Construct (i, (u :: us), ts)
              | uu____1830 -> Construct (i, us, ((x, q) :: ts)))
         | Unit  -> failwith "Ill-typed application"
         | Bool uu____1843 -> failwith "Ill-typed application"
         | Univ uu____1844 -> failwith "Ill-typed application"
         | Type_t uu____1845 -> failwith "Ill-typed application")
and iapp:
  t ->
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
      -> t
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____1858 ->
          let uu____1865 =
            let uu____1866 =
              let uu____1867 = FStar_List.hd args in
              FStar_Pervasives_Native.fst uu____1867 in
            let uu____1876 =
              let uu____1877 = FStar_List.hd args in
              FStar_Pervasives_Native.snd uu____1877 in
            app f uu____1866 uu____1876 in
          let uu____1886 = FStar_List.tl args in iapp uu____1865 uu____1886
and translate_fv:
  FStar_TypeChecker_Env.env -> t Prims.list -> FStar_Syntax_Syntax.fv -> t =
  fun env  ->
    fun bs  ->
      fun fvar1  ->
        let find_in_sigtab env1 lid =
          FStar_Util.smap_try_find env1.FStar_TypeChecker_Env.sigtab
            (FStar_Ident.text_of_lid lid) in
        let uu____1913 =
          let uu____1918 =
            let uu____1923 =
              find_sigelt_in_gamma env
                (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____1926 =
              let uu____1931 =
                find_in_sigtab env
                  (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              [uu____1931] in
            uu____1923 :: uu____1926 in
          FStar_List.find FStar_Util.is_some uu____1918 in
        match uu____1913 with
        | FStar_Pervasives_Native.Some elt ->
            (match elt with
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,lb::[]),uu____1949);
                   FStar_Syntax_Syntax.sigrng = uu____1950;
                   FStar_Syntax_Syntax.sigquals = uu____1951;
                   FStar_Syntax_Syntax.sigmeta = uu____1952;
                   FStar_Syntax_Syntax.sigattrs = uu____1953;_}
                 ->
                 if is_rec
                 then mkAccuRec lb []
                 else
                   (debug
                      (fun uu____1974  ->
                         FStar_Util.print "Translate fv: it's a Sig_let\n" []);
                    debug
                      (fun uu____1982  ->
                         let uu____1983 =
                           let uu____1984 =
                             FStar_Syntax_Subst.compress
                               lb.FStar_Syntax_Syntax.lbtyp in
                           FStar_Syntax_Print.tag_of_term uu____1984 in
                         let uu____1985 =
                           let uu____1986 =
                             FStar_Syntax_Subst.compress
                               lb.FStar_Syntax_Syntax.lbtyp in
                           FStar_Syntax_Print.term_to_string uu____1986 in
                         FStar_Util.print2 "Type of lbdef: %s - %s\n"
                           uu____1983 uu____1985);
                    debug
                      (fun uu____1994  ->
                         let uu____1995 =
                           let uu____1996 =
                             FStar_Syntax_Subst.compress
                               lb.FStar_Syntax_Syntax.lbdef in
                           FStar_Syntax_Print.tag_of_term uu____1996 in
                         let uu____1997 =
                           let uu____1998 =
                             FStar_Syntax_Subst.compress
                               lb.FStar_Syntax_Syntax.lbdef in
                           FStar_Syntax_Print.term_to_string uu____1998 in
                         FStar_Util.print2 "Body of lbdef: %s - %s\n"
                           uu____1995 uu____1997);
                    translate_letbinding env [] lb)
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel =
                     FStar_Syntax_Syntax.Sig_datacon
                     (uu____1999,uu____2000,uu____2001,lid,uu____2003,[]);
                   FStar_Syntax_Syntax.sigrng = uu____2004;
                   FStar_Syntax_Syntax.sigquals = uu____2005;
                   FStar_Syntax_Syntax.sigmeta = uu____2006;
                   FStar_Syntax_Syntax.sigattrs = uu____2007;_}
                 ->
                 (debug
                    (fun uu____2019  ->
                       let uu____2020 = FStar_Syntax_Print.lid_to_string lid in
                       FStar_Util.print1
                         "Translate fv %s: it's a Sig_datacon\n" uu____2020);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel =
                     FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,univs1,bs1,ty,uu____2029,uu____2030);
                   FStar_Syntax_Syntax.sigrng = uu____2031;
                   FStar_Syntax_Syntax.sigquals = uu____2032;
                   FStar_Syntax_Syntax.sigmeta = uu____2033;
                   FStar_Syntax_Syntax.sigattrs = uu____2034;_}
                 ->
                 (debug
                    (fun uu____2052  ->
                       let uu____2053 = FStar_Syntax_Print.lid_to_string lid in
                       FStar_Util.print1
                         "Translate fv %s: it's a Sig_inductive_type\n"
                         uu____2053);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel =
                     FStar_Syntax_Syntax.Sig_declare_typ
                     (lid,uu____2059,uu____2060);
                   FStar_Syntax_Syntax.sigrng = uu____2061;
                   FStar_Syntax_Syntax.sigquals = uu____2062;
                   FStar_Syntax_Syntax.sigmeta = uu____2063;
                   FStar_Syntax_Syntax.sigattrs = uu____2064;_}
                 ->
                 (debug
                    (fun uu____2074  ->
                       let uu____2075 = FStar_Syntax_Print.lid_to_string lid in
                       FStar_Util.print1
                         "Translate fv %s: it's a Sig_declare_typ\n"
                         uu____2075);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.None  ->
                 (debug
                    (fun uu____2083  ->
                       FStar_Util.print
                         "Translate fv: it's not in the environment\n" []);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.Some s ->
                 let uu____2089 =
                   let uu____2090 = FStar_Syntax_Print.sigelt_to_string s in
                   FStar_Util.format1 "Sig %s\n" uu____2090 in
                 FStar_All.pipe_right uu____2089 failwith)
        | FStar_Pervasives_Native.None  -> mkConstruct fvar1 [] []
and translate_letbinding:
  FStar_TypeChecker_Env.env ->
    t Prims.list -> FStar_Syntax_Syntax.letbinding -> t
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
                  FStar_Pervasives_Native.None) in
        make_univ_abst lb.FStar_Syntax_Syntax.lbunivs bs
          lb.FStar_Syntax_Syntax.lbdef
and translate:
  FStar_TypeChecker_Env.env -> t Prims.list -> FStar_Syntax_Syntax.term -> t
  =
  fun env  ->
    fun bs  ->
      fun e  ->
        debug
          (fun uu____2142  ->
             let uu____2143 =
               let uu____2144 = FStar_Syntax_Subst.compress e in
               FStar_Syntax_Print.tag_of_term uu____2144 in
             let uu____2145 =
               let uu____2146 = FStar_Syntax_Subst.compress e in
               FStar_Syntax_Print.term_to_string uu____2146 in
             FStar_Util.print2 "Term: %s - %s\n" uu____2143 uu____2145);
        debug
          (fun uu____2152  ->
             let uu____2153 =
               let uu____2154 = FStar_List.map (fun x  -> t_to_string x) bs in
               FStar_String.concat ";; " uu____2154 in
             FStar_Util.print1 "BS list: %s\n" uu____2153);
        (let uu____2159 =
           let uu____2160 = FStar_Syntax_Subst.compress e in
           uu____2160.FStar_Syntax_Syntax.n in
         match uu____2159 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2163,uu____2164) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             failwith "Tm_unknown: Impossible"
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) -> Unit
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Bool b
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,FStar_Pervasives_Native.None )) ->
             let uu____2217 = FStar_BigInt.big_int_of_string s in
             Int uu____2217
         | FStar_Syntax_Syntax.Tm_constant c ->
             let err =
               let uu____2220 =
                 let uu____2221 = FStar_Syntax_Print.const_to_string c in
                 Prims.strcat uu____2221 ": Not yet implemented" in
               Prims.strcat "Tm_constant " uu____2220 in
             (debug_term e; failwith err)
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug
                (fun uu____2239  ->
                   let uu____2240 = FStar_Syntax_Print.tag_of_term t in
                   let uu____2241 = FStar_Syntax_Print.term_to_string t in
                   let uu____2242 =
                     let uu____2243 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us in
                     FStar_All.pipe_right uu____2243
                       (FStar_String.concat ", ") in
                   FStar_Util.print3 "Term with univs: %s - %s\nUniv %s\n"
                     uu____2240 uu____2241 uu____2242);
              (let uu____2248 = translate env bs t in
               let uu____2249 = FStar_List.map (translate_univ bs) us in
               FStar_List.fold_left
                 (fun head1  ->
                    fun u  -> app head1 u FStar_Pervasives_Native.None)
                 uu____2248 uu____2249))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2257 =
               let uu____2258 = translate_univ bs u in un_univ uu____2258 in
             Type_t uu____2257
         | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
             (debug_term e; failwith "Tm_arrow: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_refine uu____2278 ->
             (debug_term e; failwith "Tm_refine: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2287,uu____2288) ->
             translate env bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____2357) -> translate env bs e1
         | FStar_Syntax_Syntax.Tm_name x -> mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2363,uu____2364) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (x::[],body,uu____2385) ->
             (debug
                (fun uu____2419  ->
                   let uu____2420 = FStar_Syntax_Print.tag_of_term body in
                   let uu____2421 = FStar_Syntax_Print.term_to_string body in
                   FStar_Util.print2 "Tm_abs body : %s - %s\n" uu____2420
                     uu____2421);
              Lam
                (((fun y  -> translate env (y :: bs) body)),
                  (FStar_Pervasives_Native.snd x)))
         | FStar_Syntax_Syntax.Tm_abs (x::xs,body,uu____2429) ->
             let rest =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_abs
                    (xs, body, FStar_Pervasives_Native.None))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange in
             let tm =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_abs
                    ([x], rest, FStar_Pervasives_Native.None))
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
             translate env bs tm
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv env bs fvar1
         | FStar_Syntax_Syntax.Tm_app (e1,[]) ->
             failwith "Impossible: application with no arguments"
         | FStar_Syntax_Syntax.Tm_app (e1,arg::[]) ->
             (debug
                (fun uu____2551  ->
                   let uu____2552 = FStar_Syntax_Print.term_to_string e1 in
                   let uu____2553 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg) in
                   FStar_Util.print2 "Application %s / %s\n" uu____2552
                     uu____2553);
              (let uu____2556 = translate env bs e1 in
               let uu____2557 =
                 translate env bs (FStar_Pervasives_Native.fst arg) in
               app uu____2556 uu____2557 (FStar_Pervasives_Native.snd arg)))
         | FStar_Syntax_Syntax.Tm_app (head1,arg::args) ->
             (debug
                (fun uu____2604  ->
                   let uu____2605 = FStar_Syntax_Print.term_to_string head1 in
                   let uu____2606 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg) in
                   FStar_Util.print2 "Application %s / %s (...more agrs)\n"
                     uu____2605 uu____2606);
              (let first =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               let tm =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (first, args))
                   FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
               translate env bs tm))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | Construct (c,us,args) ->
                   (debug
                      (fun uu____2713  ->
                         let uu____2714 =
                           let uu____2715 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____2736  ->
                                     match uu____2736 with
                                     | (x,q) ->
                                         let uu____2749 = t_to_string x in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____2749)) in
                           FStar_All.pipe_right uu____2715
                             (FStar_String.concat "; ") in
                         FStar_Util.print1 "Match args: %s\n" uu____2714);
                    (let uu____2753 = pickBranch scrut1 branches in
                     match uu____2753 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____2774 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1 in
                         translate env uu____2774 branch1
                     | FStar_Pervasives_Native.None  ->
                         mkAccuMatch scrut1 case))
               | uu____2791 -> mkAccuMatch scrut1 case in
             let uu____2792 = translate env bs scrut in case uu____2792
         | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
             let def = translate_letbinding env bs lb in
             translate env (def :: bs) body
         | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),body) ->
             let f = mkAccuRec lb bs in translate env (f :: bs) body
         | FStar_Syntax_Syntax.Tm_let uu____2823 ->
             failwith "Mutual recursion; not yet handled")
and readback: FStar_TypeChecker_Env.env -> t -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun x  ->
      debug
        (fun uu____2843  ->
           let uu____2844 = t_to_string x in
           FStar_Util.print1 "Readback: %s\n" uu____2844);
      (match x with
       | Unit  -> FStar_Syntax_Syntax.unit_const
       | Univ u -> failwith "Readback of universes should not occur"
       | Bool (true ) -> FStar_Syntax_Util.exp_true_bool
       | Bool (false ) -> FStar_Syntax_Util.exp_false_bool
       | Int i ->
           let uu____2847 = FStar_BigInt.string_of_big_int i in
           FStar_All.pipe_right uu____2847 FStar_Syntax_Util.exp_int
       | Type_t u ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | Lam (f,q) ->
           let x1 =
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               FStar_Syntax_Syntax.tun in
           let body =
             let uu____2857 = f (mkAccuVar x1) in readback env uu____2857 in
           FStar_Syntax_Util.abs [(x1, q)] body FStar_Pervasives_Native.None
       | Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____2904  ->
                  match uu____2904 with
                  | (x1,q) ->
                      let uu____2915 = readback env x1 in (uu____2915, q))
               args in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____2932 -> FStar_Syntax_Util.mk_app tm args1 in
           (match us with
            | uu____2939::uu____2940 ->
                let uu____2943 =
                  let uu____2946 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____2946
                    (FStar_List.rev us) in
                apply1 uu____2943
            | [] ->
                let uu____2947 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                apply1 uu____2947)
       | Accu (Var bv,[]) -> FStar_Syntax_Syntax.bv_to_name bv
       | Accu (Var bv,ts) ->
           let args =
             map_rev
               (fun uu____2994  ->
                  match uu____2994 with
                  | (x1,q) ->
                      let uu____3005 = readback env x1 in (uu____3005, q)) ts in
           let uu____3006 = FStar_Syntax_Syntax.bv_to_name bv in
           FStar_Syntax_Util.mk_app uu____3006 args
       | Accu (Match (scrut,cases),ts) ->
           let args =
             map_rev
               (fun uu____3047  ->
                  match uu____3047 with
                  | (x1,q) ->
                      let uu____3058 = readback env x1 in (uu____3058, q)) ts in
           let head1 =
             let uu____3060 = cases scrut in readback env uu____3060 in
           (match ts with
            | [] -> head1
            | uu____3065 -> FStar_Syntax_Util.mk_app head1 args)
       | Accu (Rec (lb,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____3143 = curry hd1 args1 in
                 app uu____3143 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg) in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef in
           let uu____3145 = test_args ts args_no in
           if uu____3145
           then
             let uu____3146 =
               let uu____3147 =
                 translate_letbinding env ((mkAccuRec lb bs) :: bs) lb in
               curry uu____3147 ts in
             readback env uu____3146
           else
             (let head1 =
                let f =
                  match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inl bv -> FStar_Syntax_Syntax.bv_to_name bv
                  | FStar_Util.Inr fv -> failwith "Not yet implemented" in
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((true, [lb]), f))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange in
              let args =
                map_rev
                  (fun uu____3182  ->
                     match uu____3182 with
                     | (x1,q) ->
                         let uu____3193 = readback env x1 in (uu____3193, q))
                  ts in
              match ts with
              | [] -> head1
              | uu____3198 -> FStar_Syntax_Util.mk_app head1 args))
let normalize:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  -> let uu____3211 = translate env [] e in readback env uu____3211