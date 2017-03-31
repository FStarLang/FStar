open Prims
let subst_to_string s =
  let uu____14 =
    FStar_All.pipe_right s
      (FStar_List.map
         (fun uu____22  ->
            match uu____22 with
            | (b,uu____26) ->
                (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
     in
  FStar_All.pipe_right uu____14 (FStar_String.concat ", ") 
let rec apply_until_some f s =
  match s with
  | [] -> None
  | s0::rest ->
      let uu____61 = f s0  in
      (match uu____61 with
       | None  -> apply_until_some f rest
       | Some st -> Some (rest, st))
  
let map_some_curry f x uu___100_101 =
  match uu___100_101 with | None  -> x | Some (a,b) -> f a b 
let apply_until_some_then_map f s g t =
  let uu____162 = apply_until_some f s  in
  FStar_All.pipe_right uu____162 (map_some_curry g t) 
let compose_subst s1 s2 =
  let s = FStar_List.append (Prims.fst s1) (Prims.fst s2)  in
  let ropt =
    match Prims.snd s2 with
    | Some uu____217 -> Prims.snd s2
    | uu____220 -> Prims.snd s1  in
  (s, ropt) 
let delay :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range
      Prims.option) -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed
            (FStar_Util.Inl (t', (compose_subst s' s)))
            t.FStar_Syntax_Syntax.pos
      | uu____316 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t, s))
            t.FStar_Syntax_Syntax.pos
  
let rec force_uvar' :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____347) ->
        let uu____360 = FStar_Unionfind.find uv  in
        (match uu____360 with
         | FStar_Syntax_Syntax.Fixed t' -> force_uvar' t'
         | uu____374 -> t)
    | uu____378 -> t
  
let force_uvar :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t  in
    let uu____391 = FStar_Util.physical_equality t t'  in
    if uu____391
    then t
    else delay t' ([], (Some (t.FStar_Syntax_Syntax.pos)))
  
let rec force_delayed_thunk :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____450 = FStar_ST.read m  in
        (match uu____450 with
         | None  ->
             (match f with
              | FStar_Util.Inr c ->
                  let t' =
                    let uu____486 = c ()  in force_delayed_thunk uu____486
                     in
                  (FStar_ST.write m (Some t'); t')
              | uu____497 -> t)
         | Some t' ->
             let t'1 = force_delayed_thunk t'  in
             (FStar_ST.write m (Some t'1); t'1))
    | uu____529 -> t
  
let rec compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____536 = FStar_Unionfind.find u'  in
        (match uu____536 with | Some u1 -> compress_univ u1 | uu____540 -> u)
    | uu____542 -> u
  
let subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term Prims.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___101_552  ->
           match uu___101_552 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____556 =
                 let uu____557 =
                   let uu____558 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____558  in
                 FStar_Syntax_Syntax.bv_to_name uu____557  in
               Some uu____556
           | uu____559 -> None)
  
let subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term Prims.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___102_569  ->
           match uu___102_569 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____573 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___107_574 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___107_574.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___107_574.FStar_Syntax_Syntax.sort)
                    })
                  in
               Some uu____573
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> Some t
           | uu____583 -> None)
  
let subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe Prims.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___103_593  ->
           match uu___103_593 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y -> Some t
           | uu____597 -> None)
  
let subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe Prims.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___104_607  ->
           match uu___104_607 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____611 -> None)
  
let rec subst_univ :
  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun s  ->
    fun u  ->
      let u1 = compress_univ u  in
      match u1 with
      | FStar_Syntax_Syntax.U_bvar x ->
          apply_until_some_then_map (subst_univ_bv x) s subst_univ u1
      | FStar_Syntax_Syntax.U_name x ->
          apply_until_some_then_map (subst_univ_nm x) s subst_univ u1
      | FStar_Syntax_Syntax.U_zero 
        |FStar_Syntax_Syntax.U_unknown |FStar_Syntax_Syntax.U_unif _ -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____629 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____629
      | FStar_Syntax_Syntax.U_max us ->
          let uu____632 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____632
  
let tag_with_range t s =
  match Prims.snd s with
  | None  -> t
  | Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r  in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____665 = FStar_Syntax_Syntax.set_range_of_bv bv r1  in
            FStar_Syntax_Syntax.Tm_bvar uu____665
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____667 = FStar_Syntax_Syntax.set_range_of_bv bv r1  in
            FStar_Syntax_Syntax.Tm_name uu____667
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            let v1 =
              let uu___108_675 = fv.FStar_Syntax_Syntax.fv_name  in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.ty =
                  (uu___108_675.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___108_675.FStar_Syntax_Syntax.p)
              }  in
            let fv1 =
              let uu___109_691 = fv  in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___109_691.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___109_691.FStar_Syntax_Syntax.fv_qual)
              }  in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t'  in
      let uu___110_693 = t  in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___110_693.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___110_693.FStar_Syntax_Syntax.vars)
      }
  
let tag_lid_with_range l s =
  match Prims.snd s with
  | None  -> l
  | Some r ->
      let uu____720 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r  in
      FStar_Ident.set_lid_range l uu____720
  
let mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match Prims.snd s with
      | None  -> r
      | Some r' -> FStar_Range.set_use_range r r'
  
let rec subst' :
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (Prims.snd s))  in
      match s with
      | ([],None )|([]::[],None ) -> t
      | uu____802 ->
          let t0 = force_delayed_thunk t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown 
             |FStar_Syntax_Syntax.Tm_constant _
              |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_uvar _ ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed
                 (FStar_Util.Inl (t', (compose_subst s' s)))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_delayed
               (FStar_Util.Inr uu____883,uu____884) ->
               failwith
                 "Impossible: force_delayed_thunk removes lazy delayed nodes"
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a) (Prims.fst s)
                 subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a) (Prims.fst s)
                 subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____940 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____941 =
                 let uu____944 =
                   let uu____945 = subst_univ (Prims.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____945  in
                 FStar_Syntax_Syntax.mk uu____944  in
               uu____941 None uu____940
           | uu____957 ->
               let uu____958 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t0, s))
                 uu____958)

and subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___105_972  ->
              match uu___105_972 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____976 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____976
              | f -> f))

and subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range
    Prims.option) ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],None )|([]::[],None ) -> t
      | uu____996 ->
          let uu___111_1002 = t  in
          let uu____1003 =
            tag_lid_with_range t.FStar_Syntax_Syntax.comp_typ_name s  in
          let uu____1006 =
            FStar_List.map (subst_univ (Prims.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1010 =
            FStar_List.map
              (fun uu____1024  ->
                 match uu____1024 with
                 | (t1,imp) ->
                     let uu____1039 = subst' s t1  in (uu____1039, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1044 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_typ_name = uu____1003;
            FStar_Syntax_Syntax.comp_univs = uu____1006;
            FStar_Syntax_Syntax.effect_args = uu____1010;
            FStar_Syntax_Syntax.flags = uu____1044
          }

and subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range
    Prims.option) ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],None )|([]::[],None ) -> t
      | uu____1066 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1082 = subst' s t1  in
               let uu____1083 =
                 FStar_Option.map (subst_univ (Prims.fst s)) uopt  in
               FStar_Syntax_Syntax.mk_Total' uu____1082 uu____1083
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1096 = subst' s t1  in
               let uu____1097 =
                 FStar_Option.map (subst_univ (Prims.fst s)) uopt  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1096 uu____1097
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1103 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1103)

let shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt
  =
  fun n1  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n1), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n1), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n1))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n1))
      | FStar_Syntax_Syntax.NT uu____1118 -> s
  
let shift_subst :
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' n1 s =
  let uu____1150 =
    FStar_All.pipe_right (Prims.fst s) (FStar_List.map (shift_subst n1))  in
  (uu____1150, (Prims.snd s)) 
let subst_binder' s uu____1172 =
  match uu____1172 with
  | (x,imp) ->
      let uu____1177 =
        let uu___112_1178 = x  in
        let uu____1179 = subst' s x.FStar_Syntax_Syntax.sort  in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___112_1178.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___112_1178.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1179
        }  in
      (uu____1177, imp)
  
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1220 = shift_subst' i s  in
               subst_binder' uu____1220 b)))
  
let subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs 
let subst_arg' s uu____1254 =
  match uu____1254 with
  | (t,imp) -> let uu____1265 = subst' s t  in (uu____1265, imp) 
let subst_args' s = FStar_List.map (subst_arg' s) 
let subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range Prims.option)
    ->
    (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t -> (FStar_Syntax_Syntax.pat * Prims.int)
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_disj [] ->
            failwith "Impossible: empty disjunction"
        | FStar_Syntax_Syntax.Pat_constant uu____1340 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_disj (p2::ps) ->
            let uu____1352 = aux n1 p2  in
            (match uu____1352 with
             | (p3,m) ->
                 let ps1 =
                   FStar_List.map
                     (fun p4  ->
                        let uu____1366 = aux n1 p4  in Prims.fst uu____1366)
                     ps
                    in
                 ((let uu___113_1371 = p3  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                     FStar_Syntax_Syntax.ty =
                       (uu___113_1371.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___113_1371.FStar_Syntax_Syntax.p)
                   }), m))
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1384 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1409  ->
                      fun uu____1410  ->
                        match (uu____1409, uu____1410) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1457 = aux n2 p2  in
                            (match uu____1457 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1384 with
             | (pats1,n2) ->
                 ((let uu___114_1489 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.ty =
                       (uu___114_1489.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___114_1489.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___115_1505 = x  in
              let uu____1506 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___115_1505.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___115_1505.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1506
              }  in
            ((let uu___116_1511 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.ty =
                  (uu___116_1511.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___116_1511.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___117_1522 = x  in
              let uu____1523 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___117_1522.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___117_1522.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1523
              }  in
            ((let uu___118_1528 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.ty =
                  (uu___118_1528.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___118_1528.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___119_1544 = x  in
              let uu____1545 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___119_1544.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___119_1544.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1545
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___120_1553 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.ty =
                  (uu___120_1553.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___120_1553.FStar_Syntax_Syntax.p)
              }), n1)
         in
      aux (Prims.parse_int "0") p
  
let push_subst_lcomp s lopt =
  match lopt with
  | None |Some (FStar_Util.Inr _) -> lopt
  | Some (FStar_Util.Inl l) ->
      let uu____1597 =
        let uu____1600 =
          let uu___121_1601 = l  in
          let uu____1602 =
            FStar_List.map (subst_univ (Prims.fst s))
              l.FStar_Syntax_Syntax.lcomp_univs
             in
          let uu____1606 = subst_args' s l.FStar_Syntax_Syntax.lcomp_indices
             in
          let uu____1612 = subst' s l.FStar_Syntax_Syntax.lcomp_res_typ  in
          {
            FStar_Syntax_Syntax.lcomp_name =
              (uu___121_1601.FStar_Syntax_Syntax.lcomp_name);
            FStar_Syntax_Syntax.lcomp_univs = uu____1602;
            FStar_Syntax_Syntax.lcomp_indices = uu____1606;
            FStar_Syntax_Syntax.lcomp_res_typ = uu____1612;
            FStar_Syntax_Syntax.lcomp_cflags =
              (uu___121_1601.FStar_Syntax_Syntax.lcomp_cflags);
            FStar_Syntax_Syntax.lcomp_as_comp =
              (fun uu____1615  ->
                 let uu____1616 = l.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                 subst_comp' s uu____1616)
          }  in
        FStar_Util.Inl uu____1600  in
      Some uu____1597
  
let push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____1639 = mk_range t.FStar_Syntax_Syntax.pos s  in
        (FStar_Syntax_Syntax.mk t') None uu____1639  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1650 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant _
        |FStar_Syntax_Syntax.Tm_fvar _
         |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_uvar _ ->
          tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_name _ ->
          subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 = FStar_List.map (subst_univ (Prims.fst s)) us  in
          let uu____1692 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____1692 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1713 =
            let uu____1714 =
              let uu____1724 = subst' s t0  in
              let uu____1727 = (subst_args' s) args  in
              (uu____1724, uu____1727)  in
            FStar_Syntax_Syntax.Tm_app uu____1714  in
          mk1 uu____1713
      | FStar_Syntax_Syntax.Tm_ascribed (t0,FStar_Util.Inl t1,lopt) ->
          let uu____1761 =
            let uu____1762 =
              let uu____1775 = subst' s t0  in
              let uu____1778 =
                let uu____1785 = subst' s t1  in FStar_Util.Inl uu____1785
                 in
              (uu____1775, uu____1778, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____1762  in
          mk1 uu____1761
      | FStar_Syntax_Syntax.Tm_ascribed (t0,FStar_Util.Inr c,lopt) ->
          let uu____1822 =
            let uu____1823 =
              let uu____1836 = subst' s t0  in
              let uu____1839 =
                let uu____1846 = subst_comp' s c  in
                FStar_Util.Inr uu____1846  in
              (uu____1836, uu____1839, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____1823  in
          mk1 uu____1822
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____1899 =
            let uu____1900 =
              let uu____1915 = subst_binders' s bs  in
              let uu____1919 = subst' s' body  in
              let uu____1922 = push_subst_lcomp s' lopt  in
              (uu____1915, uu____1919, uu____1922)  in
            FStar_Syntax_Syntax.Tm_abs uu____1900  in
          mk1 uu____1899
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____1959 =
            let uu____1960 =
              let uu____1968 = subst_binders' s bs  in
              let uu____1972 =
                let uu____1975 = shift_subst' n1 s  in
                subst_comp' uu____1975 comp  in
              (uu____1968, uu____1972)  in
            FStar_Syntax_Syntax.Tm_arrow uu____1960  in
          mk1 uu____1959
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___122_1996 = x  in
            let uu____1997 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_1996.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_1996.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1997
            }  in
          let phi1 =
            let uu____2003 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____2003 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2086  ->
                    match uu____2086 with
                    | (pat,wopt,branch) ->
                        let uu____2122 = subst_pat' s pat  in
                        (match uu____2122 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | None  -> None
                               | Some w ->
                                   let uu____2157 = subst' s1 w  in
                                   Some uu____2157
                                in
                             let branch1 = subst' s1 branch  in
                             (pat1, wopt1, branch1))))
             in
          mk1 (FStar_Syntax_Syntax.Tm_match (t01, pats1))
      | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),body) ->
          let n1 = FStar_List.length lbs  in
          let sn = shift_subst' n1 s  in
          let body1 = subst' sn body  in
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let lbt = subst' s lb.FStar_Syntax_Syntax.lbtyp  in
                    let lbd =
                      let uu____2217 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____2217
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___123_2227 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___123_2227.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___123_2227.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___124_2229 = fv  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___125_2230 =
                                    fv.FStar_Syntax_Syntax.fv_name  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___125_2230.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___125_2230.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___124_2229.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___124_2229.FStar_Syntax_Syntax.fv_qual)
                             })
                       in
                    let uu___126_2245 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___126_2245.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___126_2245.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2264 =
            let uu____2265 =
              let uu____2270 = subst' s t0  in
              let uu____2273 =
                let uu____2274 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____2274  in
              (uu____2270, uu____2273)  in
            FStar_Syntax_Syntax.Tm_meta uu____2265  in
          mk1 uu____2264
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2316 =
            let uu____2317 =
              let uu____2322 = subst' s t0  in
              let uu____2325 =
                let uu____2326 =
                  let uu____2331 = subst' s t1  in (m, uu____2331)  in
                FStar_Syntax_Syntax.Meta_monadic uu____2326  in
              (uu____2322, uu____2325)  in
            FStar_Syntax_Syntax.Tm_meta uu____2317  in
          mk1 uu____2316
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2350 =
            let uu____2351 =
              let uu____2356 = subst' s t0  in
              let uu____2359 =
                let uu____2360 =
                  let uu____2366 = subst' s t1  in (m1, m2, uu____2366)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2360  in
              (uu____2356, uu____2359)  in
            FStar_Syntax_Syntax.Tm_meta uu____2351  in
          mk1 uu____2350
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2379 =
            let uu____2380 = let uu____2385 = subst' s t1  in (uu____2385, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____2380  in
          mk1 uu____2379
  
let rec compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2,s),memo) ->
        let t' = let uu____2448 = push_subst s t2  in compress uu____2448  in
        (FStar_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2455 ->
        let t' = force_uvar t1  in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2459 -> compress t'
         | uu____2480 -> t')
  
let subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst' ([s], None) t 
let set_use_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun t  ->
      subst'
        ([],
          (Some
             (let uu___127_2504 = r  in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___127_2504.FStar_Range.use_range)
              }))) t
  
let subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t 
let subst_args s args =
  FStar_List.map
    (fun uu____2545  ->
       match uu____2545 with
       | (x,a) -> let uu____2552 = subst s x  in (uu____2552, a)) args
  
let subst_lcomp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun s  ->
    fun lc  ->
      let uu___128_2561 = lc  in
      let uu____2562 =
        FStar_List.map (subst_univ [s]) lc.FStar_Syntax_Syntax.lcomp_univs
         in
      let uu____2565 = subst_args s lc.FStar_Syntax_Syntax.lcomp_indices  in
      let uu____2571 = subst s lc.FStar_Syntax_Syntax.lcomp_res_typ  in
      {
        FStar_Syntax_Syntax.lcomp_name =
          (uu___128_2561.FStar_Syntax_Syntax.lcomp_name);
        FStar_Syntax_Syntax.lcomp_univs = uu____2562;
        FStar_Syntax_Syntax.lcomp_indices = uu____2565;
        FStar_Syntax_Syntax.lcomp_res_typ = uu____2571;
        FStar_Syntax_Syntax.lcomp_cflags =
          (uu___128_2561.FStar_Syntax_Syntax.lcomp_cflags);
        FStar_Syntax_Syntax.lcomp_as_comp =
          (fun uu____2574  ->
             let uu____2575 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
             subst_comp s uu____2575)
      }
  
let closing_subst bs =
  let uu____2590 =
    FStar_List.fold_right
      (fun uu____2599  ->
         fun uu____2600  ->
           match (uu____2599, uu____2600) with
           | ((x,uu____2615),(subst1,n1)) ->
               (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                 (n1 + (Prims.parse_int "1")))) bs
      ([], (Prims.parse_int "0"))
     in
  FStar_All.pipe_right uu____2590 Prims.fst 
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___129_2695 = FStar_Syntax_Syntax.freshen_bv x  in
          let uu____2696 = subst o x.FStar_Syntax_Syntax.sort  in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___129_2695.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___129_2695.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2696
          }  in
        let o1 =
          let uu____2701 = shift_subst (Prims.parse_int "1") o  in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2701
           in
        let uu____2703 = aux bs' o1  in
        (match uu____2703 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2))
     in
  aux bs [] 
let open_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  = fun bs  -> let uu____2735 = open_binders' bs  in Prims.fst uu____2735 
let open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
      let uu____2755 = open_binders' bs  in
      match uu____2755 with
      | (bs',opening) ->
          let uu____2775 = subst opening t  in (bs', uu____2775, opening)
  
let open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2788 = open_term' bs t  in
      match uu____2788 with | (b,t1,uu____2796) -> (b, t1)
  
let open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2805 = open_binders' bs  in
      match uu____2805 with
      | (bs',opening) ->
          let uu____2824 = subst_comp opening t  in (bs', uu____2824)
  
let open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec aux_disj sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj uu____2861 -> failwith "impossible"
      | FStar_Syntax_Syntax.Pat_constant uu____2867 -> p1
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu___130_2880 = p1  in
          let uu____2883 =
            let uu____2884 =
              let uu____2892 =
                FStar_All.pipe_right pats
                  (FStar_List.map
                     (fun uu____2916  ->
                        match uu____2916 with
                        | (p2,b) ->
                            let uu____2931 = aux_disj sub1 renaming p2  in
                            (uu____2931, b)))
                 in
              (fv, uu____2892)  in
            FStar_Syntax_Syntax.Pat_cons uu____2884  in
          {
            FStar_Syntax_Syntax.v = uu____2883;
            FStar_Syntax_Syntax.ty = (uu___130_2880.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___130_2880.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_var x ->
          let yopt =
            FStar_Util.find_map renaming
              (fun uu___106_2946  ->
                 match uu___106_2946 with
                 | (x',y) when
                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       (x'.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                     -> Some y
                 | uu____2952 -> None)
             in
          let y =
            match yopt with
            | None  ->
                let uu___131_2956 = FStar_Syntax_Syntax.freshen_bv x  in
                let uu____2957 = subst sub1 x.FStar_Syntax_Syntax.sort  in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___131_2956.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___131_2956.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu____2957
                }
            | Some y -> y  in
          let uu___132_2961 = p1  in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var y);
            FStar_Syntax_Syntax.ty = (uu___132_2961.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___132_2961.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___133_2966 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____2967 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_2966.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_2966.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2967
            }  in
          let uu___134_2970 = p1  in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
            FStar_Syntax_Syntax.ty = (uu___134_2970.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___134_2970.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___135_2980 = x  in
            let uu____2981 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___135_2980.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___135_2980.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2981
            }  in
          let t01 = subst sub1 t0  in
          let uu___136_2985 = p1  in
          {
            FStar_Syntax_Syntax.v =
              (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
            FStar_Syntax_Syntax.ty = (uu___136_2985.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___136_2985.FStar_Syntax_Syntax.p)
          }
       in
    let rec aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj [] ->
          failwith "Impossible: empty disjunction"
      | FStar_Syntax_Syntax.Pat_constant uu____3039 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_disj (p2::ps) ->
          let uu____3055 = aux sub1 renaming p2  in
          (match uu____3055 with
           | (p3,sub2,renaming1) ->
               let ps1 = FStar_List.map (aux_disj sub2 renaming1) ps  in
               ((let uu___137_3103 = p3  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                   FStar_Syntax_Syntax.ty =
                     (uu___137_3103.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___137_3103.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3120 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3166  ->
                    fun uu____3167  ->
                      match (uu____3166, uu____3167) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____3255 = aux sub2 renaming1 p2  in
                          (match uu____3255 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming))
             in
          (match uu____3120 with
           | (pats1,sub2,renaming1) ->
               ((let uu___138_3356 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___138_3356.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___138_3356.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___139_3370 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3371 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___139_3370.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___139_3370.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3371
            }  in
          let sub2 =
            let uu____3376 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3376
             in
          ((let uu___140_3384 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___140_3384.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___140_3384.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___141_3391 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3392 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___141_3391.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___141_3391.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3392
            }  in
          let sub2 =
            let uu____3397 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3397
             in
          ((let uu___142_3405 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___142_3405.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___142_3405.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___143_3417 = x  in
            let uu____3418 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___143_3417.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___143_3417.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3418
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___144_3428 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___144_3428.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___144_3428.FStar_Syntax_Syntax.p)
            }), sub1, renaming)
       in
    let uu____3431 = aux [] [] p  in
    match uu____3431 with | (p1,sub1,uu____3447) -> (p1, sub1)
  
let open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3465  ->
    match uu____3465 with
    | (p,wopt,e) ->
        let uu____3483 = open_pat p  in
        (match uu____3483 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3498 = subst opening w  in Some uu____3498
                in
             let e1 = subst opening e  in (p1, wopt1, e1))
  
let close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____3507 = closing_subst bs  in subst uu____3507 t
  
let close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____3515 = closing_subst bs  in subst_comp uu____3515 c
  
let close_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___145_3548 = x  in
            let uu____3549 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___145_3548.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___145_3548.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3549
            }  in
          let s' =
            let uu____3554 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3554
             in
          let uu____3556 = aux s' tl1  in (x1, imp) :: uu____3556
       in
    aux [] bs
  
let close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      let uu___146_3570 = lc  in
      let uu____3571 = subst_args s lc.FStar_Syntax_Syntax.lcomp_indices  in
      let uu____3577 = subst s lc.FStar_Syntax_Syntax.lcomp_res_typ  in
      {
        FStar_Syntax_Syntax.lcomp_name =
          (uu___146_3570.FStar_Syntax_Syntax.lcomp_name);
        FStar_Syntax_Syntax.lcomp_univs =
          (uu___146_3570.FStar_Syntax_Syntax.lcomp_univs);
        FStar_Syntax_Syntax.lcomp_indices = uu____3571;
        FStar_Syntax_Syntax.lcomp_res_typ = uu____3577;
        FStar_Syntax_Syntax.lcomp_cflags =
          (uu___146_3570.FStar_Syntax_Syntax.lcomp_cflags);
        FStar_Syntax_Syntax.lcomp_as_comp =
          (fun uu____3580  ->
             let uu____3581 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
             subst_comp s uu____3581)
      }
  
let close_pat :
  (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.withinfo_t ->
    ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt
      Prims.list)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj [] ->
          failwith "Impossible: empty disjunction"
      | FStar_Syntax_Syntax.Pat_constant uu____3624 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_disj (p2::ps) ->
          let uu____3637 = aux sub1 p2  in
          (match uu____3637 with
           | (p3,sub2) ->
               let ps1 =
                 FStar_List.map
                   (fun p4  ->
                      let uu____3667 = aux sub2 p4  in Prims.fst uu____3667)
                   ps
                  in
               ((let uu___147_3679 = p3  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                   FStar_Syntax_Syntax.ty =
                     (uu___147_3679.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___147_3679.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3696 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3730  ->
                    fun uu____3731  ->
                      match (uu____3730, uu____3731) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3796 = aux sub2 p2  in
                          (match uu____3796 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____3696 with
           | (pats1,sub2) ->
               ((let uu___148_3862 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___148_3862.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___148_3862.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___149_3876 = x  in
            let uu____3877 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___149_3876.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___149_3876.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3877
            }  in
          let sub2 =
            let uu____3882 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3882
             in
          ((let uu___150_3887 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.ty = (uu___150_3887.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___150_3887.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___151_3892 = x  in
            let uu____3893 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___151_3892.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___151_3892.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3893
            }  in
          let sub2 =
            let uu____3898 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3898
             in
          ((let uu___152_3903 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.ty = (uu___152_3903.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___152_3903.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___153_3913 = x  in
            let uu____3914 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___153_3913.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___153_3913.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3914
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___154_3921 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___154_3921.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___154_3921.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3926  ->
    match uu____3926 with
    | (p,wopt,e) ->
        let uu____3944 = close_pat p  in
        (match uu____3944 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3968 = subst closing w  in Some uu____3968
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    let uu____3984 =
      let uu____3989 =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (Some (u.FStar_Ident.idRange))
                     in
                  ((FStar_Syntax_Syntax.UN
                      ((n1 - i), (FStar_Syntax_Syntax.U_name u'))), u')))
         in
      FStar_All.pipe_right uu____3989 FStar_List.unzip  in
    match uu____3984 with | (s,us') -> (s, us')
  
let open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
      let uu____4030 = univ_var_opening us  in
      match uu____4030 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____4055 = univ_var_opening us  in
      match uu____4055 with
      | (s,us') -> let uu____4068 = subst_comp s c  in (us', uu____4068)
  
let univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
  
let close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun us  ->
    fun t  -> let uu____4087 = univ_var_closing us  in subst uu____4087 t
  
let close_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun us  ->
    fun c  ->
      let uu____4095 = univ_var_closing us  in subst_comp uu____4095 c
  
let open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____4108 = FStar_Syntax_Syntax.is_top_level lbs  in
      if uu____4108
      then (lbs, t)
      else
        (let uu____4114 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____4126  ->
                  match uu____4126 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____4145 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                        FStar_Syntax_Syntax.freshen_bv uu____4145  in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___155_4148 = lb  in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___155_4148.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___155_4148.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___155_4148.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___155_4148.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], [])
            in
         match uu____4114 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____4166 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____4178  ->
                                match uu____4178 with
                                | (i,us,out) ->
                                    let u1 =
                                      FStar_Syntax_Syntax.new_univ_name None
                                       in
                                    ((i + (Prims.parse_int "1")), (u1 :: us),
                                      ((FStar_Syntax_Syntax.UN
                                          (i,
                                            (FStar_Syntax_Syntax.U_name u1)))
                                      :: out)))
                           lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, [], let_rec_opening)
                          in
                       match uu____4166 with
                       | (uu____4201,us,u_let_rec_opening) ->
                           let uu___156_4208 = lb  in
                           let uu____4209 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___156_4208.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___156_4208.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___156_4208.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4209
                           }))
                in
             let t1 = subst let_rec_opening t  in (lbs2, t1))
  
let close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____4225 = FStar_Syntax_Syntax.is_top_level lbs  in
      if uu____4225
      then (lbs, t)
      else
        (let uu____4231 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____4239  ->
                  match uu____4239 with
                  | (i,out) ->
                      let uu____4250 =
                        let uu____4252 =
                          let uu____4253 =
                            let uu____4256 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                               in
                            (uu____4256, i)  in
                          FStar_Syntax_Syntax.NM uu____4253  in
                        uu____4252 :: out  in
                      ((i + (Prims.parse_int "1")), uu____4250)) lbs
             ((Prims.parse_int "0"), [])
            in
         match uu____4231 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____4271 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____4279  ->
                                match uu____4279 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing)
                          in
                       match uu____4271 with
                       | (uu____4292,u_let_rec_closing) ->
                           let uu___157_4296 = lb  in
                           let uu____4297 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___157_4296.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___157_4296.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___157_4296.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___157_4296.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4297
                           }))
                in
             let t1 = subst let_rec_closing t  in (lbs1, t1))
  
let close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____4307  ->
      match uu____4307 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____4325  ->
                   match uu____4325 with
                   | (x,uu____4329) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____4340  ->
      match uu____4340 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____4358 = subst s t  in (us', uu____4358)
  
let opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____4373  ->
              match uu____4373 with
              | (x,uu____4377) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
let open_sub_eff :
  FStar_Syntax_Syntax.sub_eff ->
    (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.binders *
      FStar_Syntax_Syntax.sub_eff)
  =
  fun se  ->
    let uu____4387 = univ_var_opening se.FStar_Syntax_Syntax.sub_eff_univs
       in
    match uu____4387 with
    | (univ_sub,univ_names) ->
        let binders =
          subst_binders univ_sub se.FStar_Syntax_Syntax.sub_eff_binders  in
        let uu____4402 = open_binders' binders  in
        (match uu____4402 with
         | (binders1,binders_sub) ->
             let sub1 =
               let uu____4424 =
                 shift_subst (FStar_List.length binders_sub) univ_sub  in
               FStar_List.append uu____4424 binders_sub  in
             let sub_ts = ([sub1], None)  in
             let se1 =
               let uu____4441 =
                 subst_comp_typ' sub_ts se.FStar_Syntax_Syntax.sub_eff_source
                  in
               let uu____4442 =
                 subst_comp_typ' sub_ts se.FStar_Syntax_Syntax.sub_eff_target
                  in
               let uu____4443 =
                 FStar_Util.map_opt se.FStar_Syntax_Syntax.sub_eff_lift_wp
                   (subst sub1)
                  in
               let uu____4445 =
                 FStar_Util.map_opt se.FStar_Syntax_Syntax.sub_eff_lift
                   (subst sub1)
                  in
               {
                 FStar_Syntax_Syntax.sub_eff_univs = univ_names;
                 FStar_Syntax_Syntax.sub_eff_binders = binders1;
                 FStar_Syntax_Syntax.sub_eff_source = uu____4441;
                 FStar_Syntax_Syntax.sub_eff_target = uu____4442;
                 FStar_Syntax_Syntax.sub_eff_lift_wp = uu____4443;
                 FStar_Syntax_Syntax.sub_eff_lift = uu____4445
               }  in
             (univ_names, binders1, se1))
  
let close_sub_eff :
  FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff =
  fun se  ->
    let univ_sub = univ_var_closing se.FStar_Syntax_Syntax.sub_eff_univs  in
    let binders =
      subst_binders univ_sub se.FStar_Syntax_Syntax.sub_eff_binders  in
    let binders_sub = closing_subst binders  in
    let sub1 =
      let uu____4461 = shift_subst (FStar_List.length binders_sub) univ_sub
         in
      FStar_List.append uu____4461 binders_sub  in
    let sub_ts = ([sub1], None)  in
    let uu___158_4477 = se  in
    let uu____4478 = close_binders binders  in
    let uu____4479 =
      subst_comp_typ' sub_ts se.FStar_Syntax_Syntax.sub_eff_source  in
    let uu____4480 =
      subst_comp_typ' sub_ts se.FStar_Syntax_Syntax.sub_eff_target  in
    let uu____4481 =
      FStar_Util.map_opt se.FStar_Syntax_Syntax.sub_eff_lift_wp (subst sub1)
       in
    let uu____4483 =
      FStar_Util.map_opt se.FStar_Syntax_Syntax.sub_eff_lift (subst sub1)  in
    {
      FStar_Syntax_Syntax.sub_eff_univs =
        (uu___158_4477.FStar_Syntax_Syntax.sub_eff_univs);
      FStar_Syntax_Syntax.sub_eff_binders = uu____4478;
      FStar_Syntax_Syntax.sub_eff_source = uu____4479;
      FStar_Syntax_Syntax.sub_eff_target = uu____4480;
      FStar_Syntax_Syntax.sub_eff_lift_wp = uu____4481;
      FStar_Syntax_Syntax.sub_eff_lift = uu____4483
    }
  