open Prims
let subst_to_string s =
  let uu____14 =
    FStar_All.pipe_right s
      (FStar_List.map
         (fun uu____21  ->
            match uu____21 with
            | (b,uu____25) ->
                (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
     in
  FStar_All.pipe_right _0_61 (FStar_String.concat ", ") 
let rec apply_until_some f s =
  match s with
  | [] -> None
  | s0::rest ->
      let uu____59 = f s0  in
      (match uu____59 with
       | None  -> apply_until_some f rest
       | Some st -> Some (rest, st))
  
let map_some_curry f x uu___100_99 =
  match uu___100_99 with | None  -> x | Some (a,b) -> f a b 
let apply_until_some_then_map f s g t =
  let _0_62 = apply_until_some f s  in
  FStar_All.pipe_right _0_62 (map_some_curry g t) 
let compose_subst s1 s2 =
  let s = FStar_List.append (Prims.fst s1) (Prims.fst s2)  in
  let ropt =
    match Prims.snd s2 with
    | Some uu____210 -> Prims.snd s2
    | uu____213 -> Prims.snd s1  in
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
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____340) ->
        let uu____353 = FStar_Unionfind.find uv  in
        (match uu____353 with
         | FStar_Syntax_Syntax.Fixed t' -> force_uvar' t'
         | uu____367 -> t)
    | uu____371 -> t
  
let force_uvar :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t  in
    let uu____384 = FStar_Util.physical_equality t t'  in
    match uu____384 with
    | true  -> t
    | uu____389 -> delay t' ([], (Some (t.FStar_Syntax_Syntax.pos)))
  
let rec force_delayed_thunk :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____443 = FStar_ST.read m  in
        (match uu____443 with
         | None  ->
             (match f with
              | FStar_Util.Inr c ->
                  let t' = force_delayed_thunk (c ())  in
                  (FStar_ST.write m (Some t'); t')
              | uu____497 -> t)
         | Some t' ->
             let t' = force_delayed_thunk t'  in
             (FStar_ST.write m (Some t'); t'))
    | uu____519 -> t
  
let rec compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____526 = FStar_Unionfind.find u'  in
        (match uu____526 with | Some u -> compress_univ u | uu____530 -> u)
    | uu____532 -> u
  
let subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term Prims.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___99_552  ->
           match uu___99_552 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               Some
                 (FStar_Syntax_Syntax.bv_to_name
                    (let _0_63 = FStar_Syntax_Syntax.range_of_bv a  in
                     FStar_Syntax_Syntax.set_range_of_bv x _0_63))
           | uu____546 -> None)
  
let subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term Prims.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___100_569  ->
           match uu___100_569 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               Some
                 (FStar_Syntax_Syntax.bv_to_tm
                    (let uu___107_560 = a  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___107_560.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index = i;
                       FStar_Syntax_Syntax.sort =
                         (uu___107_560.FStar_Syntax_Syntax.sort)
                     }))
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> Some t
           | uu____569 -> None)
  
let subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe Prims.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___101_593  ->
           match uu___101_593 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y -> Some t
           | uu____583 -> None)
  
let subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe Prims.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___102_607  ->
           match uu___102_607 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____597 -> None)
  
let rec subst_univ :
  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun s  ->
    fun u  ->
      let u = compress_univ u  in
      match u with
      | FStar_Syntax_Syntax.U_bvar x ->
          apply_until_some_then_map (subst_univ_bv x) s subst_univ u1
      | FStar_Syntax_Syntax.U_name x ->
          apply_until_some_then_map (subst_univ_nm x) s subst_univ u1
      | FStar_Syntax_Syntax.U_zero 
        |FStar_Syntax_Syntax.U_unknown |FStar_Syntax_Syntax.U_unif _ -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____629 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____629
      | FStar_Syntax_Syntax.U_max us ->
          FStar_Syntax_Syntax.U_max (FStar_List.map (subst_univ s) us)
  
let tag_with_range t s =
  match Prims.snd s with
  | None  -> t
  | Some r ->
      let r = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r  in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____665 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_bvar uu____665
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____667 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_name uu____667
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            let v =
              let uu___108_656 = fv.FStar_Syntax_Syntax.fv_name  in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.ty =
                  (uu___108_656.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___108_656.FStar_Syntax_Syntax.p)
              }  in
            let fv =
              let uu___109_672 = fv  in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___107_691.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___109_672.FStar_Syntax_Syntax.fv_qual)
              }  in
            FStar_Syntax_Syntax.Tm_fvar fv
        | t' -> t'  in
      let uu___110_674 = t  in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___108_693.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___108_693.FStar_Syntax_Syntax.vars)
      }
  
let tag_lid_with_range l s =
  match Prims.snd s with
  | None  -> l
  | Some r ->
      let _0_64 = FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r
         in
      FStar_Ident.set_lid_range l _0_64
  
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
      let subst_tail tl = subst' (tl, (Prims.snd s))  in
      match s with
      | ([],None )|([]::[],None ) -> t
      | uu____782 ->
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
               let _0_65 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               (FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_type (subst_univ (Prims.fst s) u)))
                 None _0_65
           | uu____931 ->
               let _0_66 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t0, s))
                 _0_66)

and subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___103_972  ->
              match uu___103_972 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____976 = subst' s a in
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
      | uu____966 ->
          let uu___111_972 = t  in
          let _0_72 =
            FStar_List.map (subst_univ (Prims.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let _0_71 = tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s
             in
          let _0_70 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let _0_69 =
            FStar_List.map
              (fun uu____986  ->
                 match uu____986 with
                 | (t,imp) -> let _0_67 = subst' s t  in (_0_67, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let _0_68 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1003;
            FStar_Syntax_Syntax.effect_name = uu____1007;
            FStar_Syntax_Syntax.result_typ = uu____1010;
            FStar_Syntax_Syntax.effect_args = uu____1013;
            FStar_Syntax_Syntax.flags = uu____1047
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
      | uu____1069 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t,uopt) ->
               let _0_74 = subst' s t  in
               let _0_73 = FStar_Option.map (subst_univ (Prims.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' _0_74 _0_73
           | FStar_Syntax_Syntax.GTotal (t,uopt) ->
               let _0_76 = subst' s t  in
               let _0_75 = FStar_Option.map (subst_univ (Prims.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' _0_76 _0_75
           | FStar_Syntax_Syntax.Comp ct ->
               FStar_Syntax_Syntax.mk_Comp (subst_comp_typ' s ct))

let shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt
  =
  fun n1  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n))
      | FStar_Syntax_Syntax.NT uu____1068 -> s
  
let shift_subst :
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n  -> fun s  -> FStar_List.map (shift n) s 
let shift_subst' n s =
  let _0_77 =
    FStar_All.pipe_right (Prims.fst s) (FStar_List.map (shift_subst n))  in
  (_0_77, (Prims.snd s)) 
let subst_binder' s uu____1120 =
  match uu____1120 with
  | (x,imp) ->
      let _0_79 =
        let uu___112_1125 = x  in
        let _0_78 = subst' s x.FStar_Syntax_Syntax.sort  in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___110_1181.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___112_1125.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = _0_78
        }  in
      (_0_79, imp)
  
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            match i = (Prims.parse_int "0") with
            | true  -> subst_binder' s b
            | uu____1163 ->
                let _0_80 = shift_subst' i s  in subst_binder' _0_80 b))
  
let subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs 
let subst_arg' s uu____1197 =
  match uu____1197 with | (t,imp) -> let _0_81 = subst' s t  in (_0_81, imp) 
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
        | FStar_Syntax_Syntax.Pat_constant uu____1280 -> (p, n)
        | FStar_Syntax_Syntax.Pat_disj (p::ps) ->
            let uu____1292 = aux n p  in
            (match uu____1292 with
             | (p,m) ->
                 let ps = FStar_List.map (fun p  -> Prims.fst (aux n p)) ps
                    in
                 ((let uu___113_1308 = p  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                     FStar_Syntax_Syntax.ty =
                       (uu___111_1374.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___111_1374.FStar_Syntax_Syntax.p)
                   }), m))
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1387 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1346  ->
                      fun uu____1347  ->
                        match (uu____1346, uu____1347) with
                        | ((pats,n),(p,imp)) ->
                            let uu____1394 = aux n p  in
                            (match uu____1394 with
                             | (p,m) -> (((p, imp) :: pats), m))) ([], n))
               in
            (match uu____1321 with
             | (pats,n) ->
                 ((let uu___114_1426 = p  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.ty =
                       (uu___112_1492.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___112_1492.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s = shift_subst' n s  in
            let x =
              let uu___115_1442 = x  in
              let _0_82 = subst' s x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___113_1508.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___115_1442.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = _0_82
              }  in
            ((let uu___116_1445 = p  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.ty =
                  (uu___114_1514.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___114_1514.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s = shift_subst' n s  in
            let x =
              let uu___117_1456 = x  in
              let _0_83 = subst' s x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___115_1525.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___117_1456.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = _0_83
              }  in
            ((let uu___118_1459 = p  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.ty =
                  (uu___116_1531.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___116_1531.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s = shift_subst' n s  in
            let x =
              let uu___119_1475 = x  in
              let _0_84 = subst' s x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___117_1547.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___119_1475.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = _0_84
              }  in
            let t0 = subst' s t0  in
            ((let uu___120_1481 = p  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.ty =
                  (uu___120_1481.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___120_1481.FStar_Syntax_Syntax.p)
              }), n)
         in
      aux (Prims.parse_int "0") p
  
let push_subst_lcomp s lopt =
  match lopt with
  | None |Some (FStar_Util.Inr _) -> lopt
  | Some (FStar_Util.Inl l) ->
      Some
        (FStar_Util.Inl
           (let uu___121_1517 = l  in
            let _0_86 = subst' s l.FStar_Syntax_Syntax.res_typ  in
            {
              FStar_Syntax_Syntax.eff_name =
                (uu___121_1517.FStar_Syntax_Syntax.eff_name);
              FStar_Syntax_Syntax.res_typ = _0_86;
              FStar_Syntax_Syntax.cflags =
                (uu___121_1517.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____1518  ->
                    let _0_85 = l.FStar_Syntax_Syntax.comp ()  in
                    subst_comp' s _0_85))
            }))
  
let push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let mk t' =
        let _0_87 = mk_range t.FStar_Syntax_Syntax.pos s  in
        (FStar_Syntax_Syntax.mk t') None _0_87  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1633 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant _
        |FStar_Syntax_Syntax.Tm_fvar _
         |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_uvar _ ->
          tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_name _ ->
          subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us = FStar_List.map (subst_univ (Prims.fst s)) us  in
          let _0_88 = FStar_Syntax_Syntax.mk_Tm_uinst t' us  in
          tag_with_range _0_88 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          mk
            (FStar_Syntax_Syntax.Tm_app
               (let _0_90 = subst' s t0  in
                let _0_89 = (subst_args' s) args  in (_0_90, _0_89)))
      | FStar_Syntax_Syntax.Tm_ascribed (t0,FStar_Util.Inl t1,lopt) ->
          mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (let _0_92 = subst' s t0  in
                let _0_91 = FStar_Util.Inl (subst' s t1)  in
                (_0_92, _0_91, lopt)))
      | FStar_Syntax_Syntax.Tm_ascribed (t0,FStar_Util.Inr c,lopt) ->
          mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (let _0_94 = subst' s t0  in
                let _0_93 = FStar_Util.Inr (subst_comp' s c)  in
                (_0_94, _0_93, lopt)))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n = FStar_List.length bs  in
          let s' = shift_subst' n s  in
          mk
            (FStar_Syntax_Syntax.Tm_abs
               (let _0_97 = subst_binders' s bs  in
                let _0_96 = subst' s' body  in
                let _0_95 = push_subst_lcomp s' lopt  in
                (_0_97, _0_96, _0_95)))
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n = FStar_List.length bs  in
          mk
            (FStar_Syntax_Syntax.Tm_arrow
               (let _0_100 = subst_binders' s bs  in
                let _0_99 =
                  let _0_98 = shift_subst' n s  in subst_comp' _0_98 comp  in
                (_0_100, _0_99)))
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x =
            let uu___122_1764 = x  in
            let _0_101 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___120_2002.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_1764.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_101
            }  in
          let phi =
            let _0_102 = shift_subst' (Prims.parse_int "1") s  in
            subst' _0_102 phi  in
          mk (FStar_Syntax_Syntax.Tm_refine (x, phi))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t0 = subst' s t0  in
          let pats =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2092  ->
                    match uu____2092 with
                    | (pat,wopt,branch) ->
                        let uu____1886 = subst_pat' s pat  in
                        (match uu____1886 with
                         | (pat,n) ->
                             let s = shift_subst' n s  in
                             let wopt =
                               match wopt with
                               | None  -> None
                               | Some w -> Some (subst' s w)  in
                             let branch = subst' s branch  in
                             (pat, wopt, branch))))
             in
          mk (FStar_Syntax_Syntax.Tm_match (t0, pats))
      | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),body) ->
          let n = FStar_List.length lbs  in
          let sn = shift_subst' n s  in
          let body = subst' sn body  in
          let lbs =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let lbt = subst' s lb.FStar_Syntax_Syntax.lbtyp  in
                    let lbd =
                      let uu____2223 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      match uu____1978 with
                      | true  -> subst' sn lb.FStar_Syntax_Syntax.lbdef
                      | uu____1981 -> subst' s lb.FStar_Syntax_Syntax.lbdef
                       in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___123_1988 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___121_2233.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___121_2233.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___124_1990 = fv  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___125_1991 =
                                    fv.FStar_Syntax_Syntax.fv_name  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___123_2236.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___123_2236.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___122_2235.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___124_1990.FStar_Syntax_Syntax.fv_qual)
                             })
                       in
                    let uu___126_2006 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___124_2251.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___124_2251.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    }))
             in
          mk (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_104 = subst' s t0  in
                let _0_103 =
                  FStar_Syntax_Syntax.Meta_pattern
                    (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
                   in
                (_0_104, _0_103)))
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t)) ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_107 = subst' s t0  in
                let _0_106 =
                  FStar_Syntax_Syntax.Meta_monadic
                    (let _0_105 = subst' s t  in (m, _0_105))
                   in
                (_0_107, _0_106)))
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t)) ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_110 = subst' s t0  in
                let _0_109 =
                  FStar_Syntax_Syntax.Meta_monadic_lift
                    (let _0_108 = subst' s t  in (m1, m2, _0_108))
                   in
                (_0_110, _0_109)))
      | FStar_Syntax_Syntax.Tm_meta (t,m) ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_111 = subst' s t  in (_0_111, m)))
  
let rec compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t = force_delayed_thunk t  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t,s),memo) ->
        let t' = compress (push_subst s t)  in
        (FStar_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2152 ->
        let t' = force_uvar t  in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2156 -> compress t'
         | uu____2177 -> t')
  
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
             (let uu___127_2201 = r  in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___125_2510.FStar_Range.use_range)
              }))) t
  
let subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t 
let closing_subst bs =
  let uu____2538 =
    FStar_List.fold_right
      (fun uu____2238  ->
         fun uu____2239  ->
           match (uu____2238, uu____2239) with
           | ((x,uu____2254),(subst,n)) ->
               (((FStar_Syntax_Syntax.NM (x, n)) :: subst),
                 (n + (Prims.parse_int "1")))) bs ([], (Prims.parse_int "0"))
     in
  FStar_All.pipe_right _0_112 Prims.fst 
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___128_2330 = FStar_Syntax_Syntax.freshen_bv x  in
          let _0_113 = subst o x.FStar_Syntax_Syntax.sort  in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___126_2643.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___128_2330.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = _0_113
          }  in
        let o =
          let _0_114 = shift_subst (Prims.parse_int "1") o  in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: _0_114  in
        let uu____2333 = aux bs' o  in
        (match uu____2333 with | (bs',o) -> (((x', imp) :: bs'), o))
     in
  aux bs [] 
let open_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  = fun bs  -> Prims.fst (open_binders' bs) 
let open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
      let uu____2378 = open_binders' bs  in
      match uu____2378 with
      | (bs',opening) ->
          let _0_115 = subst opening t  in (bs', _0_115, opening)
  
let open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2410 = open_term' bs t  in
      match uu____2410 with | (b,t,uu____2418) -> (b, t)
  
let open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2427 = open_binders' bs  in
      match uu____2427 with
      | (bs',opening) -> let _0_116 = subst_comp opening t  in (bs', _0_116)
  
let open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec aux_disj sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj uu____2809 -> failwith "impossible"
      | FStar_Syntax_Syntax.Pat_constant uu____2815 -> p1
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu___129_2501 = p  in
          let _0_119 =
            FStar_Syntax_Syntax.Pat_cons
              (let _0_118 =
                 FStar_All.pipe_right pats
                   (FStar_List.map
                      (fun uu____2527  ->
                         match uu____2527 with
                         | (p,b) ->
                             let _0_117 = aux_disj sub renaming p  in
                             (_0_117, b)))
                  in
               (fv, _0_118))
             in
          {
            FStar_Syntax_Syntax.v = uu____2831;
            FStar_Syntax_Syntax.ty = (uu___127_2828.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___127_2828.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_var x ->
          let yopt =
            FStar_Util.find_map renaming
              (fun uu___104_2894  ->
                 match uu___104_2894 with
                 | (x',y) when
                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       (x'.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                     -> Some y
                 | uu____2555 -> None)
             in
          let y =
            match yopt with
            | None  ->
                let uu___130_2559 = FStar_Syntax_Syntax.freshen_bv x  in
                let _0_120 = subst sub x.FStar_Syntax_Syntax.sort  in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___128_2904.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___128_2904.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu____2905
                }
            | Some y -> y  in
          let uu___131_2561 = p  in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var y);
            FStar_Syntax_Syntax.ty = (uu___129_2909.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___129_2909.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___132_2566 = FStar_Syntax_Syntax.freshen_bv x  in
            let _0_121 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___130_2914.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___132_2566.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_121
            }  in
          let uu___133_2567 = p  in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
            FStar_Syntax_Syntax.ty = (uu___131_2918.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___131_2918.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x =
            let uu___134_2577 = x  in
            let _0_122 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___132_2928.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___134_2577.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_122
            }  in
          let t0 = subst sub t0  in
          let uu___135_2579 = p  in
          {
            FStar_Syntax_Syntax.v =
              (FStar_Syntax_Syntax.Pat_dot_term (x, t0));
            FStar_Syntax_Syntax.ty = (uu___135_2579.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___135_2579.FStar_Syntax_Syntax.p)
          }
       in
    let rec aux sub renaming p =
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj [] ->
          failwith "Impossible: empty disjunction"
      | FStar_Syntax_Syntax.Pat_constant uu____2633 -> (p, sub, renaming)
      | FStar_Syntax_Syntax.Pat_disj (p::ps) ->
          let uu____2649 = aux sub renaming p  in
          (match uu____2649 with
           | (p,sub,renaming) ->
               let ps = FStar_List.map (aux_disj sub renaming) ps  in
               ((let uu___136_2697 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                   FStar_Syntax_Syntax.ty =
                     (uu___134_3051.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___134_3051.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3068 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____2760  ->
                    fun uu____2761  ->
                      match (uu____2760, uu____2761) with
                      | ((pats,sub,renaming),(p,imp)) ->
                          let uu____2849 = aux sub renaming p  in
                          (match uu____2849 with
                           | (p,sub,renaming) ->
                               (((p, imp) :: pats), sub, renaming)))
                 ([], sub, renaming))
             in
          (match uu____2714 with
           | (pats,sub,renaming) ->
               ((let uu___137_2950 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___135_3304.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___135_3304.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___138_2964 = FStar_Syntax_Syntax.freshen_bv x  in
            let _0_123 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___136_3318.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_2964.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_123
            }  in
          let sub =
            let _0_124 = shift_subst (Prims.parse_int "1") sub  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: _0_124
             in
          ((let uu___139_2973 = p  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___137_3332.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___137_3332.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___140_2980 = FStar_Syntax_Syntax.freshen_bv x  in
            let _0_125 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_3339.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_2980.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_125
            }  in
          let sub =
            let _0_126 = shift_subst (Prims.parse_int "1") sub  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: _0_126
             in
          ((let uu___141_2989 = p  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___139_3353.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___139_3353.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x =
            let uu___142_3001 = x  in
            let _0_127 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_3365.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___142_3001.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_127
            }  in
          let t0 = subst sub t0  in
          ((let uu___143_3009 = p  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x, t0));
              FStar_Syntax_Syntax.ty = (uu___143_3009.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___143_3009.FStar_Syntax_Syntax.p)
            }), sub, renaming)
       in
    let uu____3012 = aux [] [] p  in
    match uu____3012 with | (p,sub,uu____3028) -> (p, sub)
  
let open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3046  ->
    match uu____3046 with
    | (p,wopt,e) ->
        let uu____3064 = open_pat p  in
        (match uu____3064 with
         | (p,opening) ->
             let wopt =
               match wopt with
               | None  -> None
               | Some w -> Some (subst opening w)  in
             let e = subst opening e  in (p, wopt, e))
  
let close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun bs  -> fun t  -> let _0_128 = closing_subst bs  in subst _0_128 t 
let close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  -> fun c  -> let _0_129 = closing_subst bs  in subst_comp _0_129 c 
let close_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl ->
          let x =
            let uu___144_3124 = x  in
            let _0_130 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___142_3496.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___144_3124.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_130
            }  in
          let s' =
            let _0_131 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x, (Prims.parse_int "0"))) :: _0_131  in
          let _0_132 = aux s' tl  in (x, imp) :: _0_132
       in
    aux [] bs
  
let close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      let uu___145_3137 = lc  in
      let _0_134 = subst s lc.FStar_Syntax_Syntax.res_typ  in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___143_3518.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3519;
        FStar_Syntax_Syntax.cflags =
          (uu___143_3518.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3138  ->
             let _0_133 = lc.FStar_Syntax_Syntax.comp ()  in
             subst_comp s _0_133)
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
      | FStar_Syntax_Syntax.Pat_constant uu____3181 -> (p, sub)
      | FStar_Syntax_Syntax.Pat_disj (p::ps) ->
          let uu____3194 = aux sub p  in
          (match uu____3194 with
           | (p,sub) ->
               let ps = FStar_List.map (fun p  -> Prims.fst (aux sub p)) ps
                  in
               ((let uu___146_3230 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                   FStar_Syntax_Syntax.ty =
                     (uu___144_3621.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___144_3621.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3638 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3281  ->
                    fun uu____3282  ->
                      match (uu____3281, uu____3282) with
                      | ((pats,sub),(p,imp)) ->
                          let uu____3347 = aux sub p  in
                          (match uu____3347 with
                           | (p,sub) -> (((p, imp) :: pats), sub))) ([], sub))
             in
          (match uu____3247 with
           | (pats,sub) ->
               ((let uu___147_3413 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___145_3804.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___145_3804.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x =
            let uu___148_3427 = x  in
            let _0_135 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___146_3818.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___148_3427.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_135
            }  in
          let sub =
            let _0_136 = shift_subst (Prims.parse_int "1") sub  in
            (FStar_Syntax_Syntax.NM (x, (Prims.parse_int "0"))) :: _0_136  in
          ((let uu___149_3433 = p  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.ty = (uu___147_3829.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___147_3829.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x =
            let uu___150_3438 = x  in
            let _0_137 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___148_3834.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___150_3438.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_137
            }  in
          let sub =
            let _0_138 = shift_subst (Prims.parse_int "1") sub  in
            (FStar_Syntax_Syntax.NM (x, (Prims.parse_int "0"))) :: _0_138  in
          ((let uu___151_3444 = p  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.ty = (uu___149_3845.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___149_3845.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x =
            let uu___152_3454 = x  in
            let _0_139 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___150_3855.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___152_3454.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_139
            }  in
          let t0 = subst sub t0  in
          ((let uu___153_3459 = p  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x, t0));
              FStar_Syntax_Syntax.ty = (uu___153_3459.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___153_3459.FStar_Syntax_Syntax.p)
            }), sub)
       in
    aux [] p
  
let close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3464  ->
    match uu____3464 with
    | (p,wopt,e) ->
        let uu____3482 = close_pat p  in
        (match uu____3482 with
         | (p,closing) ->
             let wopt =
               match wopt with
               | None  -> None
               | Some w -> Some (subst closing w)  in
             let e = subst closing e  in (p, wopt, e))
  
let univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n = (FStar_List.length us) - (Prims.parse_int "1")  in
    let uu____3521 =
      let _0_140 =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (Some (u.FStar_Ident.idRange))
                     in
                  ((FStar_Syntax_Syntax.UN
                      ((n - i), (FStar_Syntax_Syntax.U_name u'))), u')))
         in
      FStar_All.pipe_right _0_140 FStar_List.unzip  in
    match uu____3521 with | (s,us') -> (s, us')
  
let open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
      let uu____3563 = univ_var_opening us  in
      match uu____3563 with | (s,us') -> let t = subst s t  in (us', t)
  
let open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____3588 = univ_var_opening us  in
      match uu____3588 with
      | (s,us') -> let _0_141 = subst_comp s c  in (us', _0_141)
  
let close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun us  ->
    fun t  ->
      let n = (FStar_List.length us) - (Prims.parse_int "1")  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n - i))))
         in
      subst s t
  
let close_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun us  ->
    fun c  ->
      let n = (FStar_List.length us) - (Prims.parse_int "1")  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n - i))))
         in
      subst_comp s c
  
let open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____3643 = FStar_Syntax_Syntax.is_top_level lbs  in
      match uu____3643 with
      | true  -> (lbs, t)
      | uu____3648 ->
          let uu____3649 =
            FStar_List.fold_right
              (fun lb  ->
                 fun uu____3661  ->
                   match uu____3661 with
                   | (i,lbs,out) ->
                       let x =
                         FStar_Syntax_Syntax.freshen_bv
                           (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
                          in
                       ((i + (Prims.parse_int "1")),
                         ((let uu___154_3682 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___153_4153.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___153_4153.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___154_3682.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef =
                               (uu___154_3682.FStar_Syntax_Syntax.lbdef)
                           }) :: lbs), ((FStar_Syntax_Syntax.DB (i, x)) ::
                         out))) lbs ((Prims.parse_int "0"), [], [])
             in
          (match uu____3649 with
           | (n_let_recs,lbs,let_rec_opening) ->
               let lbs =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____3700 =
                           FStar_List.fold_right
                             (fun u  ->
                                fun uu____3712  ->
                                  match uu____3712 with
                                  | (i,us,out) ->
                                      let u =
                                        FStar_Syntax_Syntax.new_univ_name
                                          None
                                         in
                                      ((i + (Prims.parse_int "1")), (u ::
                                        us),
                                        ((FStar_Syntax_Syntax.UN
                                            (i,
                                              (FStar_Syntax_Syntax.U_name u)))
                                        :: out)))
                             lb.FStar_Syntax_Syntax.lbunivs
                             (n_let_recs, [], let_rec_opening)
                            in
                         match uu____3700 with
                         | (uu____3735,us,u_let_rec_opening) ->
                             let uu___155_3742 = lb  in
                             let _0_142 =
                               subst u_let_rec_opening
                                 lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___155_3742.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___155_3742.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___155_3742.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = _0_142
                             }))
                  in
               let t = subst let_rec_opening t  in (lbs, t))
  
let close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____3756 = FStar_Syntax_Syntax.is_top_level lbs  in
      match uu____3756 with
      | true  -> (lbs, t)
      | uu____3761 ->
          let uu____3762 =
            FStar_List.fold_right
              (fun lb  ->
                 fun uu____3770  ->
                   match uu____3770 with
                   | (i,out) ->
                       let _0_145 =
                         let _0_144 =
                           FStar_Syntax_Syntax.NM
                             (let _0_143 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              (_0_143, i))
                            in
                         _0_144 :: out  in
                       ((i + (Prims.parse_int "1")), _0_145)) lbs
              ((Prims.parse_int "0"), [])
             in
          (match uu____3762 with
           | (n_let_recs,let_rec_closing) ->
               let lbs =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____3795 =
                           FStar_List.fold_right
                             (fun u  ->
                                fun uu____3803  ->
                                  match uu____3803 with
                                  | (i,out) ->
                                      ((i + (Prims.parse_int "1")),
                                        ((FStar_Syntax_Syntax.UD (u, i)) ::
                                        out))) lb.FStar_Syntax_Syntax.lbunivs
                             (n_let_recs, let_rec_closing)
                            in
                         match uu____3795 with
                         | (uu____3816,u_let_rec_closing) ->
                             let uu___156_3820 = lb  in
                             let _0_146 =
                               subst u_let_rec_closing
                                 lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___156_3820.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___156_3820.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___156_3820.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___156_3820.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = _0_146
                             }))
                  in
               let t = subst let_rec_closing t  in (lbs, t))
  
let close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____4252  ->
      match uu____4252 with
      | (us,t) ->
          let n = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____3846  ->
                   match uu____3846 with
                   | (x,uu____3850) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n - i)))) binders
             in
          let t = subst s t  in (us, t)
  
let close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____4285  ->
      match uu____4285 with
      | (us',t) ->
          let n = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n - i))))
              us
             in
          let _0_147 = subst s t  in (us', _0_147)
  
let opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____3893  ->
              match uu____3893 with
              | (x,uu____3897) -> FStar_Syntax_Syntax.DB ((n - i), x)))
  