open Prims
let subst_to_string s =
  let _0_76 =
    FStar_All.pipe_right s
      (FStar_List.map
         (fun uu____21  ->
            match uu____21 with
            | (b,uu____25) ->
                (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
     in
  FStar_All.pipe_right _0_76 (FStar_String.concat ", ") 
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
  let _0_77 = apply_until_some f s  in
  FStar_All.pipe_right _0_77 (map_some_curry g t) 
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
      | uu____309 ->
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
    if uu____384
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
        let uu____443 = FStar_ST.read m  in
        (match uu____443 with
         | None  ->
             (match f with
              | FStar_Util.Inr c ->
                  let t' = force_delayed_thunk (c ())  in
                  (FStar_ST.write m (Some t'); t')
              | uu____487 -> t)
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
        (fun uu___101_542  ->
           match uu___101_542 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               Some
                 (FStar_Syntax_Syntax.bv_to_name
                    (let _0_78 = FStar_Syntax_Syntax.range_of_bv a  in
                     FStar_Syntax_Syntax.set_range_of_bv x _0_78))
           | uu____546 -> None)
  
let subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term Prims.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___102_556  ->
           match uu___102_556 with
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
        (fun uu___103_579  ->
           match uu___103_579 with
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
        (fun uu___104_593  ->
           match uu___104_593 with
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
          apply_until_some_then_map (subst_univ_bv x) s subst_univ u
      | FStar_Syntax_Syntax.U_name x ->
          apply_until_some_then_map (subst_univ_nm x) s subst_univ u
      | FStar_Syntax_Syntax.U_zero 
        |FStar_Syntax_Syntax.U_unknown |FStar_Syntax_Syntax.U_unif _ -> u
      | FStar_Syntax_Syntax.U_succ u ->
          FStar_Syntax_Syntax.U_succ (subst_univ s u)
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
            FStar_Syntax_Syntax.Tm_bvar
              (FStar_Syntax_Syntax.set_range_of_bv bv r)
        | FStar_Syntax_Syntax.Tm_name bv ->
            FStar_Syntax_Syntax.Tm_name
              (FStar_Syntax_Syntax.set_range_of_bv bv r)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            let v =
              let uu___108_656 = fv.FStar_Syntax_Syntax.fv_name  in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r);
                FStar_Syntax_Syntax.ty =
                  (uu___108_656.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___108_656.FStar_Syntax_Syntax.p)
              }  in
            let fv =
              let uu___109_672 = fv  in
              {
                FStar_Syntax_Syntax.fv_name = v;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___109_672.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___109_672.FStar_Syntax_Syntax.fv_qual)
              }  in
            FStar_Syntax_Syntax.Tm_fvar fv
        | t' -> t'  in
      let uu___110_674 = t  in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___110_674.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r;
        FStar_Syntax_Syntax.vars = (uu___110_674.FStar_Syntax_Syntax.vars)
      }
  
let tag_lid_with_range l s =
  match Prims.snd s with
  | None  -> l
  | Some r ->
      let _0_79 = FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r
         in
      FStar_Ident.set_lid_range l _0_79
  
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
               (FStar_Util.Inr uu____863,uu____864) ->
               failwith
                 "Impossible: force_delayed_thunk removes lazy delayed nodes"
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a) (Prims.fst s)
                 subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a) (Prims.fst s)
                 subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let _0_80 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               (FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_type (subst_univ (Prims.fst s) u)))
                 None _0_80
           | uu____931 ->
               let _0_81 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t0, s))
                 _0_81)

and subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___105_945  ->
              match uu___105_945 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  FStar_Syntax_Syntax.DECREASES (subst' s a)
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
          let _0_86 =
            tag_lid_with_range t.FStar_Syntax_Syntax.comp_typ_name s  in
          let _0_85 =
            FStar_List.map (subst_univ (Prims.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let _0_84 =
            FStar_List.map
              (fun uu____986  ->
                 match uu____986 with
                 | (t,imp) -> let _0_82 = subst' s t  in (_0_82, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let _0_83 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_typ_name = _0_86;
            FStar_Syntax_Syntax.comp_univs = _0_85;
            FStar_Syntax_Syntax.effect_args = _0_84;
            FStar_Syntax_Syntax.flags = _0_83
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
      | uu____1023 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t,uopt) ->
               let _0_88 = subst' s t  in
               let _0_87 = FStar_Option.map (subst_univ (Prims.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' _0_88 _0_87
           | FStar_Syntax_Syntax.GTotal (t,uopt) ->
               let _0_90 = subst' s t  in
               let _0_89 = FStar_Option.map (subst_univ (Prims.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' _0_90 _0_89
           | FStar_Syntax_Syntax.Comp ct ->
               FStar_Syntax_Syntax.mk_Comp (subst_comp_typ' s ct))

let shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt
  =
  fun n  ->
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
  let _0_91 =
    FStar_All.pipe_right (Prims.fst s) (FStar_List.map (shift_subst n))  in
  (_0_91, (Prims.snd s)) 
let subst_binder' s uu____1120 =
  match uu____1120 with
  | (x,imp) ->
      let _0_93 =
        let uu___112_1125 = x  in
        let _0_92 = subst' s x.FStar_Syntax_Syntax.sort  in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___112_1125.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___112_1125.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = _0_92
        }  in
      (_0_93, imp)
  
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else (let _0_94 = shift_subst' i s  in subst_binder' _0_94 b)))
  
let subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs 
let subst_arg' s uu____1197 =
  match uu____1197 with | (t,imp) -> let _0_95 = subst' s t  in (_0_95, imp) 
let subst_args' s = FStar_List.map (subst_arg' s) 
let subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range Prims.option)
    ->
    (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t -> (FStar_Syntax_Syntax.pat * Prims.int)
  =
  fun s  ->
    fun p  ->
      let rec aux n p =
        match p.FStar_Syntax_Syntax.v with
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
                       (FStar_Syntax_Syntax.Pat_disj (p :: ps));
                     FStar_Syntax_Syntax.ty =
                       (uu___113_1308.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___113_1308.FStar_Syntax_Syntax.p)
                   }), m))
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1321 =
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
                          (fv, (FStar_List.rev pats)));
                     FStar_Syntax_Syntax.ty =
                       (uu___114_1426.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___114_1426.FStar_Syntax_Syntax.p)
                   }), n))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s = shift_subst' n s  in
            let x =
              let uu___115_1442 = x  in
              let _0_96 = subst' s x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___115_1442.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___115_1442.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = _0_96
              }  in
            ((let uu___116_1445 = p  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x);
                FStar_Syntax_Syntax.ty =
                  (uu___116_1445.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___116_1445.FStar_Syntax_Syntax.p)
              }), (n + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s = shift_subst' n s  in
            let x =
              let uu___117_1456 = x  in
              let _0_97 = subst' s x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___117_1456.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___117_1456.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = _0_97
              }  in
            ((let uu___118_1459 = p  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x);
                FStar_Syntax_Syntax.ty =
                  (uu___118_1459.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___118_1459.FStar_Syntax_Syntax.p)
              }), (n + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s = shift_subst' n s  in
            let x =
              let uu___119_1475 = x  in
              let _0_98 = subst' s x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___119_1475.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___119_1475.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = _0_98
              }  in
            let t0 = subst' s t0  in
            ((let uu___120_1481 = p  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x, t0));
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
           (let uu___121_1527 = l  in
            let _0_102 =
              FStar_List.map (subst_univ (Prims.fst s))
                l.FStar_Syntax_Syntax.lcomp_univs
               in
            let _0_101 = subst_args' s l.FStar_Syntax_Syntax.lcomp_indices
               in
            let _0_100 = subst' s l.FStar_Syntax_Syntax.lcomp_res_typ  in
            {
              FStar_Syntax_Syntax.lcomp_name =
                (uu___121_1527.FStar_Syntax_Syntax.lcomp_name);
              FStar_Syntax_Syntax.lcomp_univs = _0_102;
              FStar_Syntax_Syntax.lcomp_indices = _0_101;
              FStar_Syntax_Syntax.lcomp_res_typ = _0_100;
              FStar_Syntax_Syntax.lcomp_cflags =
                (uu___121_1527.FStar_Syntax_Syntax.lcomp_cflags);
              FStar_Syntax_Syntax.lcomp_as_comp =
                ((fun uu____1531  ->
                    let _0_99 = l.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                    subst_comp' s _0_99))
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
        let _0_103 = mk_range t.FStar_Syntax_Syntax.pos s  in
        (FStar_Syntax_Syntax.mk t') None _0_103  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1560 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant _
        |FStar_Syntax_Syntax.Tm_fvar _
         |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_uvar _ ->
          tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_name _ ->
          subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us = FStar_List.map (subst_univ (Prims.fst s)) us  in
          let _0_104 = FStar_Syntax_Syntax.mk_Tm_uinst t' us  in
          tag_with_range _0_104 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          mk
            (FStar_Syntax_Syntax.Tm_app
               (let _0_106 = subst' s t0  in
                let _0_105 = (subst_args' s) args  in (_0_106, _0_105)))
      | FStar_Syntax_Syntax.Tm_ascribed (t0,FStar_Util.Inl t1,lopt) ->
          mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (let _0_108 = subst' s t0  in
                let _0_107 = FStar_Util.Inl (subst' s t1)  in
                (_0_108, _0_107, lopt)))
      | FStar_Syntax_Syntax.Tm_ascribed (t0,FStar_Util.Inr c,lopt) ->
          mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (let _0_110 = subst' s t0  in
                let _0_109 = FStar_Util.Inr (subst_comp' s c)  in
                (_0_110, _0_109, lopt)))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n = FStar_List.length bs  in
          let s' = shift_subst' n s  in
          mk
            (FStar_Syntax_Syntax.Tm_abs
               (let _0_113 = subst_binders' s bs  in
                let _0_112 = subst' s' body  in
                let _0_111 = push_subst_lcomp s' lopt  in
                (_0_113, _0_112, _0_111)))
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n = FStar_List.length bs  in
          mk
            (FStar_Syntax_Syntax.Tm_arrow
               (let _0_116 = subst_binders' s bs  in
                let _0_115 =
                  let _0_114 = shift_subst' n s  in subst_comp' _0_114 comp
                   in
                (_0_116, _0_115)))
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x =
            let uu___122_1777 = x  in
            let _0_117 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_1777.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_1777.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_117
            }  in
          let phi =
            let _0_118 = shift_subst' (Prims.parse_int "1") s  in
            subst' _0_118 phi  in
          mk (FStar_Syntax_Syntax.Tm_refine (x, phi))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t0 = subst' s t0  in
          let pats =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____1863  ->
                    match uu____1863 with
                    | (pat,wopt,branch) ->
                        let uu____1899 = subst_pat' s pat  in
                        (match uu____1899 with
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
                      let uu____1991 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____1991
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___123_2001 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___123_2001.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___123_2001.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___124_2003 = fv  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___125_2004 =
                                    fv.FStar_Syntax_Syntax.fv_name  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___125_2004.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___125_2004.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___124_2003.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___124_2003.FStar_Syntax_Syntax.fv_qual)
                             })
                       in
                    let uu___126_2019 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___126_2019.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___126_2019.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    }))
             in
          mk (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_120 = subst' s t0  in
                let _0_119 =
                  FStar_Syntax_Syntax.Meta_pattern
                    (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
                   in
                (_0_120, _0_119)))
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t)) ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_123 = subst' s t0  in
                let _0_122 =
                  FStar_Syntax_Syntax.Meta_monadic
                    (let _0_121 = subst' s t  in (m, _0_121))
                   in
                (_0_123, _0_122)))
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t)) ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_126 = subst' s t0  in
                let _0_125 =
                  FStar_Syntax_Syntax.Meta_monadic_lift
                    (let _0_124 = subst' s t  in (m1, m2, _0_124))
                   in
                (_0_126, _0_125)))
      | FStar_Syntax_Syntax.Tm_meta (t,m) ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_127 = subst' s t  in (_0_127, m)))
  
let rec compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t = force_delayed_thunk t  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t,s),memo) ->
        let t' = compress (push_subst s t)  in
        (FStar_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2165 ->
        let t' = force_uvar t  in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2169 -> compress t'
         | uu____2190 -> t')
  
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
             (let uu___127_2214 = r  in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___127_2214.FStar_Range.use_range)
              }))) t
  
let subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t 
let subst_args s args =
  FStar_List.map
    (fun uu____2255  ->
       match uu____2255 with
       | (x,a) -> let _0_128 = subst s x  in (_0_128, a)) args
  
let subst_lcomp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun s  ->
    fun lc  ->
      let uu___128_2270 = lc  in
      let _0_132 =
        FStar_List.map (subst_univ [s]) lc.FStar_Syntax_Syntax.lcomp_univs
         in
      let _0_131 = subst_args s lc.FStar_Syntax_Syntax.lcomp_indices  in
      let _0_130 = subst s lc.FStar_Syntax_Syntax.lcomp_res_typ  in
      {
        FStar_Syntax_Syntax.lcomp_name =
          (uu___128_2270.FStar_Syntax_Syntax.lcomp_name);
        FStar_Syntax_Syntax.lcomp_univs = _0_132;
        FStar_Syntax_Syntax.lcomp_indices = _0_131;
        FStar_Syntax_Syntax.lcomp_res_typ = _0_130;
        FStar_Syntax_Syntax.lcomp_cflags =
          (uu___128_2270.FStar_Syntax_Syntax.lcomp_cflags);
        FStar_Syntax_Syntax.lcomp_as_comp =
          (fun uu____2273  ->
             let _0_129 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
             subst_comp s _0_129)
      }
  
let closing_subst bs =
  let _0_133 =
    FStar_List.fold_right
      (fun uu____2297  ->
         fun uu____2298  ->
           match (uu____2297, uu____2298) with
           | ((x,uu____2313),(subst,n)) ->
               (((FStar_Syntax_Syntax.NM (x, n)) :: subst),
                 (n + (Prims.parse_int "1")))) bs ([], (Prims.parse_int "0"))
     in
  FStar_All.pipe_right _0_133 Prims.fst 
let open_binders' bs =
  let rec aux bs o =
    match bs with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___129_2389 = FStar_Syntax_Syntax.freshen_bv x  in
          let _0_134 = subst o x.FStar_Syntax_Syntax.sort  in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___129_2389.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___129_2389.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = _0_134
          }  in
        let o =
          let _0_135 = shift_subst (Prims.parse_int "1") o  in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: _0_135  in
        let uu____2392 = aux bs' o  in
        (match uu____2392 with | (bs',o) -> (((x', imp) :: bs'), o))
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
      let uu____2437 = open_binders' bs  in
      match uu____2437 with
      | (bs',opening) ->
          let _0_136 = subst opening t  in (bs', _0_136, opening)
  
let open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2469 = open_term' bs t  in
      match uu____2469 with | (b,t,uu____2477) -> (b, t)
  
let open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2486 = open_binders' bs  in
      match uu____2486 with
      | (bs',opening) -> let _0_137 = subst_comp opening t  in (bs', _0_137)
  
let open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec aux_disj sub renaming p =
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj uu____2541 -> failwith "impossible"
      | FStar_Syntax_Syntax.Pat_constant uu____2547 -> p
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu___130_2560 = p  in
          let _0_140 =
            FStar_Syntax_Syntax.Pat_cons
              (let _0_139 =
                 FStar_All.pipe_right pats
                   (FStar_List.map
                      (fun uu____2586  ->
                         match uu____2586 with
                         | (p,b) ->
                             let _0_138 = aux_disj sub renaming p  in
                             (_0_138, b)))
                  in
               (fv, _0_139))
             in
          {
            FStar_Syntax_Syntax.v = _0_140;
            FStar_Syntax_Syntax.ty = (uu___130_2560.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___130_2560.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_var x ->
          let yopt =
            FStar_Util.find_map renaming
              (fun uu___106_2608  ->
                 match uu___106_2608 with
                 | (x',y) when
                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       (x'.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                     -> Some y
                 | uu____2614 -> None)
             in
          let y =
            match yopt with
            | None  ->
                let uu___131_2618 = FStar_Syntax_Syntax.freshen_bv x  in
                let _0_141 = subst sub x.FStar_Syntax_Syntax.sort  in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___131_2618.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___131_2618.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = _0_141
                }
            | Some y -> y  in
          let uu___132_2620 = p  in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var y);
            FStar_Syntax_Syntax.ty = (uu___132_2620.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___132_2620.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___133_2625 = FStar_Syntax_Syntax.freshen_bv x  in
            let _0_142 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_2625.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_2625.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_142
            }  in
          let uu___134_2626 = p  in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
            FStar_Syntax_Syntax.ty = (uu___134_2626.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___134_2626.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x =
            let uu___135_2636 = x  in
            let _0_143 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___135_2636.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___135_2636.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_143
            }  in
          let t0 = subst sub t0  in
          let uu___136_2638 = p  in
          {
            FStar_Syntax_Syntax.v =
              (FStar_Syntax_Syntax.Pat_dot_term (x, t0));
            FStar_Syntax_Syntax.ty = (uu___136_2638.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___136_2638.FStar_Syntax_Syntax.p)
          }
       in
    let rec aux sub renaming p =
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj [] ->
          failwith "Impossible: empty disjunction"
      | FStar_Syntax_Syntax.Pat_constant uu____2692 -> (p, sub, renaming)
      | FStar_Syntax_Syntax.Pat_disj (p::ps) ->
          let uu____2708 = aux sub renaming p  in
          (match uu____2708 with
           | (p,sub,renaming) ->
               let ps = FStar_List.map (aux_disj sub renaming) ps  in
               ((let uu___137_2756 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p :: ps));
                   FStar_Syntax_Syntax.ty =
                     (uu___137_2756.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___137_2756.FStar_Syntax_Syntax.p)
                 }), sub, renaming))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____2773 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____2819  ->
                    fun uu____2820  ->
                      match (uu____2819, uu____2820) with
                      | ((pats,sub,renaming),(p,imp)) ->
                          let uu____2908 = aux sub renaming p  in
                          (match uu____2908 with
                           | (p,sub,renaming) ->
                               (((p, imp) :: pats), sub, renaming)))
                 ([], sub, renaming))
             in
          (match uu____2773 with
           | (pats,sub,renaming) ->
               ((let uu___138_3009 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats)));
                   FStar_Syntax_Syntax.ty =
                     (uu___138_3009.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___138_3009.FStar_Syntax_Syntax.p)
                 }), sub, renaming))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___139_3023 = FStar_Syntax_Syntax.freshen_bv x  in
            let _0_144 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___139_3023.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___139_3023.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_144
            }  in
          let sub =
            let _0_145 = shift_subst (Prims.parse_int "1") sub  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: _0_145
             in
          ((let uu___140_3032 = p  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___140_3032.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___140_3032.FStar_Syntax_Syntax.p)
            }), sub, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___141_3039 = FStar_Syntax_Syntax.freshen_bv x  in
            let _0_146 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___141_3039.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___141_3039.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_146
            }  in
          let sub =
            let _0_147 = shift_subst (Prims.parse_int "1") sub  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: _0_147
             in
          ((let uu___142_3048 = p  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___142_3048.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___142_3048.FStar_Syntax_Syntax.p)
            }), sub, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x =
            let uu___143_3060 = x  in
            let _0_148 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___143_3060.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___143_3060.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_148
            }  in
          let t0 = subst sub t0  in
          ((let uu___144_3068 = p  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x, t0));
              FStar_Syntax_Syntax.ty = (uu___144_3068.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___144_3068.FStar_Syntax_Syntax.p)
            }), sub, renaming)
       in
    let uu____3071 = aux [] [] p  in
    match uu____3071 with | (p,sub,uu____3087) -> (p, sub)
  
let open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3105  ->
    match uu____3105 with
    | (p,wopt,e) ->
        let uu____3123 = open_pat p  in
        (match uu____3123 with
         | (p,opening) ->
             let wopt =
               match wopt with
               | None  -> None
               | Some w -> Some (subst opening w)  in
             let e = subst opening e  in (p, wopt, e))
  
let close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun bs  -> fun t  -> let _0_149 = closing_subst bs  in subst _0_149 t 
let close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  -> fun c  -> let _0_150 = closing_subst bs  in subst_comp _0_150 c 
let close_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun bs  ->
    let rec aux s bs =
      match bs with
      | [] -> []
      | (x,imp)::tl ->
          let x =
            let uu___145_3183 = x  in
            let _0_151 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___145_3183.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___145_3183.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_151
            }  in
          let s' =
            let _0_152 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x, (Prims.parse_int "0"))) :: _0_152  in
          let _0_153 = aux s' tl  in (x, imp) :: _0_153
       in
    aux [] bs
  
let close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      let uu___146_3196 = lc  in
      let _0_156 = subst_args s lc.FStar_Syntax_Syntax.lcomp_indices  in
      let _0_155 = subst s lc.FStar_Syntax_Syntax.lcomp_res_typ  in
      {
        FStar_Syntax_Syntax.lcomp_name =
          (uu___146_3196.FStar_Syntax_Syntax.lcomp_name);
        FStar_Syntax_Syntax.lcomp_univs =
          (uu___146_3196.FStar_Syntax_Syntax.lcomp_univs);
        FStar_Syntax_Syntax.lcomp_indices = _0_156;
        FStar_Syntax_Syntax.lcomp_res_typ = _0_155;
        FStar_Syntax_Syntax.lcomp_cflags =
          (uu___146_3196.FStar_Syntax_Syntax.lcomp_cflags);
        FStar_Syntax_Syntax.lcomp_as_comp =
          (fun uu____3197  ->
             let _0_154 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
             subst_comp s _0_154)
      }
  
let close_pat :
  (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.withinfo_t ->
    ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt
      Prims.list)
  =
  fun p  ->
    let rec aux sub p =
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj [] ->
          failwith "Impossible: empty disjunction"
      | FStar_Syntax_Syntax.Pat_constant uu____3240 -> (p, sub)
      | FStar_Syntax_Syntax.Pat_disj (p::ps) ->
          let uu____3253 = aux sub p  in
          (match uu____3253 with
           | (p,sub) ->
               let ps = FStar_List.map (fun p  -> Prims.fst (aux sub p)) ps
                  in
               ((let uu___147_3289 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p :: ps));
                   FStar_Syntax_Syntax.ty =
                     (uu___147_3289.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___147_3289.FStar_Syntax_Syntax.p)
                 }), sub))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3306 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3340  ->
                    fun uu____3341  ->
                      match (uu____3340, uu____3341) with
                      | ((pats,sub),(p,imp)) ->
                          let uu____3406 = aux sub p  in
                          (match uu____3406 with
                           | (p,sub) -> (((p, imp) :: pats), sub))) ([], sub))
             in
          (match uu____3306 with
           | (pats,sub) ->
               ((let uu___148_3472 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats)));
                   FStar_Syntax_Syntax.ty =
                     (uu___148_3472.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___148_3472.FStar_Syntax_Syntax.p)
                 }), sub))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x =
            let uu___149_3486 = x  in
            let _0_157 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___149_3486.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___149_3486.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_157
            }  in
          let sub =
            let _0_158 = shift_subst (Prims.parse_int "1") sub  in
            (FStar_Syntax_Syntax.NM (x, (Prims.parse_int "0"))) :: _0_158  in
          ((let uu___150_3492 = p  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x);
              FStar_Syntax_Syntax.ty = (uu___150_3492.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___150_3492.FStar_Syntax_Syntax.p)
            }), sub)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x =
            let uu___151_3497 = x  in
            let _0_159 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___151_3497.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___151_3497.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_159
            }  in
          let sub =
            let _0_160 = shift_subst (Prims.parse_int "1") sub  in
            (FStar_Syntax_Syntax.NM (x, (Prims.parse_int "0"))) :: _0_160  in
          ((let uu___152_3503 = p  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x);
              FStar_Syntax_Syntax.ty = (uu___152_3503.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___152_3503.FStar_Syntax_Syntax.p)
            }), sub)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x =
            let uu___153_3513 = x  in
            let _0_161 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___153_3513.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___153_3513.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_161
            }  in
          let t0 = subst sub t0  in
          ((let uu___154_3518 = p  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x, t0));
              FStar_Syntax_Syntax.ty = (uu___154_3518.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___154_3518.FStar_Syntax_Syntax.p)
            }), sub)
       in
    aux [] p
  
let close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3523  ->
    match uu____3523 with
    | (p,wopt,e) ->
        let uu____3541 = close_pat p  in
        (match uu____3541 with
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
    let uu____3580 =
      let _0_162 =
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
      FStar_All.pipe_right _0_162 FStar_List.unzip  in
    match uu____3580 with | (s,us') -> (s, us')
  
let open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
      let uu____3622 = univ_var_opening us  in
      match uu____3622 with | (s,us') -> let t = subst s t  in (us', t)
  
let open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____3647 = univ_var_opening us  in
      match uu____3647 with
      | (s,us') -> let _0_163 = subst_comp s c  in (us', _0_163)
  
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
      let uu____3702 = FStar_Syntax_Syntax.is_top_level lbs  in
      if uu____3702
      then (lbs, t)
      else
        (let uu____3708 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3720  ->
                  match uu____3720 with
                  | (i,lbs,out) ->
                      let x =
                        FStar_Syntax_Syntax.freshen_bv
                          (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
                         in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___155_3741 = lb  in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___155_3741.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___155_3741.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___155_3741.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___155_3741.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], [])
            in
         match uu____3708 with
         | (n_let_recs,lbs,let_rec_opening) ->
             let lbs =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3759 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3771  ->
                                match uu____3771 with
                                | (i,us,out) ->
                                    let u =
                                      FStar_Syntax_Syntax.new_univ_name None
                                       in
                                    ((i + (Prims.parse_int "1")), (u :: us),
                                      ((FStar_Syntax_Syntax.UN
                                          (i, (FStar_Syntax_Syntax.U_name u)))
                                      :: out)))
                           lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, [], let_rec_opening)
                          in
                       match uu____3759 with
                       | (uu____3794,us,u_let_rec_opening) ->
                           let uu___156_3801 = lb  in
                           let _0_164 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___156_3801.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___156_3801.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___156_3801.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = _0_164
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
      let uu____3815 = FStar_Syntax_Syntax.is_top_level lbs  in
      if uu____3815
      then (lbs, t)
      else
        (let uu____3821 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3829  ->
                  match uu____3829 with
                  | (i,out) ->
                      let _0_167 =
                        let _0_166 =
                          FStar_Syntax_Syntax.NM
                            (let _0_165 =
                               FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                in
                             (_0_165, i))
                           in
                        _0_166 :: out  in
                      ((i + (Prims.parse_int "1")), _0_167)) lbs
             ((Prims.parse_int "0"), [])
            in
         match uu____3821 with
         | (n_let_recs,let_rec_closing) ->
             let lbs =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3854 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3862  ->
                                match uu____3862 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing)
                          in
                       match uu____3854 with
                       | (uu____3875,u_let_rec_closing) ->
                           let uu___157_3879 = lb  in
                           let _0_168 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___157_3879.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___157_3879.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___157_3879.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___157_3879.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = _0_168
                           }))
                in
             let t = subst let_rec_closing t  in (lbs, t))
  
let close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____3887  ->
      match uu____3887 with
      | (us,t) ->
          let n = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____3905  ->
                   match uu____3905 with
                   | (x,uu____3909) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n - i)))) binders
             in
          let t = subst s t  in (us, t)
  
let close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____3920  ->
      match uu____3920 with
      | (us',t) ->
          let n = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n - i))))
              us
             in
          let _0_169 = subst s t  in (us', _0_169)
  
let opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____3952  ->
              match uu____3952 with
              | (x,uu____3956) -> FStar_Syntax_Syntax.DB ((n - i), x)))
  
let open_sub_eff : FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff
  = fun uu____3959  -> failwith "" 
let close_sub_eff :
  FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff =
  fun uu____3962  -> failwith "" 