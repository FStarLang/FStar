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
  
let map_some_curry f x uu___110_101 =
  match uu___110_101 with | None  -> x | Some (a,b) -> f a b 
let apply_until_some_then_map f s g t =
  let uu____162 = apply_until_some f s  in
  FStar_All.pipe_right uu____162 (map_some_curry g t) 
let compose_subst s1 s2 =
  let s = FStar_List.append (fst s1) (fst s2)  in
  let ropt =
    match snd s2 with | Some uu____217 -> snd s2 | uu____220 -> snd s1  in
  (s, ropt) 
let delay :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range
      option) -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____286 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec force_uvar' :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____306) ->
        let uu____319 = FStar_Syntax_Unionfind.find uv  in
        (match uu____319 with | Some t' -> force_uvar' t' | uu____324 -> t)
    | uu____326 -> t
  
let force_uvar :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t  in
    let uu____339 = FStar_Util.physical_equality t t'  in
    if uu____339
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
        let uu____386 = FStar_ST.read m  in
        (match uu____386 with
         | None  -> t
         | Some t' ->
             let t'1 = force_delayed_thunk t'  in
             (FStar_ST.write m (Some t'1); t'1))
    | uu____415 -> t
  
let rec compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____422 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____422 with | Some u1 -> compress_univ u1 | uu____425 -> u)
    | uu____427 -> u
  
let subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___111_437  ->
           match uu___111_437 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____441 =
                 let uu____442 =
                   let uu____443 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____443  in
                 FStar_Syntax_Syntax.bv_to_name uu____442  in
               Some uu____441
           | uu____444 -> None)
  
let subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___112_454  ->
           match uu___112_454 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____458 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___116_459 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___116_459.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___116_459.FStar_Syntax_Syntax.sort)
                    })
                  in
               Some uu____458
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> Some t
           | uu____468 -> None)
  
let subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___113_478  ->
           match uu___113_478 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y -> Some t
           | uu____482 -> None)
  
let subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___114_492  ->
           match uu___114_492 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____496 -> None)
  
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
      | FStar_Syntax_Syntax.U_zero  -> u1
      | FStar_Syntax_Syntax.U_unknown  -> u1
      | FStar_Syntax_Syntax.U_unif uu____512 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____516 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____516
      | FStar_Syntax_Syntax.U_max us ->
          let uu____519 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____519
  
let tag_with_range t s =
  match snd s with
  | None  -> t
  | Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r  in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____552 = FStar_Syntax_Syntax.set_range_of_bv bv r1  in
            FStar_Syntax_Syntax.Tm_bvar uu____552
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____554 = FStar_Syntax_Syntax.set_range_of_bv bv r1  in
            FStar_Syntax_Syntax.Tm_name uu____554
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            let v1 =
              let uu___117_562 = fv.FStar_Syntax_Syntax.fv_name  in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.ty =
                  (uu___117_562.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___117_562.FStar_Syntax_Syntax.p)
              }  in
            let fv1 =
              let uu___118_578 = fv  in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___118_578.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___118_578.FStar_Syntax_Syntax.fv_qual)
              }  in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t'  in
      let uu___119_580 = t  in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___119_580.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___119_580.FStar_Syntax_Syntax.vars)
      }
  
let tag_lid_with_range l s =
  match snd s with
  | None  -> l
  | Some r ->
      let uu____607 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r  in
      FStar_Ident.set_lid_range l uu____607
  
let mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match snd s with
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
      let subst_tail tl1 = subst' (tl1, (snd s))  in
      match s with
      | ([],None ) -> t
      | ([]::[],None ) -> t
      | uu____689 ->
          let t0 = force_delayed_thunk t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____697 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____700 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____703 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____769 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____770 =
                 let uu____773 =
                   let uu____774 = subst_univ (fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____774  in
                 FStar_Syntax_Syntax.mk uu____773  in
               uu____770 None uu____769
           | uu____786 ->
               let uu____787 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____787)

and subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___115_795  ->
              match uu___115_795 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____799 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____799
              | f -> f))

and subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range
    option) -> FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],None ) -> t
      | ([]::[],None ) -> t
      | uu____819 ->
          let uu___120_825 = t  in
          let uu____826 =
            FStar_List.map (subst_univ (fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____830 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____833 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____836 =
            FStar_List.map
              (fun uu____850  ->
                 match uu____850 with
                 | (t1,imp) ->
                     let uu____865 = subst' s t1  in (uu____865, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____870 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____826;
            FStar_Syntax_Syntax.effect_name = uu____830;
            FStar_Syntax_Syntax.result_typ = uu____833;
            FStar_Syntax_Syntax.effect_args = uu____836;
            FStar_Syntax_Syntax.flags = uu____870
          }

and subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range
    option) ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],None ) -> t
      | ([]::[],None ) -> t
      | uu____892 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____908 = subst' s t1  in
               let uu____909 = FStar_Option.map (subst_univ (fst s)) uopt  in
               FStar_Syntax_Syntax.mk_Total' uu____908 uu____909
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____922 = subst' s t1  in
               let uu____923 = FStar_Option.map (subst_univ (fst s)) uopt  in
               FStar_Syntax_Syntax.mk_GTotal' uu____922 uu____923
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____929 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____929)

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
      | FStar_Syntax_Syntax.NT uu____944 -> s
  
let shift_subst :
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' n1 s =
  let uu____976 =
    FStar_All.pipe_right (fst s) (FStar_List.map (shift_subst n1))  in
  (uu____976, (snd s)) 
let subst_binder' s uu____998 =
  match uu____998 with
  | (x,imp) ->
      let uu____1003 =
        let uu___121_1004 = x  in
        let uu____1005 = subst' s x.FStar_Syntax_Syntax.sort  in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___121_1004.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___121_1004.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1005
        }  in
      (uu____1003, imp)
  
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1046 = shift_subst' i s  in
               subst_binder' uu____1046 b)))
  
let subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs 
let subst_arg' s uu____1080 =
  match uu____1080 with
  | (t,imp) -> let uu____1091 = subst' s t  in (uu____1091, imp) 
let subst_args' s = FStar_List.map (subst_arg' s) 
let subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range option) ->
    (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t -> (FStar_Syntax_Syntax.pat * Prims.int)
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1162 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1177 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1202  ->
                      fun uu____1203  ->
                        match (uu____1202, uu____1203) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1250 = aux n2 p2  in
                            (match uu____1250 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1177 with
             | (pats1,n2) ->
                 ((let uu___122_1282 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.ty =
                       (uu___122_1282.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___122_1282.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___123_1298 = x  in
              let uu____1299 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___123_1298.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___123_1298.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1299
              }  in
            ((let uu___124_1304 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.ty =
                  (uu___124_1304.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___124_1304.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___125_1315 = x  in
              let uu____1316 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___125_1315.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___125_1315.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1316
              }  in
            ((let uu___126_1321 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.ty =
                  (uu___126_1321.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___126_1321.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___127_1337 = x  in
              let uu____1338 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___127_1337.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___127_1337.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1338
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___128_1346 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.ty =
                  (uu___128_1346.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___128_1346.FStar_Syntax_Syntax.p)
              }), n1)
         in
      aux (Prims.parse_int "0") p
  
let push_subst_lcomp :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp option ->
      FStar_Syntax_Syntax.residual_comp option
  =
  fun s  ->
    fun lopt  ->
      match lopt with
      | None  -> None
      | Some rc ->
          let uu____1362 =
            let uu___129_1363 = rc  in
            let uu____1364 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___129_1363.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1364;
              FStar_Syntax_Syntax.residual_flags =
                (uu___129_1363.FStar_Syntax_Syntax.residual_flags)
            }  in
          Some uu____1362
  
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
        let uu____1390 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' None uu____1390  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1397 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____1414 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____1417 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____1422 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____1433 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____1434 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____1435 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 = FStar_List.map (subst_univ (fst s)) us  in
          let uu____1447 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____1447 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1468 =
            let uu____1469 =
              let uu____1479 = subst' s t0  in
              let uu____1482 = subst_args' s args  in
              (uu____1479, uu____1482)  in
            FStar_Syntax_Syntax.Tm_app uu____1469  in
          mk1 uu____1468
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____1554 = subst' s t1  in FStar_Util.Inl uu____1554
            | FStar_Util.Inr c ->
                let uu____1568 = subst_comp' s c  in
                FStar_Util.Inr uu____1568
             in
          let uu____1575 =
            let uu____1576 =
              let uu____1594 = subst' s t0  in
              let uu____1597 =
                let uu____1609 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____1609)  in
              (uu____1594, uu____1597, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____1576  in
          mk1 uu____1575
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____1667 =
            let uu____1668 =
              let uu____1678 = subst_binders' s bs  in
              let uu____1682 = subst' s' body  in
              let uu____1685 = push_subst_lcomp s' lopt  in
              (uu____1678, uu____1682, uu____1685)  in
            FStar_Syntax_Syntax.Tm_abs uu____1668  in
          mk1 uu____1667
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____1709 =
            let uu____1710 =
              let uu____1718 = subst_binders' s bs  in
              let uu____1722 =
                let uu____1725 = shift_subst' n1 s  in
                subst_comp' uu____1725 comp  in
              (uu____1718, uu____1722)  in
            FStar_Syntax_Syntax.Tm_arrow uu____1710  in
          mk1 uu____1709
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___130_1746 = x  in
            let uu____1747 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___130_1746.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___130_1746.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1747
            }  in
          let phi1 =
            let uu____1753 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____1753 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____1836  ->
                    match uu____1836 with
                    | (pat,wopt,branch) ->
                        let uu____1872 = subst_pat' s pat  in
                        (match uu____1872 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | None  -> None
                               | Some w ->
                                   let uu____1907 = subst' s1 w  in
                                   Some uu____1907
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
                      let uu____1967 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____1967
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___131_1977 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___131_1977.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___131_1977.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___132_1979 = fv  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___133_1980 =
                                    fv.FStar_Syntax_Syntax.fv_name  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___133_1980.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___133_1980.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___132_1979.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___132_1979.FStar_Syntax_Syntax.fv_qual)
                             })
                       in
                    let uu___134_1995 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___134_1995.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___134_1995.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2014 =
            let uu____2015 =
              let uu____2020 = subst' s t0  in
              let uu____2023 =
                let uu____2024 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____2024  in
              (uu____2020, uu____2023)  in
            FStar_Syntax_Syntax.Tm_meta uu____2015  in
          mk1 uu____2014
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2066 =
            let uu____2067 =
              let uu____2072 = subst' s t0  in
              let uu____2075 =
                let uu____2076 =
                  let uu____2081 = subst' s t1  in (m, uu____2081)  in
                FStar_Syntax_Syntax.Meta_monadic uu____2076  in
              (uu____2072, uu____2075)  in
            FStar_Syntax_Syntax.Tm_meta uu____2067  in
          mk1 uu____2066
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2100 =
            let uu____2101 =
              let uu____2106 = subst' s t0  in
              let uu____2109 =
                let uu____2110 =
                  let uu____2116 = subst' s t1  in (m1, m2, uu____2116)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2110  in
              (uu____2106, uu____2109)  in
            FStar_Syntax_Syntax.Tm_meta uu____2101  in
          mk1 uu____2100
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2129 =
            let uu____2130 = let uu____2135 = subst' s t1  in (uu____2135, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____2130  in
          mk1 uu____2129
  
let rec compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____2179 = push_subst s t2  in compress uu____2179  in
        (FStar_Syntax_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2186 ->
        let t' = force_uvar t1  in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2190 -> compress t'
         | uu____2205 -> t')
  
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
             (let uu___135_2229 = r  in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___135_2229.FStar_Range.use_range)
              }))) t
  
let subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t 
let closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let uu____2247 =
      FStar_List.fold_right
        (fun uu____2256  ->
           fun uu____2257  ->
             match (uu____2256, uu____2257) with
             | ((x,uu____2272),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____2247 FStar_Pervasives.fst
  
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___136_2352 = FStar_Syntax_Syntax.freshen_bv x  in
          let uu____2353 = subst o x.FStar_Syntax_Syntax.sort  in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___136_2352.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___136_2352.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2353
          }  in
        let o1 =
          let uu____2358 = shift_subst (Prims.parse_int "1") o  in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2358
           in
        let uu____2360 = aux bs' o1  in
        (match uu____2360 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2))
     in
  aux bs [] 
let open_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  = fun bs  -> let uu____2392 = open_binders' bs  in fst uu____2392 
let open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
      let uu____2412 = open_binders' bs  in
      match uu____2412 with
      | (bs',opening) ->
          let uu____2432 = subst opening t  in (bs', uu____2432, opening)
  
let open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2445 = open_term' bs t  in
      match uu____2445 with | (b,t1,uu____2453) -> (b, t1)
  
let open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2462 = open_binders' bs  in
      match uu____2462 with
      | (bs',opening) ->
          let uu____2481 = subst_comp opening t  in (bs', uu____2481)
  
let open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____2532 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____2551 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____2597  ->
                    fun uu____2598  ->
                      match (uu____2597, uu____2598) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____2686 = open_pat_aux sub2 renaming1 p2  in
                          (match uu____2686 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming))
             in
          (match uu____2551 with
           | (pats1,sub2,renaming1) ->
               ((let uu___137_2787 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___137_2787.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___137_2787.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___138_2801 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____2802 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_2801.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_2801.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2802
            }  in
          let sub2 =
            let uu____2807 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____2807
             in
          ((let uu___139_2815 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___139_2815.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___139_2815.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___140_2822 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____2823 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_2822.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_2822.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2823
            }  in
          let sub2 =
            let uu____2828 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____2828
             in
          ((let uu___141_2836 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___141_2836.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___141_2836.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___142_2848 = x  in
            let uu____2849 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___142_2848.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___142_2848.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2849
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___143_2859 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___143_2859.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___143_2859.FStar_Syntax_Syntax.p)
            }), sub1, renaming)
       in
    let uu____2862 = open_pat_aux [] [] p  in
    match uu____2862 with | (p1,sub1,uu____2878) -> (p1, sub1)
  
let open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____2896  ->
    match uu____2896 with
    | (p,wopt,e) ->
        let uu____2914 = open_pat p  in
        (match uu____2914 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____2929 = subst opening w  in Some uu____2929
                in
             let e1 = subst opening e  in (p1, wopt1, e1))
  
let close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____2938 = closing_subst bs  in subst uu____2938 t
  
let close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____2946 = closing_subst bs  in subst_comp uu____2946 c
  
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
            let uu___144_2979 = x  in
            let uu____2980 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___144_2979.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___144_2979.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2980
            }  in
          let s' =
            let uu____2985 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____2985
             in
          let uu____2987 = aux s' tl1  in (x1, imp) :: uu____2987
       in
    aux [] bs
  
let close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      let uu___145_3001 = lc  in
      let uu____3002 = subst s lc.FStar_Syntax_Syntax.res_typ  in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___145_3001.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3002;
        FStar_Syntax_Syntax.cflags =
          (uu___145_3001.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3005  ->
             let uu____3006 = lc.FStar_Syntax_Syntax.comp ()  in
             subst_comp s uu____3006)
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
      | FStar_Syntax_Syntax.Pat_constant uu____3042 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3058 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3092  ->
                    fun uu____3093  ->
                      match (uu____3092, uu____3093) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3158 = aux sub2 p2  in
                          (match uu____3158 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____3058 with
           | (pats1,sub2) ->
               ((let uu___146_3224 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___146_3224.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___146_3224.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___147_3238 = x  in
            let uu____3239 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___147_3238.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___147_3238.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3239
            }  in
          let sub2 =
            let uu____3244 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3244
             in
          ((let uu___148_3249 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.ty = (uu___148_3249.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___148_3249.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___149_3254 = x  in
            let uu____3255 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___149_3254.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___149_3254.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3255
            }  in
          let sub2 =
            let uu____3260 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3260
             in
          ((let uu___150_3265 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.ty = (uu___150_3265.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___150_3265.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___151_3275 = x  in
            let uu____3276 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___151_3275.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___151_3275.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3276
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___152_3283 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___152_3283.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___152_3283.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3288  ->
    match uu____3288 with
    | (p,wopt,e) ->
        let uu____3306 = close_pat p  in
        (match uu____3306 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3330 = subst closing w  in Some uu____3330
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    let uu____3346 =
      let uu____3351 =
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
      FStar_All.pipe_right uu____3351 FStar_List.unzip  in
    match uu____3346 with | (s,us') -> (s, us')
  
let open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
      let uu____3392 = univ_var_opening us  in
      match uu____3392 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____3417 = univ_var_opening us  in
      match uu____3417 with
      | (s,us') -> let uu____3430 = subst_comp s c  in (us', uu____3430)
  
let close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun us  ->
    fun t  ->
      let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
         in
      subst s t
  
let close_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun us  ->
    fun c  ->
      let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
         in
      subst_comp s c
  
let open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____3473 = FStar_Syntax_Syntax.is_top_level lbs  in
      if uu____3473
      then (lbs, t)
      else
        (let uu____3479 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3491  ->
                  match uu____3491 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____3510 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                        FStar_Syntax_Syntax.freshen_bv uu____3510  in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___153_3513 = lb  in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___153_3513.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___153_3513.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___153_3513.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___153_3513.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], [])
            in
         match uu____3479 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3531 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3543  ->
                                match uu____3543 with
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
                       match uu____3531 with
                       | (uu____3566,us,u_let_rec_opening) ->
                           let uu___154_3573 = lb  in
                           let uu____3574 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___154_3573.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___154_3573.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___154_3573.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3574
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
      let uu____3590 = FStar_Syntax_Syntax.is_top_level lbs  in
      if uu____3590
      then (lbs, t)
      else
        (let uu____3596 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3604  ->
                  match uu____3604 with
                  | (i,out) ->
                      let uu____3615 =
                        let uu____3617 =
                          let uu____3618 =
                            let uu____3621 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                               in
                            (uu____3621, i)  in
                          FStar_Syntax_Syntax.NM uu____3618  in
                        uu____3617 :: out  in
                      ((i + (Prims.parse_int "1")), uu____3615)) lbs
             ((Prims.parse_int "0"), [])
            in
         match uu____3596 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3636 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3644  ->
                                match uu____3644 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing)
                          in
                       match uu____3636 with
                       | (uu____3657,u_let_rec_closing) ->
                           let uu___155_3661 = lb  in
                           let uu____3662 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___155_3661.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___155_3661.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___155_3661.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___155_3661.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3662
                           }))
                in
             let t1 = subst let_rec_closing t  in (lbs1, t1))
  
let close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____3672  ->
      match uu____3672 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____3690  ->
                   match uu____3690 with
                   | (x,uu____3694) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____3705  ->
      match uu____3705 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____3723 = subst s t  in (us', uu____3723)
  
let opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____3738  ->
              match uu____3738 with
              | (x,uu____3742) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  